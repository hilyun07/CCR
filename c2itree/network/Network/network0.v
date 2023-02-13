Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Any.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import FMapList.
Require Import OrderedTypeEx.
Require Import error.
Require Import values.
Require Import ConvC2ITree.

Module Z_map := Make OrderedTypeEx.Z_as_OT.

From compcert Require Import
  AST Ctypes Values Integers Clight Maps Globalenvs Memdata Clightdefs.

Section MOD.

Section DEF.

Context (sk: Sk.t).
Let skenv: SkEnv.t := Cskel.load_skenv sk.


Definition node_id := Z.
Definition sock_fd := Z.
Definition ip := Z.

(** Values for the structure of [sockaddr_in] *)
Definition _sockaddr_in := 1%positive.
Definition _sin_family := 1%positive.
Definition _sin_port := 2%positive.
Definition _sin_addr := 3%positive.
Definition _sin_zero := 4%positive.

(** Environment with structure of [sockaddr_in] *)
Program Definition empty_genv_genv :=
    Genv.mkgenv (F := fundef) (V := type) [] PTree.Empty PTree.Empty
        (genv_next := xH) _ _ _.

Program Definition addr_genv_cenv: composite_env :=
    let members := [Member_bitfield _sin_family I16 Signed noattr 2 false;
        Member_bitfield _sin_port I16 Unsigned noattr 2 false;
        Member_bitfield _sin_addr I32 Unsigned noattr 4 false;
        Member_plain _sin_zero (Tlong Unsigned noattr)] in
    let al := alignof_composite PTree.Empty members in
    PTree.Nodes (PTree.Node010
    (Build_composite Struct members noattr
        (Coqlib.align (sizeof_composite PTree.Empty Struct members) al)
        al (rank_members PTree.Empty members) _ _ _)).

Next Obligation.
exists 3.
compute.
reflexivity.
Qed.

Next Obligation.
apply Coqlib.align_divides.
compute.
reflexivity.
Qed.

Definition ge: Clight.genv := {|genv_genv := empty_genv_genv; genv_cenv := addr_genv_cenv|}.

(** ** Socket types *)

(** Sockets *)
Record socket := {
    sock_port: option Z; (**r port the socket is bound to *)
    sock_queue: list sock_fd; (**r queue for connection *)
    sock_max_queue: Z (**r maximum queue length *)
}.
(** Incoming connections should be added at the end of the queue
and a maximum queue length of 0 indicates the socket is not listening. *)

(** Connected sockets *)
Record csocket := {
    csock_tgt: sock_fd; (**r its counterpart *)
    csock_msg: option (list (list memval)) (**r messages sent *)
}.
(** If `csock_msg` is set to `None`, it means the connection
is closed. *)

(** The socket environment *)
Definition sockets := Z_map.t (socket + csocket).

(** The global environment *)
Record environment := {
    socks: sockets;
    portm: Z_map.t sock_fd
}.

(** ** Auxiliary functions *)

(* Return a new file descriptor. *)
Definition new_fd (socks: sockets): Z :=
    (Z_map.fold
        (fun fd _ m => Z.max fd m)
        socks 0%Z) + 1.

(** Update a field in a Z_map. The difference with Z_map.add
is that it fails if the mapping does not exist. *)
Definition Z_map_update [elt] (x: Z_map.key)
        (e: elt) (m: Z_map.t elt): option (Z_map.t elt) :=
    option_map (fun _ => Z_map.add x e m) (Z_map.find x m).

(** Return the list of keys of a Z_map. *)
Definition Z_map_keys [elt] (m: Z_map.t elt): list Z :=
    Z_map.fold (fun x _ l => x :: l) m [].

(** Find an object in the reverse image by a Z_map *)
Definition Z_map_find_rev [elt] {eqb_elt: elt -> elt -> bool}
    (e: elt) (m: Z_map.t elt) :=
    Z_map.fold (fun x e' a => match a with
    | None => if eqb_elt e e' then Some x else None
    | Some _ => a end) m None.

(** Set the field sock_max_queue (a.k.a. backlog) of a socket. *)
Definition set_backlog fd backlog socks: option sockets :=
    match Z_map.find fd socks with
    | Some (inl sock) =>
        Some (Z_map.add fd (inl
            {|sock_port := sock.(sock_port);
            sock_queue := sock.(sock_queue);
            sock_max_queue := backlog|})
            socks)
    | _ => None
    end.

(** Set the field csock_msg of a connected socket. *)
Definition set_msg fd msgl socks: option sockets :=
    match Z_map.find fd socks with
    | Some (inr sock) =>
        let sock := {|csock_tgt := sock.(csock_tgt);
                    csock_msg := msgl|} in
        Some (Z_map.add fd (inr sock) socks)
    | _ => None
    end.

(** Close a connected socket. *)
Definition close_csock fd socks: option sockets :=
    set_msg fd None socks.

(** Return the messages received by a connected socket. *)
Definition get_msg fd (socks: sockets): option (list (list memval)) :=
    match Z_map.find fd socks with
    | Some (inr sock) => sock.(csock_msg)
    | _ => None
    end.

(** Return the socket a connected socket is connected to. *)
Definition get_tgt fd (socks: sockets): option sock_fd :=
    match Z_map.find fd socks with
    | Some (inr sock) => Some sock.(csock_tgt)
    | _ => None
    end.

(** Read the port from a [sockaddr_in]. *)
Definition read_port addr_b addr_ofs: itree Es Z :=
    `addr: composite <- ((Clight.genv_cenv ge) ! _sockaddr_in)?;;
    `port_field: positive <- (match co_members addr with
        | _ :: (Member_bitfield pf I16 Unsigned _ _ false) :: _ => Some pf
        | _ => None
        end)?;;
    `port_ptr: block * (ptrofs * bitfield) <- (match field_offset (Clight.genv_cenv ge)
            port_field (co_members addr) with
        | Errors.OK (delta, bf) =>
            Some (addr_b, (Ptrofs.add addr_ofs (Ptrofs.repr delta), bf))
        | _ => None
        end)?;;

    `port: val <- ccallU "load" (Mint16unsigned, (fst port_ptr), (fst (snd port_ptr)));;
    `port: Z <- (match port with Vint i => Some (Int.unsigned i) | _ => None end)?;;
    Ret port.

(* Choose a port in the unprivileged range (1024 to 65535) that is not in the [ports] list. *)
Definition choose_port ports: itree Es Z :=
    port <- trigger (Choose nat);;
    let port := Z.of_nat port in
    guarantee ((1024 <= port /\ port <= 65535)%Z /\ ~ In port ports);;;
    Ret port.

(** ** Module functions *)
(** *** Socket *)
(** Missing features:
- [domain] argument is ignored and supposed to be AF_INET,
- [type] argument is ignored and supposed to be SOCK_STREAM.
*)
Definition socketF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(domain, (type, protocol))
            <- (pargs [tint; tint; tint] varg)?;;

        let sock := Build_socket None [] 0%Z in
        let fd := new_fd env.(socks) in
        let socks := Z_map.add fd (inl sock) env.(socks) in

        let env := {|socks := socks; portm := env.(portm)|} in
        trigger (PPut env↑);;;

        Ret (Vint (Int.repr fd)).

(** *** Bind *)
(** Missing features:
- The [addrlen] argument is ignored,
- Only the port is read from [addr],
- No error when the socket is already bound,
*)
Definition bindF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [tint; Tpointer (Tstruct _sockaddr_in noattr) noattr; tint] varg)?;;

        `port: Z <- read_port addr_b addr_ofs;;

        (* Choose port in case provided one is 0 *)
        `port': Z <- choose_port (Z_map_keys env.(portm));;
        let port := if (port =? 0)%Z then port' else port in

        (* Check port availability *)
        if in_dec Z.eq_dec port (Z_map_keys env.(portm)) then
            set_errno sk EADDRINUSE (Vint Int.mone)
        else

        let sock := Build_socket (Some port) [] 0%Z in

        socks <- (Z_map_update fd (inl sock) env.(socks))?;;

        let portm := Z_map.add port fd env.(portm) in

        let env := {|socks := socks; portm := portm|} in
        trigger (PPut env↑);;;

        Ret (Vint Int.zero).

(** *** Listen *)
Definition listenF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, backlog) <- (pargs [tint; tint] varg)?;;

        socks <- (set_backlog fd backlog env.(socks))?;;

        let env := {|socks := socks; portm := env.(portm)|} in
        trigger (PPut env↑);;;

        Ret (Vint Int.zero).

(** *** Accept *)
(** Missing features:
- No address is written at the provided pointer.
*)
Definition acceptF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, (addr, addrlen))
            <- (pargs [tint; Tpointer (Tstruct xH noattr) noattr; Tpointer tuint noattr] varg)?;;

        match Z_map.find fd env.(socks) with
        | Some (inl sock) =>
        match sock.(sock_queue) with
        | [] => (**r No incoming connection *)
            `_: unit <- ccallU "yield" ([]:list val);;
            ccallU "accept" varg
        | client_fd :: tl =>
            (* Remove client from queue *)
            let sock := {|sock_port := sock.(sock_port);
                        sock_queue := tl;
                        sock_max_queue := sock.(sock_max_queue)|}
            in
            let socks := Z_map.add fd (inl sock) env.(socks) in

            (* Find client *)
            client <- (Z_map.find client_fd socks)?;;

            (* Create new file descriptor on server side *)
            let server_fd := new_fd socks in

            (* Create both connected sockets *)
            let socks := Z_map.add client_fd (inr {|
                csock_tgt := server_fd;
                csock_msg := Some []
                |}) socks in
            let socks := Z_map.add server_fd (inr {|
                csock_tgt := client_fd;
                csock_msg := Some []
                |}) socks in

            client_port <- (Z_map_find_rev (eqb_elt := Z.eq_dec)
                client_fd env.(portm))?;;
            let portm := Z_map.remove client_port env.(portm) in

            let env := {|socks := socks; portm := portm|} in
            trigger (PPut env↑);;;

            Ret (Vint (Int.repr server_fd))
        end
        | _ => triggerUB (**r The fd isn't a connected socket *)
        end.

(** *** Connect *)
Definition connectF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [tint; Tpointer (Tstruct xH noattr) noattr; tuint] varg)?;;

        `server_port: Z <- read_port addr_b addr_ofs;;

        match Z_map.find server_port env.(portm) with
        | None => (**r No server bound to this address *)
            `_: unit <- ccallU "yield" ([]:list val);;
            ccallU "connect" varg
        | Some server_fd =>
        match Z_map.find server_fd env.(socks) with
        | Some (inl serv) =>
            if Z.of_nat (List.length serv.(sock_queue)) >=? serv.(sock_max_queue) then (**r Queue full *)
                `_: unit <- ccallU "yield" ([]:list val);;
                ccallU "connect" varg
            else
                (* Add socket to queue *)
                let socks := Z_map.add server_fd (inl {|
                    sock_port := serv.(sock_port);
                    sock_queue := serv.(sock_queue) ++ [fd];
                    sock_max_queue := serv.(sock_max_queue)
                |}) env.(socks) in

                (* Pick new port for client *)
                client_port <- choose_port (Z_map_keys env.(portm));;

                let client := Build_socket (Some client_port) [] 0%Z in
                socks <- (Z_map_update fd (inl client) socks)?;;
                let portm := Z_map.add client_port fd env.(portm) in

                let env := {|socks := socks; portm := portm|} in
                trigger (PPut env↑);;;

                Ret (Vint Int.zero)
        | _ => triggerUB
        end end.

(** *** Close *)
Definition closeF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        fd <- (pargs [tint] varg)?;;

        (* Yield to give some time to recover messages *)
        `_: unit <- ccallU "yield" ([]:list val);;

        match Z_map.find fd env.(socks) with
        | None => triggerUB
        | Some (inl _) => (* not connected *)
            let socks := Z_map.remove fd env.(socks) in
            let env := {|socks := socks; portm := env.(portm)|} in
            trigger (PPut env↑);;;

            Ret (Vint Int.zero)
        | Some (inr _) => (* connected *)
            socks <- (close_csock fd env.(socks))?;;
            tgt <- (get_tgt fd socks)?;;
            socks <- (close_csock tgt socks)?;;

            let env := {|socks := socks; portm := env.(portm)|} in
            trigger (PPut env↑);;;

            Ret (Vint Int.zero)
        end.

(** *** Send *)
Definition sendF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, ((buf_b, buf_ofs), (len, flags)))
              <- (pargs [tint; Tpointer Tvoid noattr; tulong; tint] varg)?;;

        (* added by Jaehyung Lee : they also have to send null char *)
        let len := (len + 1)%Z in

        if len >? 65536 then (**r Message too long *)
            Ret (Vlong Int64.mone)
        else
            `msg: list memval <- (ccallU "loadbytes" (buf_b, buf_ofs, len));;

            (* Add message to the message list *)
            tgt_fd <- (get_tgt fd env.(socks))?;;
            msgl <- (get_msg tgt_fd env.(socks))?;;
            socks <- (set_msg tgt_fd (Some (msg :: msgl)) env.(socks))?;;

            let env := {|socks := socks; portm := env.(portm)|} in
            trigger (PPut env↑);;;

            Ret (Vlong (Int64.repr len)).

(** *** Recv *)
Definition recvF: list val -> itree Es val :=
    fun varg =>
        env <- trigger (PGet);;
        `env: environment <- env↓?;;

        '(fd, ((buf_b, buf_ofs), (len, flags)))
            <- (pargs [tint; Tpointer Tvoid noattr; tulong; tint] varg)?;;

        match get_msg fd env.(socks) with
        | None => Ret (Vlong Int64.zero) (**r Connection closed *)

        | Some msgl =>
        i_msg <- trigger (Choose nat);;
        match i_msg with
        | 0 => (**r No message received *)
            `_: unit <- ccallU "yield" ([]:list val);;
            ccallU "recv" varg
        | S i_msg =>
            guarantee (i_msg < (List.length msgl));;;
            msg <- (List.nth_error msgl i_msg)?;;
            `_: unit <- ccallU "storebytes" (buf_b, buf_ofs, msg);;
            Ret (Vlong (Int64.repr (Z.of_nat (List.length msg))))
        end
        end.

Definition htonsF: list val -> itree Es val :=
    fun varg =>
      `i: Z <- (pargs [tushort] varg)?;;

        let i := if Archi.big_endian then i
            else switch_endianness 1 i in
        Ret (Vint (Int.repr i)).

Definition ntohsF := htonsF.

Definition htonlF: list val -> itree Es val :=
    fun varg =>
        `i: Z <- (pargs [tuint] varg)?;;

        let i := if Archi.big_endian then i
            else switch_endianness 2 i in
        Ret (Vint (Int.repr i)).

Definition ntohlF := htonlF.

(* Placeholder for the inet_addr function *)
Definition inet_addrF: list val -> itree Es val :=
    fun _ => Ret (Vint Int.zero).

Definition NetSem: ModSem.t :=
  {|
    ModSem.fnsems := [("socket", cfunU socketF); ("bind", cfunU bindF);
                      ("listen", cfunU listenF); ("accept", cfunU acceptF);
                      ("connect", cfunU connectF); ("close", cfunU closeF);
                      ("send", cfunU sendF); ("recv", cfunU recvF);
                      ("htons", cfunU htonsF); ("ntohs", cfunU ntohsF);
                      ("htonl", cfunU htonlF); ("ntohl", cfunU ntohlF);
                      ("inet_addr", cfunU inet_addrF)];
    ModSem.mn := "Net";
    ModSem.initial_st := (ge, Z_map.empty (socket + csocket), Z_map.empty sock_fd)↑
  |}.

End DEF.

Definition Net: Mod.t :=
  {|
    Mod.get_modsem := NetSem;
    Mod.sk := Sk.unit;
  |}.

End MOD.

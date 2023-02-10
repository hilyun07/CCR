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

Context (skenv: SkEnv.t).

Definition node_id := Z.
Definition sock_fd := Z.
Definition ip := Z.

(** Values for the structure of [sockaddr_in] *)
Definition _sockaddr_in := 1%positive.
Definition _sin_family := 1%positive.
Definition _sin_port := 2%positive.
Definition _sin_addr := 3%positive.
Definition _sin_zero := 4%positive.

(** Sockets *)
Record socket := {
    sock_port: option Z; (**r port the socket is bound to *)
    sock_queue: list sock_fd; (**r queue for connection *)
    sock_max_queue: Z (**r maximum queue length *)
}.
(** Incoming connections should be added at the end of the queue
and a maximum queue length of 0 indicates the socket is not listening *)

(** Connected sockets *)
Record csocket := {
    csock_tgt: sock_fd; (**r its counterpart *)
    csock_msg: option (list (list memval)) (**r messages sent *)
}.
(** If `csock_msg` is set to `None`, it means the connection
is closed. *)

(** The socket environment *)
Definition sockets := Z_map.t (socket + csocket).

(* Returns a new file descriptor *)
Definition new_fd (socks: sockets): Z :=
    (Z_map.fold
        (fun fd _ m => Z.max fd m)
        socks 0%Z) + 1.

Definition Z_map_update [elt] (x: Z_map.key)
        (e: elt) (m: Z_map.t elt): option (Z_map.t elt) :=
    option_map (fun _ => Z_map.add x e m) (Z_map.find x m).

Definition Z_map_keys [elt] (m: Z_map.t elt): list Z :=
    Z_map.fold (fun x _ l => x :: l) m [].

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

Definition set_msg socks fd msgl: option sockets :=
    match Z_map.find fd socks with
    | Some (inr sock) =>
        let sock := {|csock_tgt := sock.(csock_tgt);
                    csock_msg := msgl|} in
        Some (Z_map.add fd (inr sock) socks)
    | _ => None
    end.

Definition close_csock socks fd: option sockets :=
    set_msg socks fd None.

Definition get_msg (socks: sockets) fd: option (list (list memval)) :=
    match Z_map.find fd socks with
    | Some (inr sock) => sock.(csock_msg)
    | _ => None
    end.

Definition get_tgt (socks: sockets) fd: option sock_fd :=
    match Z_map.find fd socks with
    | Some (inr sock) => Some sock.(csock_tgt)
    | _ => None
    end.

Definition read_port ge addr_b addr_ofs: itree Es Z :=
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
      _ <- trigger (Syscall "print_string" ["aware"]↑ top1);;
      _ <- trigger (Syscall "print_num" [port]↑ top1);;
      Ret port.

Definition choose_port ports: itree Es Z :=
    let av_ports: Type := {p: Z | (49152 <= p /\ p <= 65535)%Z /\ ~ In p ports} in
    port <- trigger (Choose av_ports);;
    Ret (match port with exist _ port _ => port end).

Definition socketF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(domain, (type, protocol))
            <- (pargs [Tint I32 Signed noattr;
                      Tint I32 Signed noattr;
                      Tint I32 Signed noattr] varg)?;;
        (* Arguments are ignored for now *)

        let sock := Build_socket None [] 0%Z in
        let fd := new_fd socks in
        let socks := Z_map.add fd (inl sock) socks in

        trigger (PPut (ge, socks, ports)↑);;;

        Ret (Vint (Int.repr fd)).

Definition bindF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in


        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [tint; Tpointer (Tstruct _sockaddr_in noattr) noattr; tint] varg)?;;

        `port: Z <- read_port ge addr_b addr_ofs;;

        (* Choose port in case provided one is 0 *)
        `port': Z <- choose_port (Z_map_keys ports);;
        let port := if (port =? 0)%Z then port' else port in
      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;

        (* Check port availability *)
        if in_dec Z.eq_dec port (Z_map_keys ports) then
            set_errno (skenv := skenv) EADDRINUSE (Vint Int.mone)
        else

        let sock := Build_socket (Some port) [] 0%Z in

        socks <- (Z_map_update sockfd (inl sock) socks)?;;

        trigger (PPut (ge, socks, Z_map.add port sockfd ports)↑);;;
        Ret (Vint Int.zero).

Definition listenF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, backlog) <- (pargs [Tint I32 Signed noattr;
                                    Tint I32 Signed noattr] varg)?;;

      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;
        socks <- (set_backlog sockfd backlog socks)?;;

        trigger (PPut (ge, socks, ports)↑);;;
        Ret (Vint Int.zero).

Definition acceptF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, (addr, addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tpointer (Tint I32 Unsigned noattr) noattr] varg)?;;
      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;

        match Z_map.find sockfd socks with
        | Some (inl sock) =>
        match sock.(sock_queue) with
        | [] =>
            `_: unit <- ccallU "yield" ([]:list val);;
                ccallU "accept" varg
        | clientfd :: tl =>
            (* Remove client from queue *)
            let sock := {|sock_port := sock.(sock_port);
                        sock_queue := tl;
                        sock_max_queue := sock.(sock_max_queue)|}
            in
            let socks := Z_map.add sockfd (inl sock) socks in

            (* Find client *)
      _ <- trigger (Syscall "print_string" ["clientfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [clientfd]↑ top1);;
            client <- (Z_map.find clientfd socks)?;;

            (* Create new file descriptor on server side *)
            let servfd := new_fd socks in

            (* Create both connected sockets *)
            let socks := Z_map.add clientfd (inr {|
                csock_tgt := servfd;
                csock_msg := Some []
                |}) socks in
            let socks := Z_map.add servfd (inr {|
                csock_tgt := clientfd;
                csock_msg := Some []
                |}) socks in
        msgl <- (get_msg socks clientfd)?;;
            
            (*write_addr (fst addr) (snd addr) (get_addr socks (fst src) (snd src));;;
            Need to set addrlen *)

            trigger (PPut (ge, socks, ports)↑);;;
            Ret (Vint (Int.repr servfd))
        end
        | _ =>
            triggerUB
        end.

Definition connectF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tint I32 Unsigned noattr] varg)?;;

      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;
        `serv_port: Z <- read_port ge addr_b addr_ofs;;

        match Z_map.find serv_port ports with
        | None =>
        `_: unit <- ccallU "yield" ([]:list val);;
        ccallU "connect" varg
        | Some servfd =>
      _ <- trigger (Syscall "print_string" ["servfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [servfd]↑ top1);;
        match Z_map.find servfd socks with
        | Some (inl serv) =>
        if Z.of_nat (List.length serv.(sock_queue)) >=? serv.(sock_max_queue) then
            `_: unit <- ccallU "yield" ([]:list val);;
            ccallU "connect" varg
        else
            let socks := Z_map.add servfd (inl {|
                sock_port := serv.(sock_port);
                sock_queue := serv.(sock_queue) ++ [sockfd];
                sock_max_queue := serv.(sock_max_queue)
            |}) socks in

            (* Picking new port for client *)
            client_port <- choose_port (Z_map_keys ports);;

            let client := Build_socket (Some client_port) [] 0%Z in
            socks <- (Z_map_update sockfd (inl client) socks)?;;

            trigger (PPut (ge, socks, Z_map.add client_port sockfd ports)↑);;;
            Ret (Vint Int.zero)
        | _ => triggerUB
        end end.

Definition closeF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        fd <- (pargs [Tint I32 Signed noattr] varg)?;;
               (* diff *)
               match close_csock socks fd with
               | Some socks =>
        trigger (PPut (ge, socks, ports)↑);;;
          Ret (Vint Int.zero)
               | None => Ret (Vint Int.zero)
                            end.
                   
        (* socks <- (close_csock socks fd)?;; *)

        (* trigger (PPut (ge, socks, ports)↑);;; *)
        (* Ret (Vint Int.zero). *)

Definition sendF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((buf_b, buf_ofs), (len, flags)))
            <- (pargs [Tint I32 Signed noattr;
                      Tpointer Tvoid noattr;
                      Tlong Unsigned noattr;
                      Tint I32 Signed noattr] varg)?;;
      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
        _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;
        let len := (len + 1)%Z in

        if len >? 65536 then
            Ret (Vlong Int64.mone)
        else
          `msg: list memval <- (ccallU "loadbytes" (buf_b, buf_ofs, len));; 

            msgl <- (get_msg socks sockfd)?;;
            socks <- (set_msg socks sockfd (Some (msg :: msgl)))?;;
                      (* diff *)
            tgt_fd <- (get_tgt socks sockfd)?;;
            socks <- (set_msg socks tgt_fd (Some (msg :: msgl)))?;;

            trigger (PPut (ge, socks, ports)↑);;;
            Ret (Vlong (Int64.repr len)).

Definition recvF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * Z_map.t sock_fd <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((buf_b, buf_ofs), (len, flags)))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer Tvoid noattr;
                        Tlong Unsigned noattr;
                        Tint I32 Signed noattr] varg)?;;
                (* severe diff *)
      _ <- trigger (Syscall "print_string" ["socketfd"]↑ top1);;
      _ <- trigger (Syscall "print_num" [sockfd]↑ top1);;

_ <- (        match get_tgt socks sockfd with
             | Some _ => trigger (Syscall "print_string" ["asdf"]↑ top1)
             | None => trigger (Syscall "print_string" ["sadf"]↑ top1)
             end
    );;
_ <- (        match get_msg socks sockfd with
             | Some _ => trigger (Syscall "print_string" ["ttt"]↑ top1)
             | None => trigger (Syscall "print_string" ["ddd"]↑ top1)
             end
    );;
        msgl <- (get_msg socks sockfd)?;;
      _ <- trigger (Syscall "print_string" ["sossketfd"]↑ top1);;

        (* diff *)
        i_msg <- trigger (Choose (option {n: nat | n < (List.length msgl)}));;
        match i_msg with
        | None => Ret (Vlong Int64.mone)
        | Some (exist _ i_msg _) =>
            msg <- (List.nth_error msgl i_msg)?;;
            `_ : () <- ccallU "storebytes" (buf_b, buf_ofs, msg);;
            Ret (Vlong (Int64.repr (Z.of_nat (List.length msg))))
        end.

Definition htonsF: list val -> itree Es val :=
    fun varg =>
        `i: Z <- (pargs [Tint I16 Unsigned noattr] varg)?;;

        let i := if Archi.big_endian then i
            else switch_endianness 1 i in
      _ <- trigger (Syscall "print_string" ["aware"]↑ top1);;
      _ <- trigger (Syscall "print_num" [i]↑ top1);;
        Ret (Vint (Int.repr i)).

Definition ntohsF := htonsF.

Definition htonlF: list val -> itree Es val :=
    fun varg =>
        `i: Z <- (pargs [Tint I32 Unsigned noattr] varg)?;;

        let i := if Archi.big_endian then i
            else switch_endianness 2 i in
        Ret (Vint (Int.repr i)).

Definition ntohlF := htonlF.

(* Placeholder for the inet_addr function *)
Definition inet_addrF: list val -> itree Es val :=
    fun _ => Ret (Vint Int.zero).

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
    Mod.get_modsem := fun sk => NetSem (load_skenv sk);
    Mod.sk := cskel.(Sk.unit)
  |}.

End MOD.

Section TEST.

  Definition errval : Errcode -> val := fun _ => Vint Int.zero.

  Definition skenv : SkEnv.t :=
    {|
      SkEnv.blk2id := fun blk =>
                        if Pos.eqb blk 127
                        then Some "errno" else None;
      SkEnv.id2blk := fun id =>
                        if id =? "errno"
                        then Some 127%positive else None
    |}.

End TEST.

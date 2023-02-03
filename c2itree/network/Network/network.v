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
  Ctypes Values Integers Clight Maps Globalenvs Clightdefs.

Section MOD.

Section DEF.

Context (skenv: SkEnv.t).

(* Should be removed, solves problem with implicit arguments *)

Notation "x <- t1 ?*;; t2" := (unwrapUErr (skenv := skenv) t1 (fun x => t2) (fun v => set_errno (skenv := skenv) EWOULDBLOCK v))
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*;; t2" := (unwrapUErr (skenv := skenv) t1 (fun _ => t2) (fun v => set_errno (skenv := skenv) EWOULDBLOCK v))
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*;; t2" :=
    (unwrapUErr (skenv := skenv) t1 (fun x_ => match x_ with p => t2 end) (fun v => set_errno (skenv := skenv) EWOULDBLOCK v))
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
Notation "x <- t1 ?*[ g ];; t2" := (unwrapUErr (skenv := skenv) t1 (fun x => t2) g)
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*[ g ];; t2" := (unwrapUErr (skenv := skenv) t1 (fun _ => t2) g)
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*[ g ];; t2" :=
    (unwrapUErr (skenv := skenv) t1 (fun x_ => match x_ with p => t2 end) g)
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.

Definition node_id := Z.
Definition sock_fd := Z.
Definition ip := Z.
Definition _sockaddr_in := 1%positive.
Definition _sin_family := 1%positive.
Definition _sin_port := 2%positive.
Definition _sin_addr := 3%positive.
Definition _sin_zero := 4%positive.

Definition get_pid: itree Es node_id :=
    `pid:val <- ccallU "getpid" ([]:list val);;
    pid <- (parg tint pid)?;;
    Ret pid.

Record socket := {
    sock_port: option Z;
    sock_queue: list (node_id * sock_fd);
    sock_max_queue: Z
}.

Record csocket := {
    csock_tgt: node_id * sock_fd;
    csock_msg: option (list (list val))
}.

Record node_sockets := {
    socks_sockmap: Z_map.t socket;
    socks_csockmap: Z_map.t csocket;
    socks_av_fd: Z
}.

Definition sockets := Z_map.t node_sockets.

Definition Z_map_find {A: Type} fd node_socks: opt_err A :=
    match Z_map.find fd node_socks with
    | None => ErrKo EBADF (Vint Int.mone)
    | Some x => ErrOk x
    end.

Definition find_node_sockets_safe socks sock_pid: sockets * node_sockets :=
    match Z_map.find sock_pid socks with
    | None => let node_socks := (* No sockets yet on this thread *)
        Build_node_sockets (Z_map.empty socket)
                (Z_map.empty csocket) 0%Z in
            (Z_map.add sock_pid node_socks socks, node_socks)
    | Some node_socks => (socks, node_socks)
    end.

Definition update_socket socks sock_pid fd sock: opt_err sockets :=
    opt_err_map (fun node_socks =>
        let node_socks := Build_node_sockets
            (Z_map.add fd sock node_socks.(socks_sockmap))
            node_socks.(socks_csockmap)
            node_socks.(socks_av_fd) in
        Z_map.add sock_pid node_socks socks)
    (opt_to_opt_err (Z_map.find sock_pid socks)).

Definition add_socket socks sock_pid sock: sockets * sock_fd :=
    let (socks, node_socks) := find_node_sockets_safe socks sock_pid in
    let fd := node_socks.(socks_av_fd) in
    let node_socks := Build_node_sockets
        (Z_map.add fd sock node_socks.(socks_sockmap))
        node_socks.(socks_csockmap)
        (node_socks.(socks_av_fd) + 1) in
    (Z_map.add sock_pid node_socks socks, fd).

Definition update_csocket socks sock_pid fd csock: opt_err sockets :=
    opt_err_map (fun node_socks =>
        let node_socks := Build_node_sockets
            node_socks.(socks_sockmap)
            (Z_map.add fd csock node_socks.(socks_csockmap))
            node_socks.(socks_av_fd) in
        Z_map.add sock_pid node_socks socks)
    (opt_to_opt_err (Z_map.find sock_pid socks)).

Definition add_csocket socks sock_pid csock: sockets * sock_fd :=
    let (socks, node_socks) := find_node_sockets_safe socks sock_pid in
    let fd := node_socks.(socks_av_fd) in
    let node_socks := Build_node_sockets
        node_socks.(socks_sockmap)
        (Z_map.add fd csock node_socks.(socks_csockmap))
        (node_socks.(socks_av_fd) + 1) in
    (Z_map.add sock_pid node_socks socks, fd).

Definition set_backlog socks sock_pid fd backlog: opt_err sockets :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        match Z_map.find fd node_socks.(socks_sockmap) with
        | None => ErrKo EBADF (Vint Int.mone)
        | Some sock =>
            let sock := Build_socket sock.(sock_port)
                sock.(sock_queue) backlog in
            update_socket socks sock_pid fd sock
        end
    end.

Definition push_connection socks id_tgt fd_tgt id_src fd_src : opt_err sockets :=
    match Z_map.find id_tgt socks with
    | None => ErrUB
    | Some node_socks =>
        match Z_map.find fd_tgt node_socks.(socks_sockmap) with
        | None => ErrKo EBADF (Vint Int.mone)
        | Some sock =>
            if (Z.of_nat (List.length sock.(sock_queue))
                =? sock.(sock_max_queue))%Z
            then ErrKo ETIMEDOUT (Vint Int.mone)
            else let sock := Build_socket sock.(sock_port)
                (sock.(sock_queue) ++ [(id_src, fd_src)]) sock.(sock_max_queue) in
            update_socket socks id_tgt fd_tgt sock
        end
    end.

Definition pop_connection socks sock_pid fd: opt_err (sockets * (node_id * sock_fd)) :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        match Z_map.find fd node_socks.(socks_sockmap) with
        | None => ErrKo EBADF (Vint Int.mone)
        | Some sock =>
            match sock.(sock_queue) with
            | [] => ErrKo EWOULDBLOCK (Vint Int.mone)
            | src :: queue =>
                let sock := Build_socket sock.(sock_port) queue
                    sock.(sock_max_queue) in
                opt_err_map (fun socks => (socks, src))
                    (update_socket socks sock_pid fd sock)
            end
        end
    end.

Definition sock_connect socks sock_pid fd tgt: opt_err sockets :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        opt_err_map (fun sock =>
            let csock := Build_csocket tgt (Some []) in
            let node_socks := Build_node_sockets
                (Z_map.remove fd node_socks.(socks_sockmap))
                (Z_map.add fd csock node_socks.(socks_csockmap))
                node_socks.(socks_av_fd) in
            Z_map.add sock_pid node_socks socks)
        (Z_map_find fd node_socks.(socks_sockmap))
    end.

Definition set_msg socks sock_pid fd msgl: opt_err sockets :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        opt_err_map (fun csock =>
            let csock := Build_csocket csock.(csock_tgt) msgl in
            let node_socks := Build_node_sockets
                node_socks.(socks_sockmap)
                (Z_map.add fd csock node_socks.(socks_csockmap))
                node_socks.(socks_av_fd) in
            Z_map.add sock_pid node_socks socks)
        (Z_map_find fd node_socks.(socks_csockmap))
    end.

Definition close_csock socks sock_pid fd: opt_err sockets :=
    set_msg socks sock_pid fd None.

Definition get_msg socks sock_pid fd: opt_err (list (list val)) :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        match Z_map_find fd node_socks.(socks_csockmap) with
        | ErrUB => ErrUB
        | ErrKo c v => ErrKo c v
        | ErrOk csock => match csock.(csock_msg) with
            | None => ErrKo DEF (Vint Int.zero)
            | Some msgl => ErrOk msgl
            end
        end
    end.

Definition get_tgt socks sock_pid fd: opt_err (node_id * sock_fd) :=
    match Z_map.find sock_pid socks with
    | None => ErrUB
    | Some node_socks =>
        opt_err_map (fun csock => csock.(csock_tgt))
        (Z_map_find fd node_socks.(socks_csockmap))
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

    `port: Int16.int <- Read_short (fst port_ptr) (fst (snd port_ptr));;
    Ret (Int16.unsigned port).

Definition find_port_socket_node sockmap port: opt_err sock_fd :=
    Z_map.fold
        (fun fd sock (x: opt_err sock_fd) => match x with
        | ErrKo c v => match sock.(sock_port) with
            | None => ErrKo c v
            | Some port' => if (port =? port')%Z then ErrOk fd
                else ErrKo c v
            end
        | ErrOk fd => ErrOk fd
        | ErrUB => ErrUB
        end)
        sockmap (ErrKo ECONNREFUSED (Vint Int.mone)).

Definition find_port_socket socks port: opt_err (node_id * sock_fd) :=
    Z_map.fold
       (fun sock_pid node_socks (x: opt_err (node_id * sock_fd))
        => match x with
        | ErrKo c v => opt_err_map (fun fd => (sock_pid, fd))
            (find_port_socket_node node_socks.(socks_sockmap) port)
        | ErrOk id_fd => ErrOk id_fd
        | ErrUB => ErrUB end)
        socks (ErrKo ECONNREFUSED (Vint Int.mone)).

Definition socketF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(domain, (type, protocol))
            <- (pargs [Tint I32 Signed noattr;
                      Tint I32 Signed noattr;
                      Tint I32 Signed noattr] varg)?;;
        (* Arguments are ignored for now *)

        let sock := Build_socket None [] 0%Z in
        `pid: node_id <- get_pid;;
        let (socks, fd) := add_socket socks pid sock in

        trigger (PPut (ge, socks, ports)↑);;;

        Ret (Vint (Int.repr fd)).

Definition bindF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;
        let '(ge, socks, ports) := ge_socks_ports in
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;


        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [tint; tptr (Tstruct _sockaddr_in noattr); tuint] varg)?;;
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;

        `port: Z <- read_port ge addr_b addr_ofs;;
        let sock := Build_socket (Some port) [] 0%Z in
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;

        `pid: node_id <- get_pid;;
        socks <- (update_socket socks pid sockfd sock)?*;;
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;

        trigger (PPut (ge, socks, (port :: ports))↑);;;
      _ <- trigger (Syscall "print_string" ["hello"]↑ top1);;
        Ret (Vint Int.zero).

Definition listenF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, backlog) <- (pargs [Tint I32 Signed noattr;
                                    Tint I32 Signed noattr] varg)?;;

        `pid: node_id <- get_pid;;
        socks <- (set_backlog socks pid sockfd backlog)?*;;

        trigger (PPut (ge, socks, ports)↑);;;
        Ret (Vint Int.zero).

Definition acceptF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, (addr, addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tpointer (Tint I32 Unsigned noattr) noattr] varg)?;;

        `pid: node_id <- get_pid;;
        '(socks, src) <- (pop_connection socks pid sockfd)?*[
            fun _ =>
            `r: val <- ccallU "accept" varg;;
            Ret r
        ];;

        socks <- (sock_connect socks (fst src) (snd src) (pid, sockfd))?*;;

        let ctgt := Build_csocket src (Some []) in
        let (socks, fd_ctgt) := add_csocket socks pid ctgt in

        (*write_addr (fst addr) (snd addr) (get_addr socks (fst src) (snd src));;;
        Need to set addrlen *)

        trigger (PPut (ge, socks, ports)↑);;;
        Ret (Vint (Int.repr fd_ctgt)).

Definition connectF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tint I32 Unsigned noattr] varg)?;;

        `port_tgt: Z <- read_port ge addr_b addr_ofs;;

        tgt <- (find_port_socket socks port_tgt)?*[
            fun _ =>
            `r: val <- (ccallU "connect" varg);;
            Ret r
        ];;

        `pid: node_id <- get_pid;;
        socks <- (push_connection socks (fst tgt) (snd tgt) pid sockfd)?*[
            fun _ =>
            `r: val <- (ccallU "connect" varg);;
            Ret r
        ];;

        (* Picking new port for source *)
        let av_ports: Type := {p: Z | (49152 <= p /\ p <= 65535)%Z /\ ~ In p ports} in
        port_src <- trigger (Choose av_ports);;
        let port_src := match port_src with exist _ port _ => port end in

        let src := Build_socket (Some port_src) [] 0%Z in

        `pid: node_id <- get_pid;;
        socks <- (update_socket socks pid sockfd src)?*;;

        trigger (PPut (ge, socks, (port_src :: ports))↑);;;
        Ret (Vint Int.zero).

Definition closeF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        fd <- (pargs [Tint I32 Signed noattr] varg)?;;

        `pid: node_id <- get_pid;;
        socks <- (close_csock socks pid fd)?*;;
        tgt <- (get_tgt socks pid fd)?*;;
        socks <- (close_csock socks (fst tgt) (snd tgt))?*;;

        trigger (PPut (ge, socks, ports)↑);;;
        Ret (Vint Int.zero).

Definition read_message buf msg_len: itree Es () :=
    ITree.iter (fun '(i, msg) =>
        if (i <? msg_len)%Z then
            let ptr := (Val.add buf (Vint (Int.repr (i * 8)%Z))) in
            `v: val <- (ccallU "load" [ptr]);;
            Ret (inl (i + 1, msg ++ [v])%Z)
        else
            trigger (PPut msg↑);;;
            Ret (inr tt)
        ) (0%Z, []).

Definition sendF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((buf_b, buf_ofs), (len, flags)))
            <- (pargs [Tint I32 Signed noattr;
                      Tpointer Tvoid noattr;
                      Tlong Unsigned noattr;
                      Tint I32 Signed noattr] varg)?;;

        let buf := Vptr buf_b buf_ofs in

        if len >? 8 (* What should the max be? *) then
            Ret (Vlong Int64.mone)
        else
            read_message buf len;;;
            msg <- trigger PGet;;
            `msg: list val <- msg↓?;;

            `pid: node_id <- get_pid;;
            msgl <- (get_msg socks pid sockfd)?*;;
            socks <- (set_msg socks pid sockfd (Some (msg :: msgl)))?*;;

            trigger (PPut (ge, socks, ports)↑);;;
            Ret (Vlong (Int64.repr len)).

Definition write_message buf buf_len msg: itree Es val :=
    ITree.iter (fun '(i, msg) =>
        match msg with
        | [] => Ret (inr (Vlong (Int64.repr i)))
        | v :: msg =>
            if (i <? buf_len)%Z then
                let ptr := (Val.add buf (Vint (Int.repr (i * 8)%Z))) in
                `_: val <- (ccallU "store" [ptr; v]);;
                Ret (inl (i + 1, msg))%Z
            else
                Ret (inr (Vlong (Int64.repr i)))
        end)
        (0%Z, msg).

Definition recvF: list val -> itree Es val :=
    fun varg =>
        ge_socks_ports <- trigger (PGet);;
        `ge_socks_ports: Clight.genv * sockets * list Z <- ge_socks_ports↓?;;
        let '(ge, socks, ports) := ge_socks_ports in

        '(sockfd, ((buf_b, buf_ofs), (len, flags)))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer Tvoid noattr;
                        Tlong Unsigned noattr;
                        Tint I32 Signed noattr] varg)?;;

        let buf := Vptr buf_b buf_ofs in
        `pid: node_id <- get_pid;;
        msgl <- (get_msg socks pid sockfd)?*;;

        i_msg <- trigger (Choose (option {n: nat | n < (List.length msgl)}));;
        match i_msg with
        | None => Ret (Vlong Int64.mone)
        | Some (exist _ i_msg _) =>
            msg <- (List.nth_error msgl i_msg)?;;
            write_message buf len msg
        end.

Definition htonsF: list val -> itree Es val :=
    fun varg =>
        `i: Z <- (pargs [Tint I16 Unsigned noattr] varg)?;;

        let i := if Archi.big_endian then i
            else switch_endianness 1 i in
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


Definition site_append_morph (sn: string) : Es ~> Es.
  Proof.
    intros. destruct X.
    { destruct c. destruct ((fn =? "store") || (fn =? "load")).
      exact (inl1 (Call (sn ++ "." ++ fn) args)).
      exact (inl1 (Call fn args)). } (* if memory call *)
    destruct s.
    { destruct s.
      exact (inr1 (inl1 (EventsL.Spawn fn args))).
      exact (inr1 (inl1 EventsL.Yield)).
      exact (inr1 (inl1 EventsL.Getpid)). }
    destruct s.
    { destruct p.
      exact (inr1 (inr1 (inl1 (PPut p)))).
      exact (inr1 (inr1 (inl1 (PGet )))). }
    { destruct e.
      exact (inr1 (inr1 (inr1 (Choose X)))).
      exact (inr1 (inr1 (inr1 (Take X)))).
      exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). }
  Defined.
    

  Definition site_appended_itree sn : itree Es ~> itree Es := translate (site_append_morph sn).

  Definition site_cfunU {X Y : Type} (body : X -> itree Es Y) :=
    fun '(optsmn, varg) =>
      smn <- (optsmn)?;;
      idx <- (index 0 "." smn)?;;
      ` varg0 : X <- (Any.downcast varg)?;;
      ` vret : Y <- site_appended_itree (substring 0 idx smn) Y (body varg0);; Ret (Any.upcast vret).

Definition NetSem: ModSem.t :=
  {|
    ModSem.fnsems := [("socket", site_cfunU socketF); ("bind", site_cfunU bindF);
                      ("listen", site_cfunU listenF); ("accept", site_cfunU acceptF);
                      ("connect", site_cfunU connectF); ("close", site_cfunU closeF);
                      ("send", site_cfunU sendF); ("recv", site_cfunU recvF);
                      ("htons", site_cfunU htonsF); ("ntohs", site_cfunU ntohsF);
                      ("htonl", site_cfunU htonlF); ("ntohl", site_cfunU ntohlF);
                      ("inet_addr", site_cfunU inet_addrF)];
    ModSem.mn := "Net";
    ModSem.initial_st := (ge, Z_map.empty node_sockets, @nil Z)↑
  |}.

End DEF.

Fixpoint init_size (t : type) : Z :=
  match t with
  | Tint I16 _ _ => 2%Z
  | Tint I32 _ _ | Tfloat F32 _ => 4%Z
  | Tlong _ _ | Tfloat F64 _ => 8%Z
  | Tpointer _ _ => if Archi.ptr64 then 8%Z else 4%Z
  | Tarray t' n _ => (init_size t' * Z.max 0 n)%Z
  | _ => 1%Z
  end.
    
Definition gvar_default (t: type) := AST.mkglobvar t [AST.Init_space (init_size t)] false false.

Definition Net: Mod.t :=
  {|
    Mod.get_modsem := fun sk => NetSem (load_skenv sk);
    Mod.sk := [(ident_of_string "errno", AST.Gvar (gvar_default tint))]
  |}.
    
End MOD.

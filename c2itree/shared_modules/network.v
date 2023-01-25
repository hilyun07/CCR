Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Any.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import FMapList.
Require Import OrderedTypeEx.

Module Z_map := Make OrderedTypeEx.Z_as_OT.

From compcert Require Import
    Ctypes Values Integers.

Require Import parse_compcert.

Section DEF.
Definition node_id := Z.
Definition sock_fd := Z.


Inductive Errcode: Type :=
| DEF (* When setting error number isn't needed *)
| EACCES
| EAFNOSUPPORT
| EINVAL
| EMFILE
| ENFILE
| ENOBUFS
| ENOMEM
| EPROTONOSUPPORT
| EADDRINUSE
| EBADF
| ENOTSOCK
| EADDRNOTAVAIL
| EFAULT
| ELOOP
| ENAMETOOLONG
| ENOENT
| ENOTDIR
| EROFS
| EOPNOTSUPP
| EAGAIN
| EWOULDBLOCK
| ECONNABORTED
| EINTR
| EPROTO
| EPERM
| ENOSR
| ESOCKTNOSUPPORT
| ETIMEDOUT
| EALREADY
| ECONNREFUSED
| EINPROGRESS
| EISCONN
| ENETUNREACH
| EPROTOTYPE
| EDESTADDRREQ
| EMSGSIZE
| ENOTCONN
| EPIPE.

Hypothesis errval: Errcode -> val.

Variable (skenv: SkEnv.t).

Inductive opt_err (A: Type): Type :=
    | Err: Errcode -> val -> opt_err A
    | Cor: A -> opt_err A
    | Non: opt_err A.

Arguments Err {A} code v.
Arguments Cor {A} a.
Arguments Non {A}.


Definition unwrapUErr {X: Type} (x: opt_err X) (f: X -> itree Es val): itree Es val :=
    match x with
    | Non => triggerUB
    | Cor x => f x
    | Err code v => errno <- (skenv.(SkEnv.id2blk) "errno")?;;
        `_: val <- (ccallU "store" [Vptr (Pos.of_nat errno) Ptrofs.zero;
                                    errval code]);;
        Ret v
    end.

Notation "x <- t1 ?*;; t2" := (unwrapUErr t1 (fun x => t2))
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*;; t2" := (unwrapUErr t1 (fun _ => t2))
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*;; t2" :=
    (unwrapUErr t1 (fun x_ => match x_ with p => t2 end))
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.

Definition opt_err_map {A B: Type} (f: A -> B) (o: opt_err A): opt_err B :=
    match o with
    | Cor a => Cor (f a)
    | Err code v => Err code v
    | Non => Non
    end.

Definition opt_to_opt_err {A: Type} (o: option A): opt_err A :=
    match o with
    | None => Non
    | Some x => Cor x
    end.

Variable address: Type.

Definition get_pid: itree Es node_id :=
    `pid:val <- ccallU "getpid" ([]:list val);;
    pid <- (parg (Tlong Unsigned noattr) pid)?;;
    Ret pid.

Record socket := {
    sock_addr: option address;
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
    | None => Err EBADF (Vint Int.mone)
    | Some x => Cor x
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
    | None => Non
    | Some node_socks =>
        match Z_map.find fd node_socks.(socks_sockmap) with
        | None => Err EBADF (Vint Int.mone)
        | Some sock =>
            let sock := Build_socket sock.(sock_addr)
                sock.(sock_queue) backlog in
            update_socket socks sock_pid fd sock
        end
    end.

Definition push_connection socks id_tgt fd_tgt id_src fd_src : opt_err sockets :=
    match Z_map.find id_tgt socks with
    | None => Non
    | Some node_socks =>
        match Z_map.find fd_tgt node_socks.(socks_sockmap) with
        | None => Err EBADF (Vint Int.mone)
        | Some sock =>
            if (Z.of_nat (List.length sock.(sock_queue))
                =? sock.(sock_max_queue))%Z
            then Err ETIMEDOUT (Vint Int.mone)
            else let sock := Build_socket sock.(sock_addr)
                (sock.(sock_queue) ++ [(id_src, fd_src)]) sock.(sock_max_queue) in
            update_socket socks id_tgt fd_tgt sock
        end
    end.

Definition pop_connection socks sock_pid fd: opt_err (sockets * (node_id * sock_fd)) :=
    match Z_map.find sock_pid socks with
    | None => Non
    | Some node_socks =>
        match Z_map.find fd node_socks.(socks_sockmap) with
        | None => Err EBADF (Vint Int.mone)
        | Some sock =>
            match sock.(sock_queue) with
            | [] => Err EWOULDBLOCK (Vint Int.mone)
            | src :: queue =>
                let sock := Build_socket sock.(sock_addr) queue
                    sock.(sock_max_queue) in
                opt_err_map (fun socks => (socks, src))
                    (update_socket socks sock_pid fd sock)
            end
        end
    end.

Definition sock_connect socks sock_pid fd tgt: opt_err sockets :=
    match Z_map.find sock_pid socks with
    | None => Non
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
    | None => Non
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
    | None => Non
    | Some node_socks =>
        match Z_map_find fd node_socks.(socks_csockmap) with
        | Non => Non
        | Err c v => Err c v
        | Cor csock => match csock.(csock_msg) with
            | None => Err DEF (Vint Int.zero)
            | Some msgl => Cor msgl
            end
        end
    end.

Definition get_tgt socks sock_pid fd: opt_err (node_id * sock_fd) :=
    match Z_map.find sock_pid socks with
    | None => Non
    | Some node_socks =>
        opt_err_map (fun csock => csock.(csock_tgt))
        (Z_map_find fd node_socks.(socks_csockmap))
    end.

Hypothesis addr_eq_dec: address -> address -> bool.
Hypothesis read_addr: block -> ptrofs -> address.

Definition find_addr_socket_node sockmap addr: opt_err sock_fd :=
    Z_map.fold
        (fun fd sock (x: opt_err sock_fd) => match x with
        | Err c v => match sock.(sock_addr) with
            | None => Err c v
            | Some addr' => if addr_eq_dec addr addr' then Cor fd
                else Err c v
            end
        | Cor fd => Cor fd
        | Non => Non
        end)
        sockmap (Err ECONNREFUSED (Vint Int.mone)).

Definition find_addr_socket socks addr: opt_err (node_id * sock_fd) :=
    Z_map.fold
        (fun sock_pid node_socks (x: opt_err (node_id * sock_fd))
        => match x with
        | Err c v => opt_err_map (fun fd => (sock_pid, fd))
            (find_addr_socket_node node_socks.(socks_sockmap) addr)
        | Cor id_fd => Cor id_fd
        | Non => Non end)
        socks (Err ECONNREFUSED (Vint Int.mone)).

Definition socketF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        '(domain, (type, protocol))
            <- (pargs [Tint I32 Signed noattr;
                      Tint I32 Signed noattr;
                      Tint I32 Signed noattr] varg)?;;
        (* Arguments are ignored for now *)

        let sock := Build_socket None [] 0%Z in
        `pid: node_id <- get_pid;;
        let (socks, fd) := add_socket socks pid sock in

        trigger (PPut socks↑);;;
        
        Ret (Vint (Int.repr fd)).

Definition bindF: list val -> itree Es val :=
    fun varg => 
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tpointer (Tint I32 Unsigned noattr) noattr] varg)?;;
        
        let addr := read_addr addr_b addr_ofs in
        
        let sock := Build_socket (Some addr) [] 0%Z in
        
        `pid: node_id <- get_pid;;
        socks <- (update_socket socks pid sockfd sock)?*;;

        trigger (PPut socks↑);;;
        Ret (Vint Int.zero).

Definition listenF: list val -> itree Es val :=
    fun varg => 
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        '(sockfd, backlog) <- (pargs [Tint I32 Signed noattr;
                                    Tint I32 Signed noattr] varg)?;;

        `pid: node_id <- get_pid;;
        socks <- (set_backlog socks pid sockfd backlog)?*;;

        trigger (PPut socks↑);;;
        Ret (Vint Int.zero).

Definition acceptF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        '(sockfd, (addr, addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tpointer (Tint I32 Unsigned noattr) noattr] varg)?;;

        `pid: node_id <- get_pid;;
        '(socks, src) <- (pop_connection socks pid sockfd)?*;;

        socks <- (sock_connect socks (fst src) (snd src) (pid, sockfd))?*;;

        let ctgt := Build_csocket src (Some []) in
        let (socks, fd_ctgt) := add_csocket socks pid ctgt in

        (* Need to find and write address *)

        trigger (PPut socks↑);;;
        Ret (Vint (Int.repr fd_ctgt)).

Definition connectF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        '(sockfd, ((addr_b, addr_ofs), addrlen))
            <- (pargs [Tint I32 Signed noattr;
                        Tpointer (Tstruct xH noattr) noattr;
                        Tint I32 Unsigned noattr] varg)?;;

        let addr := read_addr addr_b addr_ofs in
        tgt <- (find_addr_socket socks addr)?*;;

        `pid: node_id <- get_pid;;
        socks <- (push_connection socks (fst tgt) (snd tgt) pid sockfd)?*;;

        (* Need to bind socket to an address *)

        trigger (PPut socks↑);;;
        Ret (Vint Int.zero).

Definition closeF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

        fd <- (pargs [Tint I32 Signed noattr] varg)?;;

        `pid: node_id <- get_pid;;
        socks <- (close_csock socks pid fd)?*;;
        tgt <- (get_tgt socks pid fd)?*;;
        socks <- (close_csock socks (fst tgt) (snd tgt))?*;;

        trigger (PPut socks↑);;;
        Ret (Vint Int.zero).

Definition read_message buf msg_len: itree Es () :=
    ITree.iter (fun '(i, msg) =>
        if (i <? msg_len)%Z then
            let ptr := (Val.add buf (Vint (Int.repr (i * 8)%Z))) in
            `v: val <- ccallU "load" [ptr];;
            Ret (inl (i + 1, msg ++ [v])%Z)
        else
            trigger (PPut msg↑);;;
            Ret (inr tt)
        ) (0%Z, []).

Definition sendF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

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

            trigger (PPut socks↑);;;
            Ret (Vlong (Int64.repr len)).

Definition write_message buf buf_len msg: itree Es val :=
    ITree.iter (fun '(i, msg) =>
        match msg with
        | [] => Ret (inr (Vlong (Int64.repr i)))
        | v :: msg =>
            if (i <? buf_len)%Z then
                let ptr := (Val.add buf (Vint (Int.repr (i * 8)%Z))) in
                `_: val <- ccallU "store" [ptr; v];;
                Ret (inl (i + 1, msg))%Z
            else
                Ret (inr (Vlong (Int64.repr i)))
        end)
        (0%Z, msg).

Definition recvF: list val -> itree Es val :=
    fun varg =>
        socks <- trigger (PGet);;
        `socks: sockets <- socks↓?;;

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

Definition NetSem: ModSem.t :=
  {|
    ModSem.fnsems := [("socket", cfunU socketF); ("bind", cfunU bindF);
                      ("listen", cfunU listenF); ("accept", cfunU acceptF);
                      ("connect", cfunU connectF); ("close", cfunU closeF);
                      ("send", cfunU sendF); ("recv", cfunU recvF)];
    ModSem.mn := "Net";
    ModSem.initial_st := (Z_map.empty node_sockets)↑
  |}.

Definition Net: Mod.t :=
  {|
    Mod.get_modsem := fun _ => NetSem;
    Mod.sk := Sk.unit
  |}.

    
End DEF.

Section TEST.

  Definition errval : Errcode -> val := fun _ => Vint Int.zero.
  
  Definition skenv : SkEnv.t :=
    {|
      SkEnv.blk2id := fun blk =>
                        if Nat.eqb blk 127
                        then Some "errno" else None;
      SkEnv.id2blk := fun id =>
                        if id =? "errno"
                        then Some 127 else None
    |}.

  Definition address := nat.

End TEST.

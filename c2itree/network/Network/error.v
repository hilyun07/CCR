Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import ConvC2ITree.
From compcert Require Import Values Integers.

Section Error.

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

Definition errval: Errcode -> val := fun _ => Vint (Int.zero).

Import Cskel.
Context {sk: Sk.t}.
Let skenv: SkEnv.t := load_skenv sk.

Inductive opt_err (A: Type): Type :=
    | ErrKo: Errcode -> val -> opt_err A
    | ErrOk: A -> opt_err A
    | ErrUB: opt_err A.

Arguments ErrKo {A} code v.
Arguments ErrOk {A} a.
Arguments ErrUB {A}.

Definition set_errno code v: itree Es val :=
    errno <- (skenv.(SkEnv.id2blk) "errno")?;;
    `_: val <- (ccallU "store" [Vptr errno Ptrofs.zero;
                                errval code]);;
    Ret v.

Definition unwrapUErr {X: Type} (x: opt_err X) (f: X -> itree Es val) (g: val -> itree Es val): itree Es val :=
    match x with
    | ErrUB => triggerUB
    | ErrOk x => f x
    | ErrKo EWOULDBLOCK v => g v
    | ErrKo code v => set_errno code v
    end.

Definition opt_err_map {A B: Type} (f: A -> B) (o: opt_err A): opt_err B :=
    match o with
    | ErrOk a => ErrOk (f a)
    | ErrKo code v => ErrKo code v
    | ErrUB => ErrUB
    end.

Definition opt_to_opt_err {A: Type} (o: option A): opt_err A :=
    match o with
    | None => ErrUB
    | Some x => ErrOk x
    end.

End Error.

Arguments ErrKo {A} code v.
Arguments ErrOk {A} a.
Arguments ErrUB {A}.

(*Notation "x <- t1 ?*;; t2" := (unwrapUErr t1 (fun x => t2) (fun v => set_errno EWOULDBLOCK v))
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*;; t2" := (unwrapUErr t1 (fun _ => t2) (fun v => set_errno EWOULDBLOCK v))
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*;; t2" :=
    (unwrapUErr t1 (fun x_ => match x_ with p => t2 end) (fun v => set_errno EWOULDBLOCK v))
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
Notation "x <- t1 ?*[ g ];; t2" := (unwrapUErr t1 (fun x => t2) g)
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*[ g ];; t2" := (unwrapUErr t1 (fun _ => t2) g)
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*[ g ];; t2" :=
    (unwrapUErr t1 (fun x_ => match x_ with p => t2 end) g)
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.*)

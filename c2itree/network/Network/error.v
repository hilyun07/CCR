Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
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

Context {skenv: SkEnv.t}.

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
        `_: val <- (ccallU "store" [Vptr errno Ptrofs.zero;
                                    errval code]);;
        Ret v
    end.

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

End Error.

Arguments Err {A} code v.
Arguments Cor {A} a.
Arguments Non {A}.

Notation "x <- t1 ?*;; t2" := (unwrapUErr t1 (fun x => t2))
    (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ?*;; t2" := (unwrapUErr t1 (fun _ => t2))
    (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ?*;; t2" :=
    (unwrapUErr t1 (fun x_ => match x_ with p => t2 end))
    (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.

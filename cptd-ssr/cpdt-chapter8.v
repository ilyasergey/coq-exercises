Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path pred prelude idynamic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive type : Set := Nat | Bool | Prod of type & type. 

(*
Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.
*)

Inductive exp (t : type) := 
  NConst' of nat & t = Nat
| Plus' of exp Nat & exp Nat & t = Nat
| Eq' of exp Nat & exp Nat & t = Bool

| BConst' of bool & t = Bool
| And' of exp Bool & exp Bool & t = Bool
| If' t' of exp Bool & exp t' & exp t' & t = t'

| Pair' t1 t2 of exp t1 & exp t2 & t = (Prod t1 t2)
| Fst' t1 t2 of exp (Prod t1 t2) & t = t1
| Snd' t1 t2 of exp (Prod t1 t2) & t = t2.


Definition NConst n := NConst' n (erefl _).
Definition Plus e1 e2 := Plus' e1 e2 (erefl _).
Definition Eq e1 e2 := Eq' e1 e2 (erefl _).

Definition BConst n := BConst' n (erefl _).
Definition And e1 e2 := And' e1 e2 (erefl _).
Definition If t b e1 e2 := @If' t t b e1 e2 (erefl _).

Definition Pair t1 t2 e1 e2 := @Pair' _ t1 t2 e1 e2 (erefl _).
Definition Fst t1 t2 e := @Fst' _ t1 t2 e (erefl _).
Definition Snd t1 t2 e := @Snd' _ t1 t2 e (erefl _).

(*
CoInductive exp_spec t : exp t -> Type := 
| nconst_exp_spec n : t = Nat -> forall pf, exp_spec (icoerce id (NConst n) pf) 
| plus_exp_spec e1 e2 : t = Nat -> forall pf, exp_spec (icoerce id (Plus e1 e2) pf)
| eq_exp_spec e1 e2 : t = Nat -> forall pf, exp_spec (icoerce id (Eq e1 e2) pf).

Lemma expP t (e : exp t) : exp_spec e.
Proof. admit. Qed.
*)


Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type.

Lemma blah1 t : t = Nat -> nat = typeDenote t.
Proof. by move=>->. Defined.

Print blah1.
Check eq_ind_r. 
Check eq_rect.
Check icoerce. 
Check typeDenote.

Definition get_eq t (e : exp t) : type :=
  match e with
    NConst' n r => Nat
 | Plus' _ _ r => Nat
 | Eq' _ _ r => Nat
 | _ => Bool
 end.

Lemma expDenote t (e : exp t) : get_eq e = t.
admit.

Program Fixpoint expDenote t (e : exp t) : typeDenote (get_eq e) :=
  match e with
    | NConst' n r => n 
    | Plus' e1 e2 r => expDenote e1 + expDenote e2
    | Eq' e1 e2 r => icoerce id ((expDenote e1) == (expDenote e2)) (eq_ind_r _ r (erefl _)) 

    | BConst' b r => icoerce id b (eq_ind_r _ r (erefl _)) 
    | And' e1 e2 r => icoerce id (expDenote e1 && expDenote e2) (eq_ind_r _ r (erefl _))
    | If' _ e' e1 e2 _ => if expDenote e' then expDenote e1 else expDenote e2

    | Pair' t1 t2 e1 e2 r => icoerce id (expDenote e1, expDenote e2) (eq_ind_r _ r (erefl _))
    | Fst' _ _ e' _ => fst (expDenote e')
    | Snd' _ _ e' _ => snd (expDenote e')
  end.


Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
    | NConst n => n
    | Plus e1 e2 => expDenote e1 + expDenote e2
    | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

    | BConst b => b
    | And e1 e2 => expDenote e1 && expDenote e2
    | If _ e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

    | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
    | Fst _ _ e' => fst (expDenote e')
    | Snd _ _ e' => snd (expDenote e')
  end.



Definition pairOutType (t : type) := option (if t is Prod t1 t2 then exp t1 * exp t2 else unit).

Definition pairOut t (e : exp t) :=
  match e in (exp t) return (pairOutType t) with
    | Pair _ _ e1 e2 => Some (e1, e2)
    | _ => None
  end.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
    | NConst n => NConst n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp Nat with
        | NConst n1, NConst n2 => NConst (n1 + n2)
        | _, _ => Plus e1' e2'
      end
    | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp Bool with
        | NConst n1, NConst n2 => BConst (n1 == n2)
        | _, _ => Eq e1' e2'
      end

    | BConst b => BConst b
    | And e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp Bool with
        | BConst b1, BConst b2 => BConst (b1 && b2)
        | _, _ => And e1' e2'
      end
    | If _ e e1 e2 =>
      let e' := cfold e in
      match e' with
        | BConst true => cfold e1
        | BConst false => cfold e2
        | _ => If e' (cfold e1) (cfold e2)
      end

    | Pair _ _ e1 e2 => Pair (cfold e1) (cfold e2)
    | Fst _ _ e =>
      let e' := cfold e in
      match pairOut e' with
        | Some p => fst p
        | None => Fst e'
      end
    | Snd _ _ e =>
      let e' := cfold e in
      match pairOut e' with
        | Some p => snd p
        | None => Snd e'
      end
end.

Theorem cfold_correct t (e : exp t): expDenote e = expDenote (cfold e).
Proof.
elim:e=>//. move=>e1 H1 e2 H2.
- rewrite [cfold _]/=.
  case: e1.

- simpl. case: e1.


move: (@expDenote Nat e1) (@expDenote Nat e2) H1 H2.

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path Eqdep.
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

Inductive exp t := 
  NConst' of Nat = t & nat
| Plus' of Nat = t & exp Nat & exp Nat
| Eq' of  Bool = t & exp Nat & exp Nat
| BConst' of Bool = t & bool 
| And' of Bool = t & exp Bool & exp Bool 
| If of exp Bool & exp t & exp t
| Pair' t1 t2 of Prod t1 t2 = t & exp t1 & exp t2 
| Fst t2 of exp (Prod t t2)
| Snd t1 of exp (Prod t1 t).

Notation NConst := (NConst' (erefl _)).
Notation Plus := (Plus' (erefl _)).
Notation Eq := (Eq' (erefl _)).
Notation BConst := (BConst' (erefl _)).
Notation And := (And' (erefl _)).
Notation Pair := (Pair' (erefl _)).

(* a better induction principle, to gather the like constructors *)
(* and remove unnecessary type equations *)

Lemma exp_ind' (P : forall t : type, exp t -> Prop) : 
        [/\ forall n, P Nat (NConst n) &
            forall b, P Bool (BConst b)] ->
        [/\ forall e1 e2, P Nat e1 -> P Nat e2 -> P Nat (Plus e1 e2),
            forall e1 e2, P Nat e1 -> P Nat e2 -> P Bool (Eq e1 e2) &
            forall e1 e2, P Bool e1 -> P Bool e2 -> P Bool (And e1 e2)] ->
        (forall t e e1 e2, P Bool e -> P t e1 -> P t e2 -> P t (If e e1 e2)) ->
        (forall t1 t2 e1 e2, P t1 e1 -> P t2 e2 -> P (Prod t1 t2) (Pair e1 e2)) ->
        [/\ forall t1 t2 e, P (Prod t1 t2) e -> P t1 (Fst e) &
            forall t1 t2 e, P (Prod t1 t2) e -> P t2 (Snd e)] ->
        forall t e, P t e.
Proof. by case=>?? [???] ?? [??] t; elim=>t' *; try subst t'; intuition. Qed.

Definition cast T (t t' : type) (r : t = t') (e : T t) :=
  match r in (_ = t') return T t' with erefl => e end.

(* eliminating casts *)
Lemma eqc T t (r : t = t) (e : T t) : cast r e = e.
Proof. by move: r; apply: Streicher_K. Qed.

(*
(* re-introducing casts *)
Lemma recast T t t' (P : forall t, t' = t -> T t) (r : t' = t) : 
        P t r = cast r (P t' (erefl _)).
Proof. by move: (r); rewrite -r; apply: Streicher_K. Qed.

(* better case analysis over exp t that *)
(* doesn't go down to primed constructors *)
(* this is a boring boilerplate, which is in Coq done by tactics *)
(* but let's not use tactics here *)

Inductive exp_spec t : exp t -> Type := 
| nconst_exp n : Nat = t -> forall pf, exp_spec (cast pf (NConst n)) 
| plus_exp e1 e2 : Nat = t -> forall pf, exp_spec (cast pf (Plus e1 e2))
| eq_exp e1 e2 : Bool = t -> forall pf, exp_spec (cast pf (Eq e1 e2))
| bconst_exp b : Bool = t -> forall pf, exp_spec (cast pf (BConst b))
| and_exp e1 e2 : Bool = t -> forall pf, exp_spec (cast pf (And e1 e2))
| if_exp b (e1 e2 : exp t) : exp_spec (If b e1 e2)
| pair_exp t1 t2 (e1 : exp t1) (e2 : exp t2) : 
    Prod t1 t2 = t -> forall pf, exp_spec (cast pf (Pair e1 e2))
| fst_exp t2 (e : exp (Prod t t2)) : exp_spec (Fst e)
| snd_exp t1 (e : exp (Prod t1 t)) : exp_spec (Snd e).

Lemma expP t (e : exp t) : exp_spec e.
Proof. case: e=>*. rewrite 1?(recast (fun t => _)); constructor. Qed.

(* test goal *)
Lemma xx n (x : exp Nat) : x = NConst n.
Proof. case/expP: x=>//. Abort.
*)

Fixpoint typeDenote (t : type) : Set :=
  match t with
    Nat => nat
  | Bool => bool
  | Prod t1 t2 => prod (typeDenote t1) (typeDenote t2)
  end.

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
    NConst' r n => cast r n
  | Plus' r e1 e2 => cast r (expDenote e1 + expDenote e2)
  | Eq' r e1 e2 => cast r (expDenote e1 == expDenote e2) 
  | BConst' r b => cast r b
  | And' r e1 e2 => cast r (expDenote e1 && expDenote e2)
  | If e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2
  | Pair' _ _ r e1 e2 => cast r (expDenote e1, expDenote e2)
  | Fst _ e' => fst (expDenote e')
  | Snd _ e' => snd (expDenote e')
  end.

Lemma fst_out t1 t2 s1 s2 : Prod t1 t2 = Prod s1 s2 -> t1 = s1.
Proof. by case. Defined.

Lemma snd_out t1 t2 s1 s2 : Prod t1 t2 = Prod s1 s2 -> t2 = s2.
Proof. by case. Qed.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
    NConst' r n => NConst' r n
  | Plus' r e1 e2 => 
      let: (e1', e2') := (cfold e1, cfold e2) in
      if (e1', e2') is (NConst' _ n1, NConst' _ n2) then NConst' r (n1 + n2)
      else Plus' r e1' e2'
  | Eq' r e1 e2 =>
      let: (e1', e2') := (cfold e1, cfold e2) in
      if (e1', e2') is (NConst' _ n1, NConst' _ n2) then BConst' r (n1 == n2) 
      else Eq' r e1' e2' 
  | BConst' r b => BConst' r b
  | And' r e1 e2 =>
      let: (e1', e2') := (cfold e1, cfold e2) in
      if (e1', e2') is (BConst' _ b1, BConst' _ b2) then BConst' r (b1 && b2)
      else And' r e1' e2' 
  | If e e1 e2 =>
      let: e' := cfold e in
      match e' with
        BConst' _ true => cfold e1
      | BConst' _ false => cfold e2
      | _ => If e' (cfold e1) (cfold e2)
      end
  | Pair' _ _ r e1 e2 => Pair' r (cfold e1) (cfold e2) 
  | Fst _ e =>
      let: e' := cfold e in
      if e' is Pair' _ _ r e1 e2 then cast (fst_out r) e1 else Fst e'
  | Snd _ e =>
      let e' := cfold e in
      if e' is Pair' _ _ r e1 e2 then cast (snd_out r) e2 else Snd e'
  end. 

Lemma cfold_correct t (e : exp t) : expDenote e = expDenote (cfold e).
Proof.
elim/exp_ind': e=>//=.
- by split=>?? ->->; do 2![case: (cfold _)=>//= *]; rewrite !eqc. 
- by move=>???? ->->->; case: (cfold _)=>//= *; rewrite eqc; case: ifP.
- by move=>???? ->->.
by split=>??? ->; case: (cfold _)=>//= ?? r; case: r (r)=>->-> *; rewrite !eqc.
Qed.




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

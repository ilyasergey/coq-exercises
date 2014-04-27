Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive type := Nat | Bool | Prod of type & type. 

Fixpoint typeDenote t :=
  match t with
    Nat => nat
  | Bool => bool
  | Prod t1 t2 => prod (typeDenote t1) (typeDenote t2)
  end.

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

(* a better induction principle; gathers the like constructors *)
(* and removes unnecessary type equations *)

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
(* One can recover the behavior of the family as follows *)

Inductive exp_spec : forall t', exp t' -> Type := 
  nconst_exp n : exp_spec (NConst n)
| plus_exp e1 e2 : exp_spec (Plus e1 e2)
| eq_exp e1 e2 : exp_spec (Eq e1 e2)
| bconst_exp b : exp_spec (BConst b)
| and_exp e1 e2 : exp_spec (And e1 e2)
| if_exp t b (e1 e2 : exp t) : exp_spec (If b e1 e2)
| pair_exp t1 t2 (e1 : exp t1) (e2 : exp t2) : 
    exp_spec (Pair e1 e2)
| fst_exp t t2 (e : exp (Prod t t2)) : exp_spec (Fst e)
| snd_exp t t1 (e : exp (Prod t1 t)) : exp_spec (Snd e).

Lemma expP t (e : exp t) : exp_spec e.
Proof. by case: e=>*; try subst t; constructor. Qed.

(*
Given t : type, x : exp t, casing over (expP x) will rewrite
occurences of x in the goal by NConst n, Plus e1 e2, etc, and the
occurences of t by Nat, Nat, Bool, etc, as it corresponds.

Very often this results in ill-typed goals, so one needs to use
occurence selectors and patterns to prevent some occurence from being
changed.
*)

(* test goals *)
Lemma xx1 n (x : exp Nat) : x = NConst n.
Proof. 
case: {-1}Nat x / (expP x) (erefl _). 
(* the above works, because we protected the first occurence of pattern Nat
(which is what t is in this case, from being changed. But all the other occurences
are changed. Notice also that we had to first abstract erefl, as the first
occurence of Nat is precisely in the type of the erefl *)
Abort.

Lemma xx2 t (x : exp t) : t = Nat /\ x = x.
Proof. 
case: {-1}t x / (expP x).
Abort.
*)

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

Lemma pair_out t1 t2 s1 s2 : Prod t1 t2 = Prod s1 s2 -> t1 = s1 /\ t2 = s2.
Proof. by case. Qed.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
    NConst' r n => NConst' r n
  | Plus' r e1 e2 => 
      let: (f1, f2) := (cfold e1, cfold e2) in
      if (f1, f2) is (NConst' _ n1, NConst' _ n2) then NConst' r (n1 + n2)
      else Plus' r f1 f2
  | Eq' r e1 e2 =>
      let: (f1, f2) := (cfold e1, cfold e2) in
      if (f1, f2) is (NConst' _ n1, NConst' _ n2) then BConst' r (n1 == n2) 
      else Eq' r f1 f2 
  | BConst' r b => BConst' r b
  | And' r e1 e2 =>
      let: (f1, f2) := (cfold e1, cfold e2) in
      if (f1, f2) is (BConst' _ b1, BConst' _ b2) then BConst' r (b1 && b2)
      else And' r f1 f2 
  | If e e1 e2 =>
      let: f := cfold e in
      match f with
        BConst' _ true => cfold e1
      | BConst' _ false => cfold e2
      | _ => If f (cfold e1) (cfold e2)
      end
  | Pair' _ _ r e1 e2 => Pair' r (cfold e1) (cfold e2) 
  | Fst _ e =>
      let: f := cfold e in
      if f is Pair' _ _ r e1 e2 then cast (proj1 (pair_out r)) e1 else Fst f
  | Snd _ e =>
      let f := cfold e in
      if f is Pair' _ _ r e1 e2 then cast (proj2 (pair_out r)) e2 else Snd f
  end. 

Lemma cfold_correct t (e : exp t) : expDenote e = expDenote (cfold e).
Proof.
elim/exp_ind': e=>//=.
- by split=>?? ->->; do 2![case: (cfold _)=>//= *]; rewrite !eqc. 
- by move=>???? ->->->; case: (cfold _)=>//= *; rewrite eqc; case: ifP.
- by move=>???? ->->.
by split=>??? ->; case: (cfold _)=>//= ?? r; case: r (r)=>->-> *; rewrite !eqc.
Qed.

(* Implementation using an indexed family *)

Inductive exp2 : type -> Type :=
  NConst2 of nat : exp2 Nat
| Plus2 of exp2 Nat & exp2 Nat : exp2 Nat
| Eq2 of exp2 Nat & exp2 Nat : exp2 Bool
| BConst2 of bool : exp2 Bool
| And2 of exp2 Bool & exp2 Bool : exp2 Bool
| If2 t of exp2 Bool & exp2 t & exp2 t : exp2 t
| Pair2 t1 t2 of exp2 t1 & exp2 t2 : exp2 (Prod t1 t2)
| Fst2 t1 t2 of exp2 (Prod t1 t2) : exp2 t1
| Snd2 t1 t2 of exp2 (Prod t1 t2) : exp2 t2.

Fixpoint expDenote2 t (e : exp2 t) : typeDenote t :=
  match e with
    NConst2 n => n
  | Plus2 e1 e2 => expDenote2 e1 + expDenote2 e2
  | Eq2 e1 e2 => expDenote2 e1 == expDenote2 e2
  | BConst2 b => b
  | And2 e1 e2 => expDenote2 e1 && expDenote2 e2
  | If2 _ e' e1 e2 => if expDenote2 e' then expDenote2 e1 else expDenote2 e2
  | Pair2 _ _ e1 e2 => (expDenote2 e1, expDenote2 e2)
  | Fst2 _ _ e' => fst (expDenote2 e')
  | Snd2 _ _ e' => snd (expDenote2 e')
  end.

Definition pairOutType t := 
  option (if t is Prod t1 t2 then exp2 t1 * exp2 t2 else unit).

Definition pair_out2 t (e : exp2 t) :=
  if e is Pair2 _ _ e1 e2 in exp2 t return pairOutType t 
  then Some (e1, e2) else None. 

Fixpoint cfold2 t (e : exp2 t) : exp2 t :=
  match e with
    NConst2 n => NConst2 n
  | Plus2 e1 e2 =>
      let: (f1, f2) := (cfold2 e1, cfold2 e2) in
      if (f1, f2) is (NConst2 n1, NConst2 n2) then NConst2 (n1 + n2)
      else Plus2 f1 f2
  | Eq2 e1 e2 =>
      let: (f1, f2) := (cfold2 e1, cfold2 e2) in
      if (f1, f2) is (NConst2 n1, NConst2 n2) then BConst2 (n1 == n2)
      else Eq2 f1 f2
  | BConst2 b => BConst2 b
  | And2 e1 e2 =>
      let: (f1, f2) := (cfold2 e1, cfold2 e2) in
      if (f1, f2) is (BConst2 b1, BConst2 b2) then BConst2 (b1 && b2)
      else And2 f1 f2
  | If2 _ e e1 e2 =>
      let: f := cfold2 e in
      match f with
        BConst2 true => cfold2 e1
      | BConst2 false => cfold2 e2
      | _ => If2 f (cfold2 e1) (cfold2 e2)
      end
  | Pair2 _ _ e1 e2 => Pair2 (cfold2 e1) (cfold2 e2)
  | Fst2 _ _ e =>
      let: f := cfold2 e in
      if pair_out2 f is Some p then fst p else Fst2 f
  | Snd2 t1 t2 e1 =>
      let: f := cfold2 e1 in
      if pair_out2 f is Some p then snd p else Snd2 f
end.

Lemma cfold_correct2 t (e : exp2 t) : expDenote2 e = expDenote2 (cfold2 e).
Proof.
elim: e=>//. 
- move=>/= e1 -> e2 ->. 
Set Printing All.
(* in this goal, it's really impossible to count the occurences *)
(* moreover, the casing will change Nat to other types, but I have *)
(* addition in the goal, which will thus always be ill-typed after casing *)
(* it's not clear that that can even be protected by an occurence selection *)
(* hence, i don't think the right first move here is to case *)
(* rather, one has to obtain some type equations first, maybe by *)
(* inversion, or some other tactic *)
(* in principle, this whole approach looks completely wrongheaded *)
try case: {-3}Nat / (cfold2 e1).
Unset Printing All.
Abort.

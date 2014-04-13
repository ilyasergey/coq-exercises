Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive evenP: nat -> Prop :=
| EvenO  : evenP 0
| EvenSs : forall n, evenP n -> evenP (n + 2).

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.

Lemma even_4: evenb 4.
Proof. done. Qed.

Theorem even_3_contra: ~evenb 3.
Proof. done. Qed.

(*Proof by induction on the rule (for evenP) *)
Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
elim=>//; move=>k Ek Hk Hm=>/=; rewrite -(addnC m) addnA; constructor. 
by rewrite addnC; apply: Hk. 
Qed.

(* TODO: How to build induction on recursive function? *)
Lemma evenb_plus m n : evenb m -> evenb n -> evenb (m + n).
Proof.
elim: m {-2}m (leqnn m)=>[|m IH]; case=>//.
by case=>// m' /ltnW /IH.
Qed.

Inductive evenP1 n : Prop :=
  Even01 of n = 0 | EvenSs1 m of n = m.+2 & evenP1 m.

Lemma evenP_contra': forall n', evenP n' -> forall n, n' = (n + 1 + n) -> False.
Proof.
move=>k; elim=>[n|]=>{k}.
-rewrite addnC addnA addn1.
 move=> E. move:(ltn0Sn (n+n))=>H; rewrite E in H.
 by move:(ltnn ((n+n).+1)); rewrite H. case. 
-move=>_ _ n. rewrite addnC addn0; case:n=>[|n]//=.
+by rewrite addn1 addnS addnC !addnS; move/eqP; rewrite !eqSS; move/eqP.
 (* TODO: what exactly is happened here? *)
move=>n H IHEven. case.
+by rewrite !addn0 (addnC 0) addn0 addnC add2n. 
 (* TODO: what exactly is happened here? *)
move=>n0; rewrite addn2 addn1 addnS addnC !addnS. 
move/eqP; rewrite !eqSS; move/eqP=>E; subst n. 
by apply: (IHEven n0); rewrite addnC addn1 addnS.
Qed.


Lemma evenP_contra: forall n, evenP (n + 1 + n) -> False.
Proof.
move=>n. move:(@evenP_contra' (n + 1 + n))=>H.
move/H=>H1. move:(H1 n)=> H2. apply:H2. done.
Qed.

(* TODO: How to characterize this general pattern when inducing of n<=n *)
Lemma even_contra n: evenb (n + 1 + n) -> False.
Proof.
elim: n {-2}n (leqnn n)=>[|n IH]; elim=>//.
case=>// m H1 H3; rewrite ltnS in H3.
move:(ltn_trans H3 (ltnSn n))=>/H1=> H4.
rewrite 2!addnS=>/=. 
by rewrite addnS addnC -(addnC 1) addnS addnS addnA /= in H4. 
Qed.




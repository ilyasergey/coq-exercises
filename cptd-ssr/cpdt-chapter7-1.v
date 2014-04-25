Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Comp.
Variable A : Type.

Definition monotone (f : nat -> option A) := 
  forall n n' v, n <= n' -> f n = Some v -> f n' = Some v.

Structure comp := Comp {
  f_of :> nat -> option A;
  _ : monotone f_of}.

Lemma compP (f : comp) : monotone f. 
Proof. by case: f=>f; apply. Qed.

(* Can be run with a fuel up to 'n', delivering the result A *)
Definition run (f : comp) v := exists n, f n = Some v.

End Comp.

Prenex Implicits compP.


Section Bottom. 
Variable A : Type.

Lemma bottom_mono : monotone (fun _ => @None A).
Proof. by []. Qed.

Definition bottom := Comp bottom_mono.

Lemma run_bottom : forall v, ~ run bottom v. 
Proof. by move=>v []. Qed.

End Bottom.

Implicit Arguments bottom [A].


Section Return. 
Variables (A : Type) (v : A).

Lemma ret_mono : monotone (fun _ => Some v). 
Proof. by move=>n n' v' _ [->]. Qed.

Definition ret := Comp ret_mono. 

Lemma run_ret : run ret v. 
Proof. by exists 0. Qed.

End Return.


Section Bind.
Variables (A B : Type) (f1 : comp A) (f2 : A -> comp B).

Lemma bind_mono : monotone (fun n => obind (f2^~ n) (f1 n)).
Proof.
move=>n n' v /= H; case E: (f1 n)=>[v1|//]. 
by rewrite (compP H E); apply: compP H.
Qed.

Definition bind := Comp bind_mono. 

Lemma run_bind v1 v2 : run f1 v1 -> run (f2 v1) v2 -> run bind v2.
Proof.
case=>n1 E1 [n2 E2]; exists (maxn n1 n2); rewrite /bind /=.
by rewrite (compP (leq_maxl _ _) E1) /= (compP (leq_maxr _ _) E2).
Qed.

End Bind.

Notation "x <- f1 ; f2" :=
  (bind f1 (fun x => f2)) (right associativity, at level 70).

Definition meq A (f1 f2 : comp A) := forall n, f1 n = f2 n.


(* Proving monad laws *)

Lemma left_identity A B (v : A) (f : A -> comp B) : 
        meq (x <- ret v; f x) (f v).
Proof. by []. Qed.

Lemma right_identity A (f : comp A) : meq (x <- f; ret x) f.
Proof. by move=>n /=; case: (f n). Qed.

Lemma associativity A B C (f : comp A) (g : A -> comp B) (h : B -> comp C) : 
        meq (bind (bind f g) h) (x <- f; bind (g x) h).
Proof. by move=>n /=; case: (f n). Qed.


(* lattice stuff *)

Definition mleq A B n (f1 f2 : A -> comp B) := 
  forall x v, f2 x n = Some v -> f1 x n = Some v.

Lemma mleq_refl A B n (f : A -> comp B) : mleq n f f.
Proof. by []. Qed.

Hint Resolve mleq_refl.


Section Fix.
Variables (A B : Type) (f : (A -> comp B) -> (A -> comp B)).
Variable f_cont : 
  forall m (f1 f2 : A -> comp B), mleq m f1 f2 -> mleq m (f f1) (f f2). 

Fixpoint Fix' n x := if n is n'.+1 then f (Fix' n') x else bottom.

Lemma fix_mleq m n n' : n <= n' -> mleq m (Fix' n') (Fix' n). 
Proof. by elim: n n'=>// n IH [|n'] //= /IH; apply: f_cont. Qed.

Lemma fix_mono x : monotone (fun n => (Fix' n x) n).
Proof. by move=>n n' v H /(fix_mleq H); apply: compP. Qed.

Definition Fix x := Comp (@fix_mono x).

Lemma run_fix x v : run (f Fix x) v -> run (Fix x) v.
Proof. by case=>n H; exists n.+1; apply: compP (f_cont _ H). Qed.

End Fix.

Implicit Arguments Fix [A B].

Section MergeSortHelpers.

Variable A: Type.
Variable le: A -> A -> bool.

Fixpoint split (ls : list A) : list A * list A :=
  match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
	  (h1 :: ls1, h2 :: ls2)
  end.

Fixpoint insert (x : A) (ls : list A) : list A :=
  match ls with
    | nil => x :: nil
    | h :: ls' =>
      if le x h
      then x :: ls
      else h :: insert x ls'
  end.

Fixpoint merge (ls1 ls2 : list A) : list A :=
  match ls1 with
    | nil => ls2
    | h :: ls' => insert h (merge ls' ls2)
  end.

End MergeSortHelpers.

Program Definition mergeSort' A (le: A -> A -> bool): seq A -> comp (seq A) :=
Fix (fun (mergeSort : seq A -> comp (seq A)) 
         (ls : list A) =>
          if (length ls) > 1
          then let lss := split ls in
                   ls1 <- mergeSort (fst lss);
                   ls2 <- mergeSort (snd lss);
                   ret (merge le ls1 ls2)
          else ret ls) _.
(* Proving continuity of the argument *)
Next Obligation. 
move=> x y; elim: (length x > 1) H=>H//=. 
move: (H (split x).1); case (f2 (split x).1)=>//=f.
case:(f m)=>//=a Mf /(_ a erefl)->{f Mf}.
move: (H (split x).2); case (f2 (split x).2)=>//=f.
by case:(f m)=>//=b Mf /(_ b erefl)->{f Mf}.
Defined.

Definition leb := fun x y => x <= y.

Lemma test_mergeSort' : run (mergeSort' leb (2 :: 1 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
by exists 4.
Qed.

Program Definition looper : bool -> comp unit :=
Fix (fun looper (b : bool) =>
    if b then ret tt else looper b) _.
Next Obligation.
by move=> b; case; case b=>// /(H false tt).
Qed.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.













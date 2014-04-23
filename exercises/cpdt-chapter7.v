Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section computation. 

Variable A : Type.


(*

This is a suggested way to defined the computation. 
To my taste, it has a number of disadvantages:

- Constructor uses default name rather than a meaningful one;
- You can define no coresion from the DT to a function f;
- You are constrantly force to use projections (e.g., proj1_sig) insead of relyin to the coercion;

*)

(*
Definition computation := 
  {f : nat -> option A 
   | forall  (n : nat) (v : A),
     f n = Some v -> forall n', n <= n' -> f n' = Some v}.
*)

Structure computation := Comp {
  f_of :> nat -> option A;
  _ : forall n v n', f_of n = Some v -> n <= n' -> f_of n' = Some v}.

Lemma comp_mono (f : computation) n v n' : f n = Some v -> n <= n' -> f n' = Some v.
Proof. by case: f=>f; apply. Qed.

Definition runTo (m: computation) (n: nat) (v: A): Prop := m n = Some v.

(* Can be run with a fuel up to 'n', delivering the result A *)
Definition run (m: computation) (v: A): Prop := 
 exists n, runTo m n v.

End computation.

Section Bottom. 
Variable A : Type.

Definition Bottom : computation A.
by apply Comp with (f_of := (fun _ : nat => @None A)).
Defined.

Theorem run_Bottom : forall v, ~(run Bottom v). 
Proof. by move=>v; case=>n. Qed.
End Bottom.

Section Return. 
Variable A : Type. 
Variable v : A.

Definition Return : computation A.
exists (fun _ : nat => Some v).
by move=>n v' n'; case=><-.
Defined.

Theorem run_Return : run Return v. 
Proof. by exists 0. Qed.
End Return.

Lemma comp_max A (m : computation A) n1 n2 v : runTo m n1 v -> runTo m (maxn n1 n2) v.
Proof.
case:m=>/= f Hf; rewrite /runTo /==> E.
by move:(Hf n1 v (maxn n1 n2) E (leq_maxl n1 n2)).
Qed.

Section Bind.
Variables A B : Type.
Variable m1 : computation A.
Variable m2 : A -> computation B.

Definition Bind : computation B.
(* A shortcut for constructor 1 *)
 exists (fun n =>           
  let: f1 := m1 in
  if f1 n is Some v then 
   let: f2 := (m2 v) in f2 n
  else None). 
move=>n vb /=; case: m1=>/= f /(_ n) Hf n'.
case:(f n) n' Hf =>//a n' Hf E Hn'; move:(Hf a n' erefl Hn')=>{Hf f}->.
by case:m2 E=>/= f /(_ n vb n') Hf q; move:(Hf q Hn').
Defined.

Theorem run_Bind : forall (v1 : A) (v2 : B),
 run m1 v1
 -> run (m2 v1) v2
 -> run Bind v2.
Proof.
move=> v1 v2 [n1]E1[n2]E2; exists (maxn n1 n2).
move:(@comp_max A m1 n1 n2 v1 E1)=>{E1}E1.
rewrite /runTo /=; rewrite E1.
by move:(@comp_max B (m2 v1) n2 n1 v2 E2)=>{E2}E2; rewrite maxnC. 
Qed.

End Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq A (m1 m2 : computation A) := forall n, m1 n = m2 n.

(* Proving monad laws *)

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
Proof. by []. Qed.

Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
Proof. 
by move=> A m n; case:m=>/= f Hf; case:( f n)=>//.
Qed.

Theorem associativity : forall A B C (m : computation A)
  (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
Proof.
move=> A B C m f g n. 
by case:m=>/=p Hp; case:(p n)=>//.
Qed.


Section lattice.
Variable A : Type.

Definition leq (x y : option A) :=
 forall v, y = Some v -> x = Some v.

Lemma leq_refl x: leq x x.
Proof. by []. Qed.

End lattice.

Hint Resolve leq_refl.

Section Fix.

(** First, we have the function domain and range types. *)
Variables A B : Type.

(** Next comes the function body, which is written as though it can be
parameterized over itself, for recursive calls. *) 

Variable f : (A -> computation B) -> (A -> computation B).

Hypothesis f_cont : forall n v v2 x,
  runTo (f v2 x) n v                             (* f terminates with v2 in n steps *)
  -> forall (v1 : A -> computation B),
    (forall x, leq (v1 x n) (v2 x n))  (* v1 refines v2 wrt n steps *)
    -> runTo (f v1 x) n v.

Fixpoint Fix' (n : nat) (x : A) : computation B :=
  if n is n'.+1 then f (Fix' n') x
  else Bottom _.

(** Now it is straightforward to package [Fix'] as a computation combinator [Fix]. *)
Lemma Fix'_ok steps n x v n': 
        n <= n' -> Fix' n x steps = Some v -> Fix' n' x steps = Some v.
Proof.
by elim: n n' v x =>//= n IH [|n'] //= v x L /f_cont; apply=>? ?; apply: IH.
Qed.

Hint Resolve Fix'_ok.
Hint Resolve comp_mono.

Definition Fix (x : A): computation B.
exists (fun n => (Fix' n x) n).  
by move=>n v n' E L; move:(comp_mono E L)=> /(Fix'_ok L). 
Defined.

Theorem run_Fix x v:
   run (f Fix x) v -> run (Fix x) v.
Proof. 
case=>n Hn; exists n.+1.
have X: f (Fix' n) x n = Some v by apply:((f_cont Hn) (Fix' n)).
by apply:(comp_mono X (leqnSn n)).
Qed.

End Fix.

Lemma leq_Some  A (x y : A): leq (Some x) (Some y) -> x = y.
Proof. by case/(_ y erefl). Qed.

Lemma leq_None A (x y : A): leq None (Some x) -> False.
Proof. by move/(_ x erefl). Qed.

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

Program Definition mergeSort' A (le: A -> A -> bool): seq A -> computation (seq A) :=
@Fix _ _ (fun (mergeSort : seq A -> computation (seq A)) 
         (ls : list A) =>
          if (length ls) > 1
          then let lss := split ls in
                   ls1 <- mergeSort (fst lss);
                   ls2 <- mergeSort (snd lss);
                   Return (merge le ls1 ls2)
          else Return ls) _.
(* Proving continuity of the argument *)
Next Obligation. 
elim: (length x > 1) H =>//=; rewrite /runTo /Bind /=.
move:(H0 (split x).1); case (v2 (split x).1)=>//=f.
case:(f n)=>//=a Cf /(_ a erefl) ->{f Cf}.
move:(H0 (split x).2); case (v2 (split x).2)=>//=f.
by case:(f n)=>//=b Cf /(_ b erefl) ->. 
Defined.

Definition leb := fun x y => x <= y.

Lemma test_mergeSort' : run (mergeSort' leb (2 :: 1 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
by exists 4.
Qed.

Program Definition looper : bool -> computation unit :=
@Fix _ _ (fun looper (b : bool) =>
    if b then Return tt else looper b) _.
Next Obligation.
case: x H (H0 x)=>// E /(_ v). rewrite -E /runTo=>/(_ erefl) G. 
by rewrite G.
Qed.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.

(***********************************************************************

Lessons learned:
----------------

1. First, we defined basic operations and shoed how to run them within
a liminted number of steps.

2. Then, we defined partial order on partially defined functions and a
notion of continuity (f_cont). 

3. We have shown that thefixed point can be defined for the limited
"fuel" (n) and proved it to be reachable (Lemma Fix'_ok). That is, if
the fixpoint is instantiated with enough fuel, it will terminate.  The
notion of continuity was crucial in order to prove Fix'_ok, which was
later employed for construction of the Fix computation and proving
that it "saturates" for a particular n.

4. The computation wrapper Fix provides exactly the amount of fuel
(which mich or might be not enough for termination). In order to run
the program, we need to provied the amount of fuel by hand.

5. Defining recursive functions amounts to proving continuity of their
arguments.

6. The crux of the development is a well-formed recursive function
Fix' that takes a number of steps to execute. 

7. It is important that the computations are *constructed* by means of
shallow embedding, but not *run*: in order to do it, we need to
provide enough "fuel".

8. Use new constructros instead of the embedded refined time: it
enables coercions and improves your karma and libido.

--------
Homework
--------

- Can it be used in order to implement the fixed-point iteration in
  abstract interpretation? Does one need to construct the termination
  argument?

- How to formulate the questions to the abstract interpreter?


*************************************************************************)














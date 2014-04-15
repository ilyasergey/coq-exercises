Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive maybe (A : Set) (P : A -> Prop) : Set := 
| Unknown : maybe P
| Found   : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)). 
Notation "??" := (@Unknown _ _).
Notation "[| x |]" := (@Found _ _ x _).

Program Definition pred_strong7(n: nat):  {{m | n = m + 1}} :=
 match n return {{m | n = m + 1}} with
  | 0 => ??
  | n'.+1 => [| n' |]
  end.

Next Obligation. by rewrite addn1. Qed.



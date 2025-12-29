Require Import Nat.

Theorem plus1neq0 : forall n: nat,
  (n+1) =? 0 = false.
Proof.
  intros n. 
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - reflexivity.
  Qed.
  
  
Theorem andb_commutative : forall p q: bool,
  andb p q = andb q p.
Proof.
  intros p q. destruct q eqn:Eq_q.
  - destruct p eqn:Eq_p.
    -- reflexivity.
    -- reflexivity.
  - destruct p eqn:Eq_p.
    -- reflexivity.
    -- reflexivity.
Qed.
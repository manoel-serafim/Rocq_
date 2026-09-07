Theorem add_example : forall n m : nat,
  n = m -> n+n = m+m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.
  
Check mult_n_O.
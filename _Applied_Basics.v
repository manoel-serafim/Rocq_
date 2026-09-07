(* filepath: c:\Users\manoe\Git\Rocq_\_00_Inductive_original.v *)
(* satellite mission modes - mission_critical *)
Module MissionModeAssurance.

Inductive mission_mode : Type :=
  | launch
  | transfer
  | nominal
  | deploy
  | safe_hold
  | reentry.

Definition next_mode (m : mission_mode) : mission_mode :=
  match m with
  | launch => transfer
  | transfer => nominal
  | nominal => deploy
  | deploy => safe_hold
  | safe_hold => reentry
  | reentry => launch
  end.

Fixpoint iterate_next_mode (m : mission_mode) (n : nat) : mission_mode :=
  match n with
  | 0 => m
  | S n' => iterate_next_mode (next_mode m) n'
  end.

Compute next_mode launch.
Compute iterate_next_mode launch 6.

Theorem mission_cycle_6 :
  forall m : mission_mode, iterate_next_mode m 6 = m.
Proof.
  intros m.
  destruct m; simpl; reflexivity.
Qed.

Theorem next_mode_is_deterministic :
  forall m : mission_mode, next_mode m = next_mode m.
Proof.
  intros m.
  reflexivity.
Qed.

End MissionModeAssurance.
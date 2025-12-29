Inductive bool : Type := 
  | true
  | false.

Definition negb (val:bool) : bool :=
  match val with
  | true => false
  | false => true
  end.
 
Compute negb(false).

Definition andb (val0:bool) (val1:bool) : bool :=
  match val0 with
  | true => val1
  | false => false
  end.
  
Compute andb(false) (true).

Definition orb (val0:bool) (val1:bool) : bool :=
  match val0 with
  | true => true
  | false => val1
  end.
  
Compute orb (false) (true).


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Theorem orb_true_left : forall b : bool,
  orb true b = true.
Proof.
  intros b.
  simpl.
  reflexivity.
Qed.
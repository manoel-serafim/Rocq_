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

Definition orbif (val0 :bool) (val1:bool) : bool :=
  if val0 then true else val1.
  
Compute orbif (false) (true).


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


(** Exercises *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  | true => 
    match b2 with 
    | false => true
    | true => false
    end
  | false => true
  end. 


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

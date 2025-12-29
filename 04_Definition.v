Module naturals.

Inductive nat : Type :=
  | O
  | S (n: nat).
  
Definition pred (n: nat) : nat := 
  match n with 
  | O => O
  | S n' => n'
  end. 
  
Compute pred (S (S (S O))).

Fixpoint even (n:nat) : bool :=
  match n with 
  | O => true
  | S O => false
  | S (S j) => even j
  end.
  
Compute even(S (S O)).

Fixpoint add (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Compute add (S(S(S(O)))) (S(S(O))).

Fixpoint mul (n:nat) (m:nat) :nat :=
  match n with 
  | O => O
  | S n' => add (m) (mul (n') (m))
  end.

Compute mul (S(S(S(O)))) (S(S(O))).


Fixpoint sub (n: nat) (m: nat) : nat :=
  match n, m with
  | O , _ => O
  | S _, O => n
  | S j, S k => sub (j) (k)
  end.

Compute sub (S(S(S(O)))) (S(S(O))).

Fixpoint eq (n: nat) (m:nat) : bool :=
  match n, m with
  | O , O => true
  | S _, O => false
  | O , S _ => false
  | S j, S k => eq j k
  end.
  
Compute eq (S(S(O))) (S(S(O))).

Fixpoint eq (n: nat) (m:nat) : bool :=
  match n, m with
  | O , O => true
  | S _, O => false
  | O , S _ => false
  | S j, S k => eq j k
  end.
  
Compute eq (S(S(O))) (S(S(O))).


End naturals.


Module section.
  Definition b : bool := true.
End section.

Definition b: nat := O.

Check section.b.
Check b.

Module TuppleSandbox.
  Inductive bit : Type :=
  | _1
  | _0
  .

  Inductive nibble : Type :=
  | bits (b0 : bit)(b1 : bit)(b2 : bit)(b3 : bit).

  Check bits _0 _1 _1 _1.

  Definition are_zero (nib:nibble) : bool :=
  match nib with 
  | bits _0 _0 _0 _0 => true
  | bits _ _ _ _ => false
  end.
  Definition nib_var : nibble := bits _0 _0 _0 _0.
  Compute are_zero nib_var.

End TuppleSandbox. 


Module NaturalSandbox.
  Inductive nat : Type :=
  | O
  | S (n:nat).

  Definition predecessor (value : nat) : nat :=
  match value with
  | O => O
  | S v => v
  end.
  
  Compute S O.

  Compute predecessor (S(S(S O))).

  Definition minus_two (value: nat) : nat :=
  match value with
  | O => O
  | S O => O
  | S (S v) => v
  end.

  Compute minus_two (S(S(S(O)))).

  Fixpoint even (value : nat) : bool :=
  match value with
  | O => true
  | S O => false
  | (S (S (v))) => even v
  end.

  Compute even (S(S(S(S(O))))).

  Fixpoint plus (val0:nat) (val1:nat):nat :=
  match val0 with
  | O => val1
  | S(v) => S (plus v val1)
  end.

  Compute plus (S(S(S(S(S(O)))))) (S(O)).

  Fixpoint minus (val0:nat) (val1:nat):nat :=
  match val0 with
  | O => O
  | S j => match val1 with
           | O => val0
           | S v => minus j v
           end
  end.

  Compute minus (S(S(S(S(S(S(S(O)))))))) (S(S(S(S(S(S(S(S(O))))))))).

  Fixpoint mult (val0:nat) (val1:nat): nat :=
  match val0 with
  | O => O
  | S n => plus val1 (mult (n) (val1))
  end. 

  Compute mult (S(S(O))) (S(S(S(S(O))))).

  Fixpoint fact (value:nat) : nat :=
  match value with
  | O => S O
  | S n => mult value (fact n)
  end.

  Compute fact (S(S(S(S(O))))).

  Fixpoint pow (base:nat) (exp:nat) : nat :=
  match exp with
  | O => S O
  | S n =>  (mult base (pow base n))
  end.

  Compute pow (S(S(O))) (S(S(O))).

  Example test_factorial1: (fact (S(S(S(O))))) = (S(S(S(S(S(S(O))))))).
  Proof. simpl. reflexivity. Qed.
  Example test_factorial2: (fact (S(S(S(S(S(O))))))) = (mult (S(S(S(S(S(S(S(S(S(S(O))))))))))) (S(S(S(S(S(S(S(S(S(S(S(S(O)))))))))))))).
  Proof. simpl. reflexivity. Qed.

  Fixpoint eq (val0:nat) (val1:nat) : bool :=
  match val0 with
  | O => match val1 with
        | O => true
        | S n => false
        end
  | S v => match val1 with
          | O => false
          | S n => eq v n
          end
  end.

  Compute eq (S(S(S(O)))) (S(S(O))).








    Fixpoint leq (v1:nat) (v2:nat) : bool :=
      match v1 with
      | O => match v2 with 
            | O => true
            | S v => true
            end
      | S vec1 => match v2 with 
                | O => false
                | S vec2 => leq vec1 vec2
                end
      end.

    Compute leq (S(S(S(S(S(S(O))))))) (S(S(S(S(S(S(S(O)))))))).

  
  Fixpoint ltb (v1:nat) (v2:nat) : bool :=
    match v1 with
    | O => match v2 with 
          | O => false
          | S v => true
          end
    | S vec1 => match v2 with 
              | O => false
              | S vec2 => ltb vec1 vec2
              end
    end.


  Example test_ltb1: (ltb (S(S(O))) (S(S(O)))) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb2: (ltb (S(S(O))) (S(S(S(S(O)))))) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb3: (ltb (S(S(S(S(O)))))) (S(S(O))) = false.
  Proof. simpl. reflexivity. Qed.

  


End NaturalSandbox.






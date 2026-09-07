
(** This is a definition of the inductive type day*)
(** Day is defined by its constructors *)
Inductive wk_d_t : Type :=
  | sun : wk_d_t
  | mon : wk_d_t
  | tue : wk_d_t
  | wed : wk_d_t
  | thu : wk_d_t
  | fri : wk_d_t
  | sat : wk_d_t.
 
Definition nx_wk_d(day:wk_d_t) : wk_d_t :=
 match day with
 | sun => mon : wk_d_t
 | mon => tue : wk_d_t
 | tue => wed : wk_d_t
 | wed => thu : wk_d_t
 | thu => fri : wk_d_t
 | fri => sat : wk_d_t
 | sat => sun : wk_d_t
 end.
 
Compute nx_wk_d(mon).

Example test_nxt_wkd:
  (nx_wk_d (nx_wk_d mon)) = wed.
  
Proof. simpl. reflexivity. Qed.
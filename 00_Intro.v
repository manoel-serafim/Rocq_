Inductive wk_d_t : Type :=
  | sun
  | mon
  | tue
  | wed
  | thu
  | fri
  | sat.
 
Definition nx_wk_d(day:wk_d_t) : wk_d_t :=
 match day with
 | sun => mon
 | mon => tue
 | tue => wed
 | wed => thu
 | thu => fri
 | fri => sat
 | sat => sun
 end.
 
Compute nx_wk_d(mon).

Example test_nxt_wkd:
  (nx_wk_d (nx_wk_d mon)) = wed.
  
Proof. simpl. reflexivity. Qed.
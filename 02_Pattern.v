Check true.

Check true : bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.
  
Inductive color : Type :=
  | black
  | white
  | data (p:rgb).
  
Definition mono (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | data _ => false
  end.

Compute mono(data red).


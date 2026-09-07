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

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | data p => match p with
                | red => true
                | green => false
                | blue => false
                end
  end.

Compute mono(data red).
Compute isred(data red).


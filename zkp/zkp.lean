def Rel (w x : Nat) : Prop :=
  w + w = x

#check Rel

structure Commitment where
  t : Nat
structure Challenge where
  c : Nat
structure Response where
  s : Nat

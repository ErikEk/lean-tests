def absSpec (x : Int) : Int :=
  if x < 0 then -x else x

def absImpl (x : Int) : Int :=
  if x < 0 then
    -x
  else
    x

theorem abs_correct (x : Int) :
  absImpl x = absSpec x := by
  unfold absImpl absSpec
  rfl

structure CInt32 where
  val : Fin (2^32)
deriving Repr
def CInt32.add (x y : CInt32) : CInt32 :=
  ⟨x.val + y.val⟩
instance : HAdd CInt32 CInt32 CInt32 where
  hAdd a b := ⟨a.val + b.val⟩
def add_32 (a b : CInt32) : CInt32 := a + b

def x : CInt32 := ⟨5⟩
#eval add_32 x x
#eval (⟨3⟩ : CInt32)
#eval CInt32.mk 4294967295
#eval CInt32.mk 4294967296
#eval CInt32.mk 4294967297
#eval 2^32

/-theorem add_mod {a b : Int32} :
  add_32 a b =
    ((a.val + b.val) mod 2^32)-/

def square (x : Int) : Int :=
  x * x

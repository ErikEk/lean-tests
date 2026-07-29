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
def add_32 (a b : Int32) : Int32 := a + b

#eval add_32 5 4

def square (x : Int) : Int :=
  x * x
theorem square_correct (x : Int) :

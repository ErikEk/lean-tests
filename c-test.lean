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

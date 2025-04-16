-- This module serves as the root of the `Test1` library.
-- Import modules here that should be built as part of the library.
import Test1.Basic

#eval Lean.versionString
#eval 1+1


def m: Nat := 1
def b1: Bool := true

/- com -/
#eval hello

#check b1
#check Nat → Nat
#check Nat →  Nat → Nat
#check Nat × Nat
#check Nat × Nat → Nat
#check (0, 1)
#check (Nat → Nat) → Nat
#check Nat.succ 2
#eval Nat.succ 2 + 1
#eval Nat.add 5 2

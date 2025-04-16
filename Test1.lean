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
#eval (5, 9).2
#eval Nat.add 3 3

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
#check α
#check List
#check Prod

#check fun (x : Nat) => x + 5
#check fun x => x + 5
#eval (fun x : Nat => x + 5) 13
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2
#eval (fun x y => if not y then x + 1 else x + 2) 3 true

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

#eval String.append "s" (String.append "s" "d")
#eval String.append "it is" (if 1 > 2 then "true" else "false")
#check (1-2:Int)
def lean : String := "lean"
#eval lean
def add1 (n: Nat) : Nat := n + 1
#eval add1 2
def maximum (n : Nat) (m: Nat) : Nat := if n > m then n else m
#eval maximum 2 4
#eval maximum 2 3
structure Point where
  x : Float
  y : Float
deriving Repr

#check Point
def origin : Point := { x := 0.0, y := 0.0 }

def origin.x : Float := 1.0
#eval origin

def uporigin : Point := { origin with y := 1.1}
def addPoints (p1 : Point) (p2 : Point) : Point :=
    { x := p1.x + p2.x, y := p1.y + p2.y }
#eval addPoints origin uporigin

def dist (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x) ^ 2.0 + (p1.y - p2.y) ^ 2.0)
#eval dist origin uporigin

#eval "one string".append " another string"
def Point.modifyBoth (f: Float → Float) (p: Point) : Point :=
  { x := f p.x, y := f p.y }

#eval uporigin.modifyBoth Float.floor

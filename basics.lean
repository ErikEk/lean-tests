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

structure RectangularPrism where
  width : Float
  height : Float
  depth : Float
  deriving Repr

def RectangularVolume (r : RectangularPrism) : Float :=
  r.width * r.height * r.depth

def rect : RectangularPrism :=
  { width := 1.0, height := 2.0, depth := 3.0 }

#eval rect
#eval RectangularVolume rect

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 2

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 2

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n+2) => fib n + fib (n + 1)

#eval fib 6


def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

#eval plus 3 2

def mult (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (mult n k')
#eval mult 3 2

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.pred (minus n k')

#eval minus 3 2

/- Needs a proof of termination.
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)

#eval div 10 3 -/

structure PPoint (α : Type) where
  x : α
  y : α
  deriving Repr
def testNat : PPoint Nat := { x := 1, y := 2 }
def testFloat : PPoint Float := { x := 1, y := 2 }
def replaceX (α : Type) (p : PPoint α) (newX : α) : PPoint α :=
  {p with x := newX}
#eval replaceX Nat testNat 3

inductive Sign where
  | pos : Sign
  | neg : Sign
def posOrnegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrnegThree Sign.neg
def listTest : List Nat := [1, 2, 3]
#eval listTest.head?
#eval [].head? (α := Int)
#eval ([] : List Int).head?

/-structure Prod (α : Type) (β : Type) where
  fst : α
  snd: β-/

def fives : String × Int × Nat := ("five", -5, 5)
#eval fives.fst
#eval fives.snd

def PetName : Type := String ⊕ String
def animals : List PetName :=
  [Sum.inl "spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "floo"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
#eval howManyDogs animals

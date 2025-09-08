import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finset.Basic
set_option diagnostics true
open Finset
open BigOperators -- make ∑ and ∏ notation available
#eval Finset.sum (Finset.range 5) (fun i => i)   -- prints 10

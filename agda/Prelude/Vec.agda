module Prelude.Vec where

open import Prelude.Level
open import Prelude.Nat

infixr 5 _::_

----------------------------------------------------------------------
-- Finite tuples
----------------------------------------------------------------------
data Vec {l : Level}(A : Set l) : ℕ → Set l where
  []  : Vec A 0
  _::_ :
    {n : ℕ}
    (x : A)
    (xs : Vec A n)
    → ------------
    Vec A (1+ n)

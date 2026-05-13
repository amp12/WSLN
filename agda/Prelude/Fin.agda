module Prelude.Fin where

open import Prelude.Level
open import Prelude.Nat

----------------------------------------------------------------------
-- Finite sets
----------------------------------------------------------------------
data Fin : ℕ → Set where
  zero :
   {n : ℕ}
   → --------
   Fin (1+ n)
  suc :
    {n : ℕ}
    (i : Fin n)
    → ---------
    Fin (1+ n)

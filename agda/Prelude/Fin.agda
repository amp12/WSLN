module Prelude.Fin where

open import Prelude.Decidable
open import Prelude.Empty
open import Prelude.Identity
open import Prelude.Instance
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

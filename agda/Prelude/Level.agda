module Prelude.Level where

open import Agda.Primitive public

----------------------------------------------------------------------
-- Lifting from one universe to a larger one
----------------------------------------------------------------------
record Lift {l : Level}(l' : Level) (A : Set l) : Set (l ⊔ l') where
  constructor lift
  field lower : A

open Lift public

ℓ₀ : Level
ℓ₀ = lzero

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀

ℓ₂ : Level
ℓ₂ = lsuc ℓ₁

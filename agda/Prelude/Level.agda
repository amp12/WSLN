module Prelude.Level where

open import Agda.Primitive renaming (lzero to ℓ₀; lsuc to ℓ₁+) public

----------------------------------------------------------------------
-- Lifting from one universe to a larger one
----------------------------------------------------------------------
record Lift {l : Level}(l' : Level) (A : Set l) : Set (l ⊔ l') where
  constructor lift
  field lower : A

open Lift public

ℓ₁ : Level
ℓ₁ = ℓ₁+ ℓ₀

ℓ₂ : Level
ℓ₂ = ℓ₁+ ℓ₁

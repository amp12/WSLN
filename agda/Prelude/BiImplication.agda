module Prelude.BiImplication where

open import Prelude.Level
open import Prelude.Product

----------------------------------------------------------------------
-- Propositional bi-implication
----------------------------------------------------------------------
infix 6 _↔_
_↔_ : {l m : Level}(A : Set l)(B : Set m) → Set (l ⊔ m)

A ↔ B = (A → B) ∧ (B → A)

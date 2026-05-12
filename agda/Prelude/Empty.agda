module Prelude.Empty where

open import Prelude.Level
open import Prelude.Identity

----------------------------------------------------------------------
-- Level polymorphic empty type
----------------------------------------------------------------------
data Ø {ℓ : Level} : Set ℓ where

Øelim :
  {ℓ ℓ' : Level}
  {A : Set ℓ'}
  → ------------
  Ø{ℓ} → A

Øelim ()

-- Falsity
⊥ : Set

⊥ = Ø {ℓ₀}

{-# DISPLAY Ø {ℓ₀} = ⊥ #-}

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------
¬ : {l : Level} → Set l → Set l

¬ {l} A = A → Ø{l}

-- ¬↔ :
--   {l : Level}
--   {A B : Set l}
--   (_ : A ↔ B)
--   → -----------
--   ¬ A ↔ ¬ B

-- ((¬↔ e)  $ ¬x) y = ¬x (e °$ y)
-- ((¬↔ e) °$ ¬y) x = ¬y (e  $ x)



-- ⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
-- ⊥-elim ()

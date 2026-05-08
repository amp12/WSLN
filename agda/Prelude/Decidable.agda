module Prelude.Decidable where

open import Prelude.Empty
open import Prelude.Equivalence
open import Prelude.Function
open import Prelude.Identity
open import Prelude.Level
open import Prelude.Notation

----------------------------------------------------------------------
-- Decidable inhabitation
----------------------------------------------------------------------
data Dec {l : Level} (A : Set l) : Set l where
  -- the property that A is inhabited is decidable
  no  : (¬p : ¬ A) → Dec A
  yes : (p : A)    → Dec A

----------------------------------------------------------------------
-- Conditional decidablility
----------------------------------------------------------------------
condDec :
  {l : Level}
  {A B : Set l}
  -- if A implies B
  (_ : A → B)
  -- and B is decidable
  (_ : Dec B)
  -- and A is decidable given B
  (_ : B → Dec A)
  → -------------
  -- then A is decidable
  Dec A

condDec f p g with p
... | no ¬q = no (¬q ∘ f)
... | yes x = g x

----------------------------------------------------------------------
-- Decidability is invariant under propositional equivalence
----------------------------------------------------------------------
Dec↔ :
  {l : Level}
  {A B : Set l}
  (_ : A ↔ B)
  → -----------
  Dec A → Dec B

Dec↔ e p = condDec (e °$_) p (yes ∘ e $_)

----------------------------------------------------------------------
-- Decidable equality
----------------------------------------------------------------------
record hasDecEq {l : Level}(A : Set l) : Set l where
  -- the property that two elements of A are equal is decidable
  infix 4 _≐_
  field _≐_ : (x y : A) → Dec (x ≡ y)

open hasDecEq {{...}} public

{-# DISPLAY hasDecEq._≐_ _ x y = x ≐ y #-}

pattern equ = yes refl

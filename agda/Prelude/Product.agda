module Prelude.Product where

{- Adapted from agda-stdlib/src/Data/Product.agda -}

open import Prelude.Level
open import Prelude.Identity
open import Prelude.Empty

----------------------------------------------------------------------
-- Dependent product
----------------------------------------------------------------------
open import Agda.Builtin.Sigma public
  renaming (Σ to ∑; fst to π₁; snd to π₂)
  hiding (module Σ)

module ∑ = Agda.Builtin.Sigma.Σ
  renaming (fst to π₁; snd to π₂)

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 ∑-syntax

∑-syntax : {l m : Level}(A : Set l) → (A → Set m) → Set (l ⊔ m)
∑-syntax = ∑

syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

{-# DISPLAY ∑-syntax = ∑ #-}

∑i :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  (x : A)
  (y : B x)
  → -------------
  ∑ A B
∑i = _,_

∑ext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (e : x ≡ x')
  (_ : subst B e y ≡ y')
  → --------------------
  ∑i x y ≡ ∑i x' y'
∑ext refl refl = refl

∑ext₂ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (x : A) → B x → Set n}
  {x x' : A}
  {y : B x}
  {y' : B x'}
  {z : C x y}
  {z' : C x' y'}
  (e : x ≡ x')
  (e' : subst B e y ≡ y')
  (_ : tpt B C e e' z ≡ z')
  → ------------------------------
  ∑i x (∑i y z) ≡ ∑i x' (∑i y' z')
∑ext₂ refl refl refl = refl

infix 6 ⟨_,_⟩∑
⟨_,_⟩∑ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : Set n}
  (f : C → A)
  (g : (x : C) → B (f x))
  → ---------------------
  C → ∑ A B

⟨ f , g ⟩∑ x = (f x , g x)

----------------------------------------------------------------------
-- Cartesian product
----------------------------------------------------------------------
infixr 2 _×_

_×_ : {l m : Level}(A : Set l)(B : Set m) → Set (l ⊔ m)
A × B = ∑[ _ ∈ A ] B

----------------------------------------------------------------------
-- Existential quantifier
----------------------------------------------------------------------
∃ : {l m : Level}{A : Set l} → (A → Set m) → Set (l ⊔ m)
∃ = ∑ _

infix 2 ∃-syntax
∃-syntax : {l m : Level}{A : Set l} → (A → Set m) → Set (l ⊔ m)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

{-# DISPLAY ∃-syntax = ∃ #-}

infix 2 ∃₂-syntax
∃₂-syntax :
  {l m : Level}
  {A B : Set l}
  (_ : A → B → Set m)
  → -----------------
  Set (l ⊔ m)
∃₂-syntax P = ∃[ x ] ∃[ y ] P x y

syntax ∃₂-syntax (λ x y → P) = ∃[ x , y ] P

infix 2 ∃₃-syntax
∃₃-syntax :
  {l m : Level}
  {A B C : Set l}
  (_ : A → B → C → Set m)
  → -----------------
  Set (l ⊔ m)
∃₃-syntax P = ∃[ x ] ∃[ y ] ∃[ z ] P x y z

syntax ∃₃-syntax (λ x y z → P) = ∃[ x , y , z ] P

infix 2 ∃₄-syntax
∃₄-syntax :
  {l m : Level}
  {A B C D : Set l}
  (_ : A → B → C → D → Set m)
  → -------------------------
  Set (l ⊔ m)
∃₄-syntax P = ∃[ x ] ∃[ y ] ∃[ z ] ∃[ w ] P x y z w

syntax ∃₄-syntax (λ x y z w → P) = ∃[ x , y , z , w ] P

infix 2 ∃₅-syntax
∃₅-syntax :
  {l m : Level}
  {A B C D E : Set l}
  (_ : A → B → C → D → E → Set m)
  → -----------------------------
  Set (l ⊔ m)
∃₅-syntax P = ∃[ x ] ∃[ y ] ∃[ z ] ∃[ w ] ∃[ v ] P x y z w v

syntax ∃₅-syntax (λ x y z w v → P) = ∃[ x , y , z , w , v ] P

----------------------------------------------------------------------
-- Conjunction
----------------------------------------------------------------------
infixr 2 _∧_

_∧_ : {l m : Level}(A : Set l)(B : Set m) → Set (l ⊔ m)
_∧_ = _×_

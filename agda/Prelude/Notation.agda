module Prelude.Notation where

open import Prelude.Level

----------------------------------------------------------------------
-- Notation for membership relations
----------------------------------------------------------------------
record Member
  {l m : Level}
  (A : Set l)
  (B : Set m)
  : --------------
  Set (ℓ₁+(l ⊔ m))
  where
  constructor mkMember
  infix 4 _∈_ _∉_
  field
    _∈_ : A → B → Set (l ⊔ m)
    _∉_ : A → B → Set (l ⊔ m)

open Member ⦃ ... ⦄ public

{-# DISPLAY Member._∈_ _ x S = x ∈ S #-}
{-# DISPLAY Member._∉_ _ x S = x ∉ S #-}

---------------------------------------------------------------------
-- Notation for not equals
----------------------------------------------------------------------
record NotEq {l : Level}(A : Set l) : Set (ℓ₁+ l) where
  constructor mkNotEq
  infix 4 _≠_
  field
    _≠_ : A → A → Set l

open NotEq ⦃ ... ⦄ public

{-# DISPLAY NotEq._≠_ _ x y = x ≠ y #-}

----------------------------------------------------------------------
-- Notation for binary operations
----------------------------------------------------------------------
record Apply
  {l m n : Level}
  (A : Set l)
  (B : Set m)
  (C : Set n)
  : -------------
  Set (l ⊔ m ⊔ n)
  where
  constructor mkApply
  infixr 6 _*_
  field
    _*_ : A → B → C

open Apply ⦃ ... ⦄ public

{-# DISPLAY Apply._*_ _ a b = a * b #-}

----------------------------------------------------------------------
-- Notation for composition operations
----------------------------------------------------------------------
record Composition
  {l m n : Level}
  (A : Set l)
  (B : Set m)
  (C : Set n)
  : -------------
  Set (l ⊔ m ⊔ n)
  where
  infixr 5 _∘_
  field
    _∘_ : A → B → C

open Composition ⦃ ... ⦄ public

{-# DISPLAY Composition._∘_ _ g f = g ∘ f #-}

----------------------------------------------------------------------
-- Notation for identity elements
----------------------------------------------------------------------
record Identity {l : Level}(A : Set l) : Set l where
  field
    id : A

open Identity ⦃ ... ⦄ public

{-# DISPLAY Identity.id _ = id #-}

----------------------------------------------------------------------
-- Notation for updating functions
----------------------------------------------------------------------
record UpdateFun {l m : Level}(A : Set l)(V : Set m) : Set (l ⊔ m)
  where
  infix 5 _∘/_:=_
  infix 6 _:=_
  field
    _∘/_:=_ : (A → V) → A → V → A → V

  _:=_ : A → V → ⦃ _ : Identity (A → V) ⦄ → A → V
  (x := v) = id ∘/ x := v

open UpdateFun ⦃ ... ⦄ public

{-# DISPLAY UpdateFun._∘/_:=_ _ f x v = f ∘/ x := v #-}
{-# DISPLAY UpdateFun._:=_    _ x v   = x := v      #-}

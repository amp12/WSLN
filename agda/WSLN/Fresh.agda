module WSLN.Fresh where

open import Prelude

open import WSLN.Index
open import WSLN.Atom

----------------------------------------------------------------------
-- Finite support structure
----------------------------------------------------------------------
record FiniteSupport (A : Set) : Set where
  infix 4 _#_
  field
    supp : A → Fset𝔸

  --Derived freshness relation
  _#_ : 𝔸 → A → Set
  x # a = x ∉ supp a

open FiniteSupport ⦃ ... ⦄ public

{-# DISPLAY FiniteSupport.supp _ a = supp a #-}

----------------------------------------------------------------------
-- Fresh atoms
----------------------------------------------------------------------
fresh :
  {A : Set}
  ⦃ _ : FiniteSupport A ⦄
  (a : A)
  → ---------------------
  ∃[ x ] (x # a)

fresh a = (new (supp a) , new∉ (supp a))

----------------------------------------------------------------------
-- Decidability of the freshness relation
----------------------------------------------------------------------
#? :
 {A : Set}
 ⦃ _ : FiniteSupport A ⦄
 (x : 𝔸)
 (a : A)
 → ---------------------
 Dec (x # a)

#? x a = dec∉ x (supp a)

----------------------------------------------------------------------
-- Freshness is a proposition
----------------------------------------------------------------------
instance
  isProp# :
    {A : Set}
    ⦃ _ : FiniteSupport A ⦄
    {x : 𝔸}
    {a : A}
    → ---------------------
    isProp (x # a)
  ! ⦃ isProp# ⦄ p q = ! ⦃ isProp∉ ⦄ p q

----------------------------------------------------------------------
-- Finite support for atoms and finite sets of atoms
----------------------------------------------------------------------
instance
  FiniteSupport𝔸 : FiniteSupport 𝔸
  supp ⦃ FiniteSupport𝔸 ⦄ x = ｛ x ｝

  FiniteSupportFset𝔸 : FiniteSupport (Fset𝔸)
  supp ⦃ FiniteSupportFset𝔸 ⦄ xs = xs

#symm :
  {x y : 𝔸}
  → -----------
  x # y → y # x

#symm (∉｛｝ p) = ∉｛｝ (≠𝔸symm p)

----------------------------------------------------------------------
-- Finite support for indices
----------------------------------------------------------------------
instance
  FiniteSupportFin : ∀{n} → FiniteSupport (Fin n)

  supp ⦃ FiniteSupportFin ⦄ i = ∅

----------------------------------------------------------------------
-- Finite support for cartesian products
----------------------------------------------------------------------
instance
  FiniteSupport× :
    {A B : Set}
    ⦃ _ : FiniteSupport A ⦄
    ⦃ _ : FiniteSupport B ⦄
    → ---------------------
    FiniteSupport (A × B)

  supp ⦃ FiniteSupport× ⦄ (a , b) = supp a ∪ supp b

----------------------------------------------------------------------
-- Finite support for lists
----------------------------------------------------------------------
module _ {A : Set}⦃ _ : FiniteSupport A ⦄ where
  suppList : List A → Fset𝔸

  suppList []        = ∅
  suppList (a :: as) = supp a ∪ suppList as

  instance
    FiniteSupportList : FiniteSupport (List A)
    supp ⦃ FiniteSupportList ⦄ = suppList

{-# DISPLAY suppList xs = supp xs #-}

----------------------------------------------------------------------
-- Finite support for vectors
----------------------------------------------------------------------
module _ {A : Set}⦃ _ : FiniteSupport A ⦄ where
  suppVec : ∀{n} → Vec A n → Fset𝔸

  suppVec [] = ∅
  suppVec (x :: xs) = supp x ∪ suppVec xs

  instance
    FiniteSupportVec : ∀ {n} → FiniteSupport (Vec A n)
    supp ⦃ FiniteSupportVec ⦄ = suppVec

{-# DISPLAY suppVec xs = supp xs #-}

----------------------------------------------------------------------
-- Freshness for tuples of mutually distinct atoms
----------------------------------------------------------------------
infix 4 distinct_∉_
data distinct_∉_ : ∀{n} → Vec 𝔸 n → Fset𝔸 → Set where
  -- Cf. A. Charguéraud, "The Locally Nameless Respesentation",
  -- J. Autom. Reasoning 49(2012) section 7.1
  ##◇ :
    {S : Fset𝔸}
    → -------------
    distinct [] ∉ S
  ##:: :
    {n : ℕ}
    {xs : Vec 𝔸 n}
    {x : 𝔸}
    {S : Fset𝔸}
    (x∉S : x ∉ S)
    (xs∉xS : distinct xs ∉ ｛ x ｝ ∪ S)
    → --------------------------------
    distinct x :: xs ∉ S

distinct｛｝ :
  {n : ℕ}
  {xs : Vec 𝔸 n}
  {x : 𝔸}
  (_ : distinct xs ∉ ｛ x ｝)
  → ------------------------
  x # xs
distinct⊆ :
  {n : ℕ}
  {xs : Vec 𝔸 n}
  {S S' : Fset𝔸}
  (_ : distinct xs ∉ S')
  (_ : S ⊆ S')
  → --------------------
  distinct xs ∉ S

distinct｛｝ ##◇ = ∉∅
distinct｛｝{x = x} (##::{x = x'} (∉｛｝ p) p') =
  (∉｛｝ (≠𝔸symm p)) ∉∪ (distinct｛｝ (distinct⊆ p' ∈∪₂))

distinct⊆ ##◇ _ = ##◇
distinct⊆ (##:: p p') q =
  ##:: (⊆∉ q p) (distinct⊆ p' (∪⊆ id q))

distinct::₁ :
  {n : ℕ}
  {xs : Vec 𝔸 n}
  {x : 𝔸}
  {S : Fset𝔸}
  (_ : distinct x :: xs ∉ S)
  → -----------------------
  distinct xs ∉ S

distinct::₁ (##:: _ p) = distinct⊆ p ∈∪₂

distinct::₂ :
  {n : ℕ}
  {xs : Vec 𝔸 n}
  {x : 𝔸}
  {S : Fset𝔸}
  (_ : distinct x :: xs ∉ S)
  → -----------------------
  x ∉ S

distinct::₂ (##:: p _) = p

distinct::₃ :
  {n : ℕ}
  {xs : Vec 𝔸 n}
  {x : 𝔸}
  {S : Fset𝔸}
  (_ : distinct x :: xs ∉ S)
  → -----------------------
  x # xs

distinct::₃ {xs = []} _ = ∉∅
distinct::₃ {xs = x :: xs} (##:: p p') =
  distinct｛｝ (distinct⊆ p' ∈∪₁)

-- Derived freshness relation for finitely supported types
module _  {A : Set}⦃ _ : FiniteSupport A ⦄ where
  infix 4 _##_
  _##_ : ∀{n} → Vec 𝔸 n → A → Set
  xs ## a = distinct xs ∉ supp a

  infix 4 _#_#_
  _#_#_ : 𝔸 → 𝔸 → A → Set
  x # y # a = y :: x :: [] ## a

  infix 4 _#_#_#_
  _#_#_#_ : 𝔸 → 𝔸 → 𝔸 → A → Set
  x # y # z # a = z :: y :: x :: [] ## a

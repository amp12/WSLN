module ETT.Judgement where

open import Function
open import Identity
open import Nat
open import Notation

open import WSLN

open import ETT.Syntax

----------------------------------------------------------------------
-- Forms of judgement
----------------------------------------------------------------------
infix 4
  _⦂_
  _∶_⦂_
  _＝_⦂_
  _＝_∶_⦂_
data Jg : Set where
  -- well-formed type of given level
  _⦂_ : Ty → Lvl → Jg
  -- well-formed term of given type and level
  _∶_⦂_ : (a : Tm)(A : Ty)(l : Lvl)    → Jg
  -- conversion between types of given level
  _＝_⦂_ : Ty → Ty → Lvl → Jg
  -- conversion between terms of given type and level
  _＝_∶_⦂_ : (a a' : Tm)(A : Ty)(l : Lvl) → Jg

----------------------------------------------------------------------
-- Support of judgements
----------------------------------------------------------------------
instance
  FiniteSupportJg : FiniteSupport Jg
  supp ⦃ FiniteSupportJg ⦄ (A ⦂ _) = supp A
  supp ⦃ FiniteSupportJg ⦄ (a ∶ A ⦂ _) = supp a ∪ supp A
  supp ⦃ FiniteSupportJg ⦄ (A ＝ A' ⦂ _) = supp A ∪ supp A'
  supp ⦃ FiniteSupportJg ⦄ (a ＝ a' ∶ A ⦂ _) = supp a ∪ supp a' ∪ supp A

----------------------------------------------------------------------
-- Action of substitutions on judgements
----------------------------------------------------------------------
actSbJg : Sb → Jg → Jg
actSbJg σ (A ⦂ l) = σ * A ⦂ l
actSbJg σ (a ∶ A ⦂ l) = σ * a ∶ σ * A ⦂ l
actSbJg σ (A ＝ A' ⦂ l) = σ * A ＝ σ * A' ⦂ l
actSbJg σ (a ＝ a' ∶ A ⦂ l) = σ * a ＝ σ * a' ∶ σ * A ⦂ l

instance
  ActSbJg : Apply Sb Jg Jg
  _*_ ⦃ ActSbJg ⦄ = actSbJg
  ActRnJg : Apply Rn Jg Jg
  _*_ ⦃ ActRnJg ⦄ ρ J = 𝐬 ρ * J

jgRespSupp :
  (σ σ' : Sb)
  (J : Jg)
  (_ : ∀ x → x ∈ supp J → σ x ≡ σ' x)
  → ---------------------------------
  σ * J ≡ σ' * J

jgRespSupp σ σ' (A ⦂ _) e
  rewrite sbRespSupp σ σ' A (λ _ p → e _ p) = refl
jgRespSupp σ σ' (a ∶ A ⦂ _) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (A ＝ A' ⦂ _) e
  rewrite sbRespSupp σ σ' A (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A' (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (a ＝ a' ∶ A  ⦂ _) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' a' (λ _ p → e _ (∈∪₂ (∈∪₁ p)))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ (∈∪₂ p))) = refl

sbUnitJg :
  (J : Jg)
  → -------
  ι * J ≡ J

sbUnitJg (A ⦂ _)
  rewrite sbUnit A = refl
sbUnitJg (a ∶ A ⦂ _)
  rewrite sbUnit a
  | sbUnit A = refl
sbUnitJg (A ＝ A' ⦂ _)
  rewrite sbUnit A
  | sbUnit A' = refl
sbUnitJg (a ＝ a' ∶ A ⦂ _)
  rewrite sbUnit a
  | sbUnit a'
  | sbUnit A = refl

rnUnitJg :
  (J : Jg)
  → -------
  id * J ≡ J

rnUnitJg = sbUnitJg

----------------------------------------------------------------------
-- Operations on judgements
----------------------------------------------------------------------
ty₁ : Jg → Jg

ty₁ (A ⦂ l)         = A ⦂ l
ty₁ (a ∶ A ⦂ l)      = a ∶ A ⦂ l
ty₁ (A ＝ _ ⦂ l)    = A ⦂ l
ty₁ (a ＝ _ ∶ A ⦂ l) = a ∶ A ⦂ l

ty₂ : Jg → Jg

ty₂ (A ⦂ l)         = A ⦂ l
ty₂ (a ∶ A ⦂ l)      = a ∶ A ⦂ l
ty₂ (_ ＝ A ⦂ l)    = A ⦂ l
ty₂ (_ ＝ a ∶ A ⦂ l) = a ∶ A ⦂ l

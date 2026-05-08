module MLTT.Judgement where

open import Function
open import Identity
open import Nat
open import Notation

open import WSLN

open import MLTT.Syntax

----------------------------------------------------------------------
-- Forms of judgement
----------------------------------------------------------------------
infix 4
  _∶[_]_
  _＝_∶[_]_
data Jg : Set where
  -- well-formed term of given level and type
  _∶[_]_    : (a : Tm)(ℓ : Lvl)(A : Ty)    → Jg
  -- convertible terms of given level and type
  _＝_∶[_]_ : (a a' : Tm)(ℓ : Lvl)(A : Ty) → Jg

infix 4 _∶𝐒𝐞𝐭_
_∶𝐒𝐞𝐭_ : Tm → Lvl → Jg
a ∶𝐒𝐞𝐭 ℓ = a ∶[ 1+ ℓ ] 𝐒𝐞𝐭 ℓ

infix 4 _＝_∶𝐒𝐞𝐭_
_＝_∶𝐒𝐞𝐭_ : Tm → Tm → Lvl → Jg
a ＝ a' ∶𝐒𝐞𝐭 ℓ = a ＝ a' ∶[ 1+ ℓ ] 𝐒𝐞𝐭 ℓ

----------------------------------------------------------------------
-- Support of judgements
----------------------------------------------------------------------
instance
  FiniteSupportJg : FiniteSupport Jg
  supp ⦃ FiniteSupportJg ⦄ (a ∶[ _ ] A) =
    supp a ∪ supp A
  supp ⦃ FiniteSupportJg ⦄ (a ＝ a' ∶[ _ ] A) =
    supp a ∪ supp a' ∪ supp A

----------------------------------------------------------------------
-- Action of substitutions on judgements
----------------------------------------------------------------------
actSbJg : Sb → Jg → Jg
actSbJg σ (a ∶[ ℓ ] A) = σ * a ∶[ ℓ ] σ * A
actSbJg σ (a ＝ a' ∶[ ℓ ] A) = σ * a ＝ σ * a' ∶[ ℓ ] σ * A

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

jgRespSupp σ σ' (a ∶[ _ ] A) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (a ＝ a' ∶[ _ ] A) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' a' (λ _ p → e _ (∈∪₂ (∈∪₁ p)))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ (∈∪₂ p))) = refl

sbUnitJg :
  (J : Jg)
  → -------
  ι * J ≡ J

sbUnitJg (a ∶[ _ ] A)
  rewrite sbUnit a
  | sbUnit A = refl
sbUnitJg (a ＝ a' ∶[ _ ] A)
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

ty₁ (a ∶[ ℓ ] A)      = a ∶[ ℓ ] A
ty₁ (a ＝ _ ∶[ ℓ ] A) = a ∶[ ℓ ] A

ty₂ : Jg → Jg

ty₂ (a ∶[ ℓ ] A)      = a ∶[ ℓ ] A
ty₂ (_ ＝ a ∶[ ℓ ] A) = a ∶[ ℓ ] A

module MLTTcuml.Judgement where

open import Function
open import Identity
open import Notation

open import WSLN

open import MLTTcuml.Syntax

----------------------------------------------------------------------
-- Forms of judgement
----------------------------------------------------------------------
infix 4
  _ty
  _＝_ty
  _∶_
  _＝_∶_
data Jg : Set where
  _ty    : (A : Ty) → Jg             -- well-formed type
  _＝_ty : (A A' : Ty) → Jg          -- type conversion
  _∶_     : (a : Tm)(A : Ty)    → Jg -- well-formed term
  _＝_∶_  : (a a' : Tm)(A : Ty) → Jg -- term conversion

----------------------------------------------------------------------
-- Support of judgements
----------------------------------------------------------------------
instance
  FiniteSupportJg : FiniteSupport Jg
  supp ⦃ FiniteSupportJg ⦄ (A ty) = supp A
  supp ⦃ FiniteSupportJg ⦄ (A ＝ A' ty) = supp A ∪ supp A'
  supp ⦃ FiniteSupportJg ⦄ (a ∶ A) = supp a ∪ supp A
  supp ⦃ FiniteSupportJg ⦄ (a ＝ a' ∶ A) = supp a ∪ supp a' ∪ supp A

----------------------------------------------------------------------
-- Action of substitutions on judgements
----------------------------------------------------------------------
actSbJg : Sb → Jg → Jg
actSbJg σ (A ty) = σ * A ty
actSbJg σ (A ＝ A' ty) =  σ * A ＝ σ * A' ty
actSbJg σ (a ∶ A) = σ * a ∶ σ * A
actSbJg σ (a ＝ a' ∶ A) = σ * a ＝ σ * a' ∶ σ * A

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

jgRespSupp σ σ' (A ty) e
  rewrite sbRespSupp σ σ' A e = refl
jgRespSupp σ σ' (A ＝ A' ty) e
  rewrite sbRespSupp σ σ' A (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A' (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (a ∶ A) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (a ＝ a' ∶ A) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' a' (λ _ p → e _ (∈∪₂ (∈∪₁ p)))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ (∈∪₂ p))) = refl

sbUnitJg :
  (J : Jg)
  → -------
  ι * J ≡ J

sbUnitJg (A ty)
  rewrite sbUnit A = refl
sbUnitJg (A ＝ A' ty)
  rewrite sbUnit A
  | sbUnit A' = refl
sbUnitJg (a ∶ A)
  rewrite sbUnit a
  | sbUnit A = refl
sbUnitJg (a ＝ a' ∶ A)
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
ty₁ (A ty)      = A ty
ty₁ (A ＝ _ ty) = A ty
ty₁ (a ∶ A)      = a ∶ A
ty₁ (a ＝ _ ∶ A) = a ∶ A

ty₂ : Jg → Jg
ty₂ (A ty)      = A ty
ty₂ (_ ＝ A ty) = A ty
ty₂ (a ∶ A)      = a ∶ A
ty₂ (_ ＝ a ∶ A) = a ∶ A

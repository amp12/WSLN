module MLTT1.Judgement where

open import Function
open import Identity
open import Nat
open import Notation

open import WSLN

open import MLTT1.Syntax

----------------------------------------------------------------------
-- Forms of judgement
----------------------------------------------------------------------
infix 4
  _∶_∶_
  _＝_∶_∶_
data Jg : Set where
  -- well-formed term of given type and level
  _∶_∶_     : (a : Tm)(A : Ty)(l : Lvl)    → Jg
  -- conversion between terms of given type and level
  _＝_∶_∶_  : (a a' : Tm)(A : Ty)(l : Lvl) → Jg

infix 4 _∶𝐔_ _＝_∶𝐔_
_∶𝐔_ : Ty → Lvl → Jg
(A ∶𝐔 l) = A ∶ 𝐔 l ∶ 1+ l

_＝_∶𝐔_ : Ty → Ty → Lvl → Jg
(A ＝ A' ∶𝐔 l) = A ＝ A' ∶ 𝐔 l ∶ 1+ l

----------------------------------------------------------------------
-- Support of judgements
----------------------------------------------------------------------
instance
  FiniteSupportJg : FiniteSupport Jg
  supp ⦃ FiniteSupportJg ⦄ (a ∶ A ∶ _) = supp a ∪ supp A
  supp ⦃ FiniteSupportJg ⦄ (a ＝ a' ∶ A ∶ _) = supp a ∪ supp a' ∪ supp A

----------------------------------------------------------------------
-- Action of substitutions on judgements
----------------------------------------------------------------------
actSbJg : Sb → Jg → Jg
actSbJg σ (a ∶ A ∶ l) = σ * a ∶ σ * A ∶ l
actSbJg σ (a ＝ a' ∶ A ∶ l) = σ * a ＝ σ * a' ∶ σ * A ∶ l

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

jgRespSupp σ σ' (a ∶ A ∶ _) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ p)) = refl
jgRespSupp σ σ' (a ＝ a' ∶ A  ∶ _) e
  rewrite sbRespSupp σ σ' a (λ _ p → e _ (∈∪₁ p))
  | sbRespSupp σ σ' a' (λ _ p → e _ (∈∪₂ (∈∪₁ p)))
  | sbRespSupp σ σ' A (λ _ p → e _ (∈∪₂ (∈∪₂ p))) = refl

sbUnitJg :
  (J : Jg)
  → -------
  ι * J ≡ J

sbUnitJg (a ∶ A ∶ _)
  rewrite sbUnit a
  | sbUnit A = refl
sbUnitJg (a ＝ a' ∶ A ∶ _)
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

ty₁ (a ∶ A ∶ l)      = a ∶ A ∶ l
ty₁ (a ＝ _ ∶ A ∶ l) = a ∶ A ∶ l

ty₂ : Jg → Jg

ty₂ (a ∶ A ∶ l)      = a ∶ A ∶ l
ty₂ (_ ＝ a ∶ A ∶ l) = a ∶ A ∶ l

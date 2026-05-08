module MLTTcuml.ContextConversion where

open import WSLN

open import MLTTcuml.Syntax
open import MLTTcuml.Judgement
open import MLTTcuml.TypeSystem

----------------------------------------------------------------------
-- Context conversion
----------------------------------------------------------------------
open MLTT⁺
infix 4 ⊢_＝_
data ⊢_＝_ : (Γ Γ' : Cx) → Set where
  ◇ : ⊢ ◇ ＝ ◇
  ∷ :
    {Γ Γ' : Cx}
    {A A' : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : x # Γ' ⦄
    (q₀ : ⊢ Γ ＝ Γ')
    (q₁ : Γ ⊢ A ＝ A' ty)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ty)
    (h₁ : Γ' ⊢ A' ty)
    → ----------------------------
    ⊢ (Γ ⸴ x ∶ A) ＝ (Γ' ⸴ x ∶ A')

CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇ = ◇
CxRefl (∷ q q') = ∷ (CxRefl q') (TyRefl q) q q

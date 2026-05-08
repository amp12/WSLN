module MLTT.ContextConversion where

open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem

----------------------------------------------------------------------
-- Context conversion
----------------------------------------------------------------------
open MLTT⁺
infix 4 ⊢_＝_
data ⊢_＝_ : (Γ Γ' : Cx) → Set where
  ◇ : ⊢ ◇ ＝ ◇
  ∷ :
    {ℓ : Lvl}
    {Γ Γ' : Cx}
    {A A' : Ty}
    {ℓ : Lvl}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : x # Γ' ⦄
    (q₀ : ⊢ Γ ＝ Γ')
    (q₁ : Γ ⊢ A ＝ A' ∶𝐒𝐞𝐭 ℓ)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐒𝐞𝐭 ℓ)
    (h₁ : Γ' ⊢ A' ∶𝐒𝐞𝐭 ℓ)
    → --------------------------------------
    ⊢ (Γ ⸴ x ∶[ ℓ ] A) ＝ (Γ' ⸴ x ∶[ ℓ ] A')

CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇ = ◇
CxRefl (∷ q q') = ∷ (CxRefl q') (Refl q) q q

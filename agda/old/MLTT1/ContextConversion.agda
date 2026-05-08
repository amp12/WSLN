module MLTT1.ContextConversion where

open import WSLN

open import MLTT1.Syntax
open import MLTT1.Judgement
open import MLTT1.TypeSystem

----------------------------------------------------------------------
-- Context conversion
----------------------------------------------------------------------
infix 4 ⊢_＝_
data ⊢_＝_ : (Γ Γ' : Cx) → Set where
  ◇ : ⊢ ◇ ＝ ◇
  ∷ :
    {l : Lvl}
    {Γ Γ' : Cx}
    {A A' : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : x # Γ' ⦄
    (q₀ : ⊢ Γ ＝ Γ')
    (q₁ : Γ ⊢ A ＝ A' ∶𝐔 l)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ' ⊢ A' ∶𝐔 l)
    → ------------------------------------
    ⊢ (Γ ⸴ x ∶ A ∶ l) ＝ (Γ' ⸴ x ∶ A' ∶ l)

CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇ = ◇
CxRefl (∷ q q') = ∷ (CxRefl q') (Refl q) q q

{- Symmetry and transitivity for context conversion are proved later,
in MLTT1.UniqueTypes. -}

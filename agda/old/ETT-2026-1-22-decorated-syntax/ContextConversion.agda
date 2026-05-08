module ETT.ContextConversion where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem

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
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : Γ' ⊢ A' ⦂ l)
    → ------------------------------------
    ⊢ (Γ ⸴ x ∶ A ⦂ l) ＝ (Γ' ⸴ x ∶ A' ⦂ l)

CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇ = ◇
CxRefl (∷ q q') = ∷ (CxRefl q') (TyRefl q) q q

{- Symmetry and transitivity for context conversion are proved later,
in MLTT.UniqueTypes. -}

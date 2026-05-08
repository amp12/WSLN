module ETT.Sized.ContextConversion where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.Sized.TypeSystem
open import ETT.Sized.Ok

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
    → ------------------------------------
    ⊢ (Γ ⸴ x ∶ A ⦂ l) ＝ (Γ' ⸴ x ∶ A' ⦂ l)

CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇     = ◇
CxRefl (∷ q) = ∷ (CxRefl (⊢ok q)) (TyRefl q)

{- Symmetry and transitivity for context conversion are proved later,
in MLTT.Sized.UniqueTypes. -}

module MLTT.Ok where

open import Identity
open import Product

open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem
open import MLTT.ContextConversion

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Provable judgements have well-formed contexts
----------------------------------------------------------------------
⊢ok :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → ---------
  Ok Γ

⊢ok (⊢conv q _) = ⊢ok q
⊢ok (⊢𝐯 q _) = q
⊢ok (⊢𝐔 q) = q
⊢ok (⊢𝚷 q _ _) = ⊢ok q
⊢ok (⊢𝛌 q _ _ _) with ∷ _ q' ← ⊢ok q = q'
⊢ok (⊢∙ q _ _ _ _) = ⊢ok q
⊢ok (⊢𝐈𝐝 q _ _) = ⊢ok q
⊢ok (⊢𝐫𝐞𝐟𝐥 q _) = ⊢ok q
⊢ok (⊢𝐉 _ q _ _ _ _ _ _ _) = ⊢ok q
⊢ok (⊢𝐍𝐚𝐭 q) = q
⊢ok (⊢𝐳𝐞𝐫𝐨 q) = q
⊢ok (⊢𝐬𝐮𝐜𝐜 q) = ⊢ok q
⊢ok (⊢𝐧𝐫𝐞𝐜 q _ _ _ _ _) = ⊢ok q
⊢ok (Refl q) = ⊢ok q
⊢ok (Symm q) = ⊢ok q
⊢ok (Trans q _) = ⊢ok q
⊢ok (＝conv q _) = ⊢ok q
⊢ok (𝚷Cong q _ _ _) = ⊢ok q
⊢ok (𝛌Cong q _ _ _ _) = ⊢ok q
⊢ok (∙Cong q _ _ _ _ _ _) = ⊢ok q
⊢ok (𝐈𝐝Cong q _ _) = ⊢ok q
⊢ok (𝐫𝐞𝐟𝐥Cong q _) = ⊢ok q
⊢ok (𝐉Cong _ q _ _ _ _ _ _ _) = ⊢ok q
⊢ok (𝐬𝐮𝐜𝐜Cong q) = ⊢ok q
⊢ok (𝐧𝐫𝐞𝐜Cong _ q _ _ _ _ _) = ⊢ok q
⊢ok (𝚷Beta _ q _ _ _) = ⊢ok q
⊢ok (𝐈𝐝Beta _ q _ _ _ _ _) = ⊢ok q
⊢ok (𝐍𝐚𝐭Beta₀ q _ _ _ _) = ⊢ok q
⊢ok (𝐍𝐚𝐭Beta₊ q _ _ _ _ _) = ⊢ok q
⊢ok (𝚷Eta q _ _) = ⊢ok q

ok＝ :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  Ok Γ

ok＝ ◇ = ◇
ok＝ (∷ q _ h _) = ∷ h (ok＝ q)

＝ok :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  Ok Γ'

＝ok ◇ = ◇
＝ok (∷ q _ _ h) = ∷ h (＝ok q)

----------------------------------------------------------------------
-- Context inversion
----------------------------------------------------------------------
∷⁻¹ :
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  {J : Jg}
  (_ : Γ ⸴ x ∶ A ⊢ J)
  → --------------------------------
  (∑[ ℓ ∈ Lvl ] Γ ⊢ A ∶ 𝐒𝐞𝐭 ℓ) ∧ Ok Γ

∷⁻¹ q
  -- helper hypothesis used here
  with ∷ q' h ← ⊢ok q = ((_ , q') , h)

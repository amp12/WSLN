module ETT.Ok where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem
open import ETT.ContextConversion

----------------------------------------------------------------------
-- Provable judgements have well-formed contexts
----------------------------------------------------------------------
⊢ok :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → ---------
  Ok Γ

⊢ok (⊢𝐔 q) = q
⊢ok (⊢𝚷 q _ _) = ⊢ok q
⊢ok (⊢𝐈𝐝 q _ _) = ⊢ok q
⊢ok (⊢𝐍𝐚𝐭 q) = q
⊢ok (Tm→Ty q) = ⊢ok q
⊢ok (⊢conv q _) = ⊢ok q
⊢ok (⊢𝐯 q _) = q
⊢ok (Ty→Tm q) = ⊢ok q
⊢ok (⊢𝛌 _ _ h _) = ⊢ok h
⊢ok (⊢∙ q _ _ _ _) = ⊢ok q
⊢ok (⊢𝐫𝐞𝐟𝐥 q _) = ⊢ok q
⊢ok (⊢𝐳𝐞𝐫𝐨 q) = q
⊢ok (⊢𝐬𝐮𝐜𝐜 q) = ⊢ok q
⊢ok (⊢𝐧𝐫𝐞𝐜 q _ _ _ _ _) = ⊢ok q
⊢ok (TyRefl q) = ⊢ok q
⊢ok (TySymm q) = ⊢ok q
⊢ok (TyTrans q _) = ⊢ok q
⊢ok (𝚷Cong q _ _ _) = ⊢ok q
⊢ok (𝐈𝐝Cong q _ _) = ⊢ok q
⊢ok (=Tm→Ty q) = ⊢ok q
⊢ok (TmRefl q) = ⊢ok q
⊢ok (TmSymm q) = ⊢ok q
⊢ok (TmTrans q _) = ⊢ok q
⊢ok (＝conv q _) = ⊢ok q
⊢ok (=Ty→Tm q) = ⊢ok q
⊢ok (⊢Reflect q _ _ _) = ⊢ok q
⊢ok (𝛌Cong _ _ h _) = ⊢ok h
⊢ok (∙Cong q _ _ _ _) = ⊢ok q
⊢ok (𝐬𝐮𝐜𝐜Cong q) = ⊢ok q
⊢ok (𝐧𝐫𝐞𝐜Cong _ q _ _ _ _ _) = ⊢ok q
⊢ok (𝚷Beta _ q _ _ _) = ⊢ok q
⊢ok (𝐍𝐚𝐭Beta₀ q _ _ _ _) = ⊢ok q
⊢ok (𝐍𝐚𝐭Beta₊ q _ _ _ _ _) = ⊢ok q
⊢ok (𝚷Eta q _ _) = ⊢ok q
⊢ok (UIP q _ _ _) = ⊢ok q

ok＝ :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  Ok Γ

ok＝ ◇ = ◇
ok＝ (∷ q _ h _) =
  -- helper used here
  ∷ h (ok＝ q)

＝ok :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  Ok Γ'

＝ok ◇ = ◇
＝ok (∷ q _ _ h) =
  -- helper used here
  ∷ h (＝ok q)

----------------------------------------------------------------------
-- Context inversion
----------------------------------------------------------------------
∷⁻¹ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  {J : Jg}
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢ J)
  → ---------------------------------
  (Γ ⊢ A ⦂ l) ∧ Ok Γ

∷⁻¹ q
  -- helper hypothesis used here
  with ∷ q' h ← ⊢ok q = (q' , h)

----------------------------------------------------------------------
-- Version of the rule for context formation without helper hypothesis
----------------------------------------------------------------------
∷⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ⦂ l)
  → -----------------
  Ok (Γ ⸴ x ∶ A ⦂ l)

∷⁻ q = ∷ q (⊢ok q)

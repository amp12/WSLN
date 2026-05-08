module ETT.Sized.Ok where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.Sized.TypeSystem

----------------------------------------------------------------------
-- Provable judgements have well-formed contexts of smaller size
----------------------------------------------------------------------
⊢ok :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → ---------
  Ok Γ

⊢ok< :
  {Γ : Cx}
  {J : Jg}
  (q : Γ ⊢ J)
  → -------------------
  size (⊢ok q) < size q

-- Helper function
⊢ok≤ :
  (s : ℕ)
  {Γ : Cx}
  {J : Jg}
  (q : Γ ⊢ J)
  ⦃ _ : size q ≤ s ⦄
  → -------------------------------
  ∑[ q' ∈ Ok Γ ] (size q' < size q)

⊢ok q  = π₁ (⊢ok≤ (size q) q ⦃ ≤refl ⦄)

⊢ok< q = π₂ (⊢ok≤ (size q) q ⦃ ≤refl ⦄)

⊢ok≤ 0 q ⦃ p ⦄
  with (_ , e) ← Jg+ q
  rewrite e = case p of λ{()}
⊢ok≤ (1+ _) (⊢𝐔 q) ⦃ 1+≤ ⦄ = (q , ≤refl)
⊢ok≤ (1+ s) (⊢𝚷 q _) ⦃ 1+≤ ⦄
  with ∷ q' , p' ← ⊢ok≤ s q =
  let (q'' , p'') = ⊢ok≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄
  in (q'' ,  ≤step ∘ p' ∘ ≤step ∘ ≤step ∘ p'')
⊢ok≤ (1+ s) (⊢𝐈𝐝 q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ _) (⊢𝐍𝐚𝐭 q) ⦃ 1+≤ ⦄ = (q , ≤refl)
⊢ok≤ (1+ s) (⊢conv q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (⊢𝐯 q _) ⦃ 1+≤ ⦄ = (q , ≤refl)
⊢ok≤ (1+ s) (⊢𝛌 q _) ⦃ 1+≤ ⦄
  with ∷ q' , p' ← ⊢ok≤ s q =
  let (q'' , p'') = ⊢ok≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄
  in (q'' ,  ≤step ∘ p' ∘ ≤step ∘ ≤step ∘ p'')
⊢ok≤ (1+ s) (⊢∙ q₀ q₁ q₂ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₂ (size q₀) _ (size q₂) ∘ p')
⊢ok≤ (1+ s) (⊢𝐫𝐞𝐟𝐥 q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (⊢𝐳𝐞𝐫𝐨 q) ⦃ 1+≤ ⦄ = (q , ≤refl)
⊢ok≤ (1+ s) (⊢𝐬𝐮𝐜𝐜 q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ _ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₁ _ (size q₁) (size q₂) ∘ p')
⊢ok≤ (1+ s) (TyRefl q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (TySymm q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (TyTrans q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (𝚷Cong q _ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (𝐈𝐝Cong q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (TmRefl q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (TmSymm q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (TmTrans q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (＝conv q _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (⊢Reflect q₀ q₁ q₂) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₁ _ (size q₁) (size q₂) ∘ p')
⊢ok≤ (1+ s) (𝛌Cong q _) ⦃ 1+≤ ⦄
  with ∷ q' , p' ← ⊢ok≤ s q =
  let (q'' , p'') = ⊢ok≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄
  in (q'' ,  ≤step ∘ p' ∘ ≤step ∘ ≤step ∘ p'')
⊢ok≤ (1+ s) (∙Cong q₀ q₁ q₂ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₂ (size q₀) _ (size q₂) ∘ p')
⊢ok≤ (1+ s) (𝐬𝐮𝐜𝐜Cong q) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q in (q' , ≤step ∘ p')
⊢ok≤ (1+ s) (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ _ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₁ ⦃ it ∘ ≤max⁴₂ (size q₀) _ (size q₂) (size q₃) ⦄
  in (q' , ≤step ∘ ≤max⁴₂ (size q₀) _ (size q₂) (size q₃) ∘ p')
⊢ok≤ (1+ s) (𝚷Beta q₀ q₁ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₁ ⦃ it ∘ ≤max₂ (size q₀) _ ⦄
  in (q' , ≤step ∘ ≤max₂ (size q₀) _ ∘ p')
⊢ok≤ (1+ s) (𝐍𝐚𝐭Beta₀ q _ _ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q ⦃ it ∘ ≤max₁ _ _ ⦄
  in (q' , ≤step ∘ ≤max₁ _ _ ∘ p')
⊢ok≤ (1+ s) (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ _ _) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₁ _ (size q₁) (size q₂) ∘ p')
⊢ok≤ (1+ s) (𝚷Eta q₀ q₁) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₁ ⦃ it ∘ ≤max₂ (size q₀) _ ⦄
  in (q' , ≤step ∘ ≤max₂ (size q₀) _ ∘ p')
⊢ok≤ (1+ s) (UIP q₀ q₁ q₂) ⦃ 1+≤ ⦄ =
  let (q' , p') = ⊢ok≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄
  in (q' , ≤step ∘ ≤max³₁ _ (size q₁) (size q₂) ∘ p')
⊢ok≤ (1+ s) (Ty→Tm q) = ⊢ok≤ (1+ s) q
⊢ok≤ (1+ s) (Tm→Ty q) = ⊢ok≤ (1+ s) q
⊢ok≤ (1+ s) (=Ty→Tm q) = ⊢ok≤ (1+ s) q
⊢ok≤ (1+ s) (=Tm→Ty q) = ⊢ok≤ (1+ s) q

-- ----------------------------------------------------------------------
-- -- Context inversion
-- ----------------------------------------------------------------------
-- ∷⁻¹ :
--   {h : ℕ}
--   {l : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {x : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   {J : Jg}
--   (_ : Γ ⸴ x ∶ A ⦂ l ⊢[ 1+ h ] J)
--   → -----------------------------
--   (Γ ⊢[ h ] A ⦂ l) ∧ Ok[ h ] Γ

-- ∷⁻¹ q
--   with ∷ q' ← ⊢ok q
--   with (_ , refl) ← +Jg q' =
--   (≤Jg q' _ ⦃ ≤step ⦄ , (≤Ok (⊢ok q') _ ⦃ ≤trans ≤step ≤step ⦄))

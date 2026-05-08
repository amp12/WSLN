module MLTT1.UniqueTypes where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTT1.Syntax
open import MLTT1.Judgement
open import MLTT1.TypeSystem
open import MLTT1.ContextConversion
open import MLTT1.Ok
open import MLTT1.WellScoped
open import MLTT1.Renaming
open import MLTT1.Substitution
open import MLTT1.ReflexivityInversion
open import MLTT1.AdmissibleRules

----------------------------------------------------------------------
-- Types of terms are unique up to conversion and have a unique level
----------------------------------------------------------------------
svVr :
 {l l' : Lvl}
 {Γ : Cx}
 {A A' : Ty}
 {x : 𝔸}
 (_ : (x , A , l) isIn Γ)
 (_ : (x , A' , l') isIn Γ)
 → ------------------------
 (l ≡ l') ∧ (A ≡ A')

svVr  (isInNew p) (isInNew refl) with refl ← cong π₂ p = (refl , refl)
svVr  (isInNew refl) (isInOld q) = Øelim (∉→¬∈ it (isIn→dom q))
svVr  (isInOld q) (isInNew refl) = Øelim (∉→¬∈ it (isIn→dom q))
svVr  (isInOld p) (isInOld q) = svVr p q

svTy :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : Γ ⊢ a ∶ A' ∶ l')
  → ---------------------------
  (l ≡ l') ∧ (Γ ⊢ A ＝ A' ∶𝐔 l)

svTy (⊢conv q₀ q₁) q' with (refl , q) ← svTy q₀ q' =
  (refl , Trans (Symm q₁) q)
svTy q (⊢conv q₀' q₁') with (refl , q') ← svTy q q₀' =
  (refl , Trans q' q₁')
svTy (⊢𝐯 q₀ q₁) (⊢𝐯 _ q₁') with (refl , refl) ← svVr q₁ q₁' =
  (refl , Refl (ok→ty q₀ q₁))
svTy (⊢𝐔 q) (⊢𝐔 _) = (refl , Refl (⊢𝐔 q))
svTy (⊢𝚷{B = B}{x} q₀ q₁ q₂) (⊢𝚷{x = x'} q₀' q₁' q₂')
  with (refl , _) ← svTy q₀ q₀'
  with (refl , _ ) ← svTy (rnTy¹{x = x}{x'}{B = B} q₁ q₂) q₁' =
  (refl , Refl (⊢𝐔 (⊢ok q₀)))
svTy (⊢𝛌{B = B}{b}{x} q₀ q₁ h₀ h₁)
     (⊢𝛌{B = B'}{x = x'} q₀' q₁' h₀' h₁')
  with (refl , _) ← svTy h₀ h₀'
  with (refl , r) ← svTy (rnTm¹{x = x}{x'}{B = B}{b} q₀ q₁) q₀' =
    (refl , 𝚷Cong
      (Refl h₀)
      r
      ((⊆∉ (∉⊆ (∉∪₁ q₁) (⊢supp h₁ ∘ ∈∪₁ ∘ ⟨⟩supp B (𝐯 x))) it) ∉∪ (∉∪₁ q₁'))
      h₀)
svTy (⊢∙{B = B}{a}{x = x} _ q₁ q₂ q₃ _) (⊢∙{x = x'} _ q₁' q₂' _ _)
  with (refl , _) ← svTy q₁ q₁'
  with (refl , _ ) ← svTy (rnTy¹{x = x}{x'}{B = B} q₂ q₃) q₂' =
  (refl , Refl (concTy B x q₂ q₁ q₃))
svTy (⊢𝐈𝐝 q _ _) (⊢𝐈𝐝 q' _ _)
  with (refl , _) ← svTy q q' = (refl , Refl (⊢𝐔 (⊢ok q)))
svTy (⊢𝐫𝐞𝐟𝐥 q _) (⊢𝐫𝐞𝐟𝐥 q' _)
  with (refl , r) ← svTy q q' = (refl , 𝐈𝐝Cong r (Refl q) (Refl q))
svTy{Γ = Γ} (⊢𝐉{l}{A = A}{C}{a}{b}{e = e}{x}{y} q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ _)
     (⊢𝐉 _ q₁' _ q₃' _ _ _ _ _)
  with (refl , _) ← svTy q₁ q₁'
  with (refl , _) ← svTy q₃ q₃' =
  (refl , Refl (concTy² C x y q₀ q₂ q q₅ q₆))
  where
  q : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x) ∶ l
  q rewrite ssbFresh x b A (⊆∉ (⊢supp h₀ ∘ ∈∪₁) it)
    | ssbFresh x b a (⊆∉ (⊢supp q₁ ∘ ∈∪₁) it)
    | updateEq{ι}{b} x = q₄
svTy (⊢𝐍𝐚𝐭 q) (⊢𝐍𝐚𝐭 _) = (refl , Refl (⊢𝐔 q))
svTy (⊢𝐳𝐞𝐫𝐨 q) (⊢𝐳𝐞𝐫𝐨 _) = (refl , Refl (⊢𝐍𝐚𝐭 q))
svTy (⊢𝐬𝐮𝐜𝐜 q) (⊢𝐬𝐮𝐜𝐜 _) = (refl , Refl (⊢𝐍𝐚𝐭 (⊢ok q)))
svTy (⊢𝐧𝐫𝐞𝐜{C = C}{x = x} q₀ _ q₂ (q₃ ∉∪ _) _ h) (⊢𝐧𝐫𝐞𝐜 q₀' _ _ _ _ _)
  with (refl , _) ← svTy q₀ q₀' =
  (refl , Refl (concTy C x h q₂ q₃))

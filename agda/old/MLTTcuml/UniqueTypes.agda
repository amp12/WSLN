module MLTTcuml.UniqueTypes where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTTcuml.Syntax
open import MLTTcuml.Judgement
open import MLTTcuml.TypeSystem
open import MLTTcuml.ContextConversion
open import MLTTcuml.Ok
open import MLTTcuml.WellScoped
open import MLTTcuml.Renaming
open import MLTTcuml.Substitution
open import MLTTcuml.ReflexivityInversion
open import MLTTcuml.AdmissibleRules

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Types of terms are unique up to conversion
----------------------------------------------------------------------
svVr :
 {Γ : Cx}
 {A B : Ty}
 {x : 𝔸}
 (_ : (x , A) isIn Γ)
 (_ : (x , B) isIn Γ)
 → ------------------
 A ≡ B

svVr  (isInNew refl) (isInNew p) = cong π₂ p
svVr  (isInNew refl) (isInOld q) = Øelim (∉→¬∈ it (isIn→dom q))
svVr  (isInOld q) (isInNew refl) = Øelim (∉→¬∈ it (isIn→dom q))
svVr  (isInOld p) (isInOld q) = svVr p q

svTy :
  {Γ : Cx}
  {A B : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⊢ a ∶ B)
  → -------------
  Γ ⊢ A ＝ B ty

svTy (⊢conv q₀ q₁) q' = TyTrans (TySymm q₁) (svTy q₀ q')

svTy q (⊢conv q₀' q₁') = TyTrans (svTy q q₀') q₁'

svTy (⊢𝐯 q₀ q₁) (⊢𝐯 q₀' q₁')
  with refl ← svVr q₁ q₁' = TyRefl (ok→ty q₀ q₁)

svTy (⊢𝚷 q _ _) (⊢𝚷 _ _ _) = TyRefl (⊢𝐔 (⊢ok q))

svTy{Γ} (⊢𝛌{A}{B}{b}{x} q₀ q₁ h₀ h₁)
     (⊢𝛌{B = B'}{x = x'} q₀' q₁' _ _) =
   𝚷TyCong{x = x'}
     (TyRefl h₀)
     (svTy (rnTm¹ {B = B}{b} q₀ q₁) q₀')
     (x'#B ∉∪ ∉∪₁ q₁')
     h₀
  where
  x'#B : x' # B
  x'#B = ⊆∉
    (∉⊆ (∉∪₁ q₁) (⊢supp h₁ ∘ ⟨⟩supp B (𝐯 x)))
    it

svTy (⊢∙{B = B}{a}{x = x} _ q₁ q₂ q₃ _) (⊢∙ _ _ _ _ _) =
  TyRefl (concTy B x q₂ q₁ q₃)

svTy (⊢𝐈𝐝 q _ _) (⊢𝐈𝐝 _ _ _) = TyRefl (⊢𝐔 (⊢ok q))

svTy (⊢𝐫𝐞𝐟𝐥 q _) (⊢𝐫𝐞𝐟𝐥 q' _) =
  𝐈𝐝TyCong (svTy q q') (TmRefl q) (TmRefl q)

svTy{Γ} (⊢𝐉{A}{C}{a}{b}{c}{e}{x}{y} q₀ q₁ q₂ _ q₄ q₅ q₆ h₀ _)
        (⊢𝐉 _ _ _ _ _ _ _ _ _) =
  TyRefl (concTy² C x y q₀ q₂ q q₅ q₆)
  where
  q : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
  q rewrite ssbFresh x b A (⊆∉ (⊢supp h₀) it)
    | ssbFresh x b a (⊆∉ (⊢supp q₁ ∘ ∈∪₁) it)
    | updateEq{ι}{b} x = q₄

svTy (⊢𝐍𝐚𝐭 q) (⊢𝐍𝐚𝐭 _) = TyRefl (⊢𝐔 q)

svTy (⊢𝐳𝐞𝐫𝐨 q) (⊢𝐳𝐞𝐫𝐨 _) = TyRefl (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 q))

svTy (⊢𝐬𝐮𝐜𝐜 q) (⊢𝐬𝐮𝐜𝐜 _) = TyRefl ((⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q))))

svTy (⊢𝐧𝐫𝐞𝐜{C = C}{a = a}{x = x} _ _ q₂ (q₃ ∉∪ _) _ h)
     (⊢𝐧𝐫𝐞𝐜 _ _ _ _ _ _) =
  TyRefl (concTy C x h q₂ q₃)

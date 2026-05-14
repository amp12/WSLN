module MLTT.Weakening where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.Cofinite
open import MLTT.Ok
open import MLTT.WellScoped

----------------------------------------------------------------------
-- Identity weakening
----------------------------------------------------------------------
▷id :
  {Γ : Cx}
  (_ : Ok Γ)
  → ---------
  Γ ▷ Γ

▷id ok◇             = ▷◇
▷id (ok⨟ q₀ q₁ q₂) = ▷⨟ (▷id q₂) q₀ q₁ q₀

proj :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : Γ ⊢ A ⦂ l)
  (_ : x # Γ)
  → ---------------
  Γ ⨟ x ∶ A ⦂ l ▷ Γ

proj q = ▷proj (▷id (⊢ok q)) q

----------------------------------------------------------------------
-- Types of variables under weakening
----------------------------------------------------------------------
▷Var :
  {l : Lvl}
  {Δ Γ : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Δ ▷ Γ)
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  (x , A , l) isIn Δ

▷Var (▷proj p _ _) isInNew     = isInOld (▷Var p isInNew)
▷Var (▷⨟ _ _ _ _)  isInNew     = isInNew
▷Var (▷proj p _ _) (isInOld q) = isInOld (▷Var p (isInOld q))
▷Var (▷⨟ p _ _ _)  (isInOld q) = isInOld (▷Var p q)

----------------------------------------------------------------------
-- Weakening preserves provable judgements
----------------------------------------------------------------------
▷Jg :
  {Δ Γ : Cx}
  {J : Jg}
  (_ : Δ ▷ Γ)
  (_ : Γ ⊢ J)
  → ---------
  Δ  ⊢ J

▷Jg p (⊢conv q₀ q₁) = ⊢conv (▷Jg p q₀) (▷Jg p q₁)
▷Jg p (⊢𝐯 _ q) = ⊢𝐯 (Ok▷ p) (▷Var p q)
▷Jg p (⊢𝐔 _) = ⊢𝐔 (Ok▷ p)
▷Jg{Δ} p (⊢𝚷 S q₀ q₁) = ⊢𝚷
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p q₀ x#Δ (▷Jg p q₀)) (q₁ x x#S)})
▷Jg{Δ} p (⊢𝛌 S q₀ h₀ h₁) = ⊢𝛌
  (S ∪ supp Δ)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (q₀ x x#S)})
  (▷Jg p h₀)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)})
▷Jg{Δ} p (⊢∙ S q₀ q₁ q₂ h) = ⊢∙
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (▷Jg p q₁)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h x#Δ (▷Jg p h)) (q₂ x x#S)})
  (▷Jg p h)
▷Jg p (⊢𝐈𝐝 q₀ q₁ h) = ⊢𝐈𝐝
  (▷Jg p q₀)
  (▷Jg p q₁)
  (▷Jg p h)
▷Jg p (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐫𝐞𝐟𝐥
  (▷Jg p q)
  (▷Jg p h)
▷Jg{Δ} p (⊢𝐉 S q₀ q₁ q₂ q₃ q₄ h₀ h₁) = ⊢𝐉
  (S ∪ supp Δ)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p h₀ x#Δ (▷Jg p h₀))
      (h₁ x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)))
    (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (▷Jg p q₁)
  (▷Jg p q₂)
  (▷Jg p q₃)
  (▷Jg p q₄)
  (▷Jg p h₀)
  λ{ x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)}
▷Jg p (⊢𝐍𝐚𝐭 _) = ⊢𝐍𝐚𝐭 (Ok▷ p)
▷Jg p (⊢𝐳𝐞𝐫𝐨 _) = ⊢𝐳𝐞𝐫𝐨 (Ok▷ p)
▷Jg p (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (▷Jg p q)
▷Jg{Δ} p (⊢𝐧𝐫𝐞𝐜 S q₀ q₁ q₂ h) = ⊢𝐧𝐫𝐞𝐜
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₂)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
      (h x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₂)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (h x x#S)))
    (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))} )
  (▷Jg p q₂)
  λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₂)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (h x x#S)}
▷Jg p (Refl q) = Refl (▷Jg p q)
▷Jg p (Symm q) = Symm (▷Jg p q)
▷Jg p (Trans q₀ q₁) = Trans (▷Jg p q₀) (▷Jg p q₁)
▷Jg p (＝conv q₀ q₁) = ＝conv (▷Jg p q₀) (▷Jg p q₁)
▷Jg{Δ} p (𝚷Cong S q₀ q₁ h) = 𝚷Cong
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h x#Δ (▷Jg p h)) (q₁ x x#S)})
  (▷Jg p h)
▷Jg{Δ} p (𝛌Cong S q₀ q₁ h₀ h₁) = 𝛌Cong
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (q₁ x x#S)})
  (▷Jg p h₀)
  λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)}
▷Jg{Δ} p (∙Cong S q₀ q₁ q₂ q₃ h₀ h₁) = ∙Cong
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x (x#S ∉∪ x#Δ) →
     ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (q₁ x x#S)})
  (▷Jg p q₂)
  (▷Jg p q₃)
  (▷Jg p h₀)
  (λ{x (x#S ∉∪ x#Δ) →
     ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)})
▷Jg p (𝐈𝐝Cong q₀ q₁ q₂) = 𝐈𝐝Cong
  (▷Jg p q₀)
  (▷Jg p q₁)
  (▷Jg p q₂)
▷Jg p (𝐫𝐞𝐟𝐥Cong q h) = 𝐫𝐞𝐟𝐥Cong
  (▷Jg p q)
  (▷Jg p h)
▷Jg{Δ} p (𝐉Cong S q₀ q₁ q₂ q₃ q₄ h₀ h₁) = 𝐉Cong
  (S ∪ supp Δ)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p h₀ x#Δ (▷Jg p h₀))
      (h₁ x x#S)
      (y#Δ ∉∪ #symm x#y)
      (▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)))
    (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (▷Jg p q₁)
  (▷Jg p q₂)
  (▷Jg p q₃)
  (▷Jg p q₄)
  (▷Jg p h₀)
  λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)}
▷Jg p (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (▷Jg p q)
▷Jg{Δ} p (𝐧𝐫𝐞𝐜Cong S q₀ q₁ q₂ q₃ h) = 𝐧𝐫𝐞𝐜Cong
  (S ∪ supp Δ)
  (λ{x (x#S ∉∪ x#Δ) →
    ▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₃)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (q₀ x x#S)})
  (▷Jg p q₁)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₃)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
      (h x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₃)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (h x x#S)))
    (q₂ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (▷Jg p q₃)
  λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₃)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
    (h x x#S)}
▷Jg{Δ} p (𝚷Beta{B = B} S q₀ q₁ h₀ h₁) = 𝚷Beta{B = B}
  (S ∪ supp Δ)
  (λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p h₀ x#Δ (▷Jg p h₀))
    (q₀ x x#S)})
  (▷Jg p q₁)
  (▷Jg p h₀)
  (λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p h₀ x#Δ (▷Jg p h₀))
    (h₁ x x#S)})
▷Jg{Δ} p (𝐈𝐝Beta S q₀ q₁ q₂ h₀ h₁) = 𝐈𝐝Beta
  (S ∪ supp Δ)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p h₀ x#Δ (▷Jg p h₀))
      (h₁ x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p h₀ x#Δ (▷Jg p h₀)) (h₁ x x#S)))
    (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (▷Jg p q₁)
  (▷Jg p q₂)
  (▷Jg p h₀)
  (λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p h₀ x#Δ (▷Jg p h₀))
    (h₁ x x#S)})
▷Jg{Δ} p (𝐍𝐚𝐭Beta₀ S q₀ q₁ h) = 𝐍𝐚𝐭Beta₀
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
      (h x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (h x x#S)))
    (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
    (h x x#S)})
▷Jg{Δ} p (𝐍𝐚𝐭Beta₊ S q₀ q₁ q₂ h) = 𝐍𝐚𝐭Beta₊
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (λ{x y (##:: (y#S ∉∪ y#Δ) (##:: (x#y ∉∪ x#S ∉∪ x#Δ) ##◇)) → ▷Jg
    (▷⨟
      (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
      (h x x#S)
      (y#Δ ∉∪ (#symm x#y))
      (▷Jg (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p))) (h x x#S)))
    (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))})
  (▷Jg p q₂)
  λ{x (x#S ∉∪ x#Δ) → ▷Jg
   (▷⨟ p (⊢𝐍𝐚𝐭 (⊢ok q₀)) x#Δ (⊢𝐍𝐚𝐭 (Ok▷ p)))
   (h x x#S)}
▷Jg{Δ} p (𝚷Eta S q₀ q₁ q₂ h) = 𝚷Eta
  (S ∪ supp Δ)
  (▷Jg p q₀)
  (▷Jg p q₁)
  (λ{x (x#S ∉∪ x#Δ) → ▷Jg
    (▷⨟ p h x#Δ (▷Jg p h))
    (q₂ x x#S)})
  (▷Jg p h)


▷⨟Jg :
  {Δ Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  {l : Lvl}
  {J : Jg}
  (_ : Γ ⨟ x ∶ A ⦂ l ⊢ J)
  (_ : Δ ▷ Γ)
  (_ : x # Δ)
  → ---------------------
  Δ ⨟ x ∶ A ⦂ l ⊢ J

▷⨟Jg q p x#Δ
  with ok⨟ q' x#Γ okΓ ← ⊢ok q =
  ▷Jg (▷⨟ p q' x#Δ (▷Jg p q')) q

----------------------------------------------------------------------
-- Admissible rule for context weakening
----------------------------------------------------------------------
▷⨟⁻ :
  {l : Lvl}
  {Δ Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : Δ ▷ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : x # Δ)
  → ----------------------------
   Δ ⨟ x ∶ A ⦂ l ▷ Γ ⨟ x ∶ A ⦂ l

▷⨟⁻ p q x#Δ = ▷⨟ p q x#Δ (▷Jg p q)

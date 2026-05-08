module MLTT.Uniqueness where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.Cofinite
open import MLTT.Ok
open import MLTT.WellScoped
open import MLTT.Weakening
open import MLTT.Substitution
open import MLTT.Admissible
open import MLTT.ExistsFresh

----------------------------------------------------------------------
-- Types of terms are unique up to conversion and have a unique level
----------------------------------------------------------------------
svVr :
 {l l' : Lvl}
 {Γ : Cx}
 {A A' : Ty}
 {x x' : 𝔸}
 (_ : Ok Γ)
 (_ : (x , A , l) isIn Γ)
 (_ : (x' , A' , l') isIn Γ)
 (_ : x ≡ x')
 → -------------------------
 (l ≡ l') ∧ (A ≡ A')

svVr _ isInNew isInNew _ = refl , refl
svVr ([] _ q _) isInNew (isInOld p') refl =
  Øelim (∉→¬∈ q (isIn→dom p'))
svVr ([] _ q _) (isInOld p) isInNew refl =
  Øelim (∉→¬∈ q (isIn→dom p))
svVr ([] _ _ q) (isInOld p) (isInOld p') e = svVr q p p' e

svTy :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ a ∶ A' ⦂ l')
  → ---------------------------
  (l ≡ l') ∧ (Γ ⊢ A ＝ A' ⦂ l)

svTy (⊢conv q₀ q₁) q' with (refl , q) ← svTy q₀ q' =
  (refl , Trans (Symm q₁) q)

svTy q (⊢conv q₀' q₁') with (refl , q') ← svTy q q₀' =
  (refl , Trans q' q₁')

svTy (⊢𝐯 q₀ q₁) (⊢𝐯 _ q₁')
  with (refl , refl) ← svVr q₀ q₁ q₁' refl =
  (refl , Refl (ok→ty q₀ q₁))

svTy (⊢𝐔 q) (⊢𝐔 _) = (refl , Refl (⊢𝐔 q))

svTy (⊢𝚷 _ q₀ _) (⊢𝚷 _ _ _) = refl , (Refl (⊢𝐔 (⊢ok q₀)))

svTy (⊢𝛌{B = B} S q₀ q₁ _) (⊢𝛌{B = B'} S' q₀' q₁' _)
  with (refl , _ ) ← svTy q₁ q₁'
  | (x , x#S ∉∪ x#S' ∉∪ x#) ← fresh (S , S' , B , B')
  with (refl , r) ← svTy (q₀ x x#S) (q₀' x x#S') =
  refl , (𝚷Cong⁻ (Refl q₁) r x#)

svTy (⊢∙{B = B} S _ q₁ q₂ _) (⊢∙ S' _ q₁' q₂' _)
  with (refl , _) ← svTy q₁ q₁'
  | (x , x#S ∉∪ x#S' ∉∪ x#) ← fresh (S , S' , B)
  with (refl , _) ← svTy (q₂ x x#S) (q₂' x x#S') =
  (refl , Refl (concTy B x (q₂ x x#S) q₁ x#))

svTy (⊢𝐈𝐝 q _ _) (⊢𝐈𝐝 q' _ _)
  with (refl , _) ← svTy q q' =
  (refl , Refl (⊢𝐔 (⊢ok q)))

svTy (⊢𝐫𝐞𝐟𝐥 q _) (⊢𝐫𝐞𝐟𝐥 q' _)
  with (refl , r) ← svTy q q' =
  (refl , 𝐈𝐝Cong r (Refl q) (Refl q))

svTy{Γ = Γ} (⊢𝐉{l}{A = A}{C}{a}{b}{e = e} S q₀ q₁ q₂ q₃ q₄ h₀ h₁)
     (⊢𝐉 _ _ q₁' _ q₃' _ _ _)
  with (refl , _) ← svTy q₁ q₁'
  | (refl , _) ← svTy q₃ q₃'
  | (y , y#S ∉∪ y#C) ← fresh (S , C)
  with (x , x#y ∉∪ x#S) ← fresh (y , S) =
  (refl , Refl (concTy² C x y
    (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))
    q₂
    q
    x#C
    y#C))
  where
  x#Γ : x # Γ
  x#Γ = π₁ ([]⁻¹ (⊢ok (h₁ x x#S)))
  x#A : x # A
  x#A = ⊆∉ (⊢supp h₀ ∘ ∈∪₁) x#Γ
  x#a : x # a
  x#a = ⊆∉ (⊢supp q₁ ∘ ∈∪₁) x#Γ
  x#C : x # C
  x#C = ⊆∉ (⊢supp q₃ ∘ ∈∪₂ ∘ []²supp C a (𝐫𝐞𝐟𝐥 a)) x#Γ

  q : Γ ⊢ e ∶ (x := b) * 𝐈𝐝 A a (𝐯 x) ⦂ l
  q rewrite ssbFresh x b A x#A
    | ssbFresh x b a x#a
    | updateEq{id}{b} x = q₄

svTy (⊢𝐍𝐚𝐭 q) (⊢𝐍𝐚𝐭 _) = (refl , Refl (⊢𝐔 q))

svTy (⊢𝐳𝐞𝐫𝐨 q) (⊢𝐳𝐞𝐫𝐨 _) = (refl , Refl (⊢𝐍𝐚𝐭 q))

svTy (⊢𝐬𝐮𝐜𝐜 q) (⊢𝐬𝐮𝐜𝐜 _) = (refl , Refl (⊢𝐍𝐚𝐭 (⊢ok q)))

svTy (⊢𝐧𝐫𝐞𝐜{C = C} S q₀ _ q₂ h) (⊢𝐧𝐫𝐞𝐜 _ q₀' _ _ _)
  with (refl , _) ← svTy q₀ q₀'
  | (x , x#S ∉∪ x#) ← fresh (S , C) =
  (refl , Refl (concTy C x (h x x#S) q₂ x#))

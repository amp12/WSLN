module MLTT.AdmissibleRules where

open import Decidable
open import Empty
open import Equivalence
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem
open import MLTT.ContextConversion
open import MLTT.Ok
open import MLTT.WellScoped
open import MLTT.Renaming
open import MLTT.Substitution
open import MLTT.ReflexivityInversion

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Congruence property of substitution
----------------------------------------------------------------------
congSbTm :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → ---------------------------
  Γ' ⊢ σ * a ＝ σ' * a' ∶ σ * A

congSbTm q q' = Trans
  (sbJg (⊢sb₁ q) q')
  (＝sbTm q (⊢ty₂ q') (⊢sb₁ q))

----------------------------------------------------------------------
-- Substitution properties of concretion
----------------------------------------------------------------------
concTy :
  {ℓ : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A) ⊢ B ⟨ x ⟩ ∶ 𝐒𝐞𝐭 ℓ)
  (_ : Γ ⊢ a ∶ A)
  (_ : x # B)
  → ---------------------------------
  Γ ⊢ B ⟨ a ⟩ ∶ 𝐒𝐞𝐭 ℓ

concTy{ℓ}{Γ}{A}{a} B x q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ∶ 𝐒𝐞𝐭 ℓ)
    (ssb⟨⟩ x a B q₂)
    (sbJg (ssbUpdate q₁ ⊢A) q₀)

concTy² :
  {ℓ : Lvl}
  {Γ : Cx}
  {A B : Ty}
  {a b : Tm}
  (C : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ⸴ y ∶ B) ⊢ C ⟨ x ⸴ y ⟩ ∶ 𝐒𝐞𝐭 ℓ)
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B)
  (_ : x # C)
  (_ : y # C)
  → ---------------------------------------------
  Γ ⊢ C ⟨ a ⸴ b ⟩ ∶ 𝐒𝐞𝐭 ℓ

concTy²{ℓ}{Γ}{A}{B}{a}{b} C x y q₀ q₁ q₃ q₄ q₅
  with ∷ ⊢B (∷ ⊢A _) ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ∶ 𝐒𝐞𝐭 ℓ)
    (ssb⟨⟩² x y a b C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (sbJg (ssbUpdate² q₁ ⊢B q₃) q₀)

----------------------------------------------------------------------
-- Well-formed contexts contain well-formed types
----------------------------------------------------------------------
ok→ty :
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : Ok Γ)
  (_ : (x , A) isIn Γ)
  → ------------------------
  ∑[ ℓ ∈ Lvl ] Γ ⊢ A ∶ 𝐒𝐞𝐭 ℓ

ok→ty (∷ q _) (isInNew refl) = (_ , wkJg _ q q)
ok→ty (∷ q₀ q₁) (isInOld q₂) =
  let  (ℓ , q ) = ok→ty q₁ q₂ in (ℓ , wkJg _ q₀ q)

----------------------------------------------------------------------
-- Well-typed terms have well-formed types
----------------------------------------------------------------------
⊢∶ty :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A)
  → -------------------------
  ∑[ ℓ ∈ Lvl ] Γ ⊢ A ∶ 𝐒𝐞𝐭 ℓ

⊢∶ty (⊢conv _ q) = (_ , ⊢ty₂ q)
⊢∶ty (⊢𝐯 q₀ q₁) = ok→ty q₀ q₁
⊢∶ty (⊢𝐔 q) = (_ , ⊢𝐔 q)
⊢∶ty (⊢𝚷 q _ _) = (_ , ⊢𝐔 (⊢ok q))
⊢∶ty (⊢𝛌 _ (q₁ ∉∪ _) q₂ q₃) = (_ , ⊢𝚷 q₂ q₃ q₁)
⊢∶ty (⊢∙{B = B}{x = x} q q₁ q₂ q₃ q₄) = (_ , concTy B x q₂ q₁ q₃)
⊢∶ty (⊢𝐈𝐝 q _ _) = ⊢∶ty q
⊢∶ty (⊢𝐫𝐞𝐟𝐥 q _) = let (ℓ , q') = ⊢∶ty q in (ℓ , ⊢𝐈𝐝 q' q q)
⊢∶ty{Γ} (⊢𝐉{A = A}{C}{a}{b}{e = e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈) = (_ , concTy² C x y q₀ q₂ q₄' q₅ q₆)
  where
  x#a : x # a
  x#a = ∉∪₁ (⊢# q₁ it)

  x#A : x # A
  x#A = ∉∪₂ (⊢# q₁ it)

  q₄' : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
  q₄' rewrite ssbFresh x b A x#A
      | ssbFresh x b a x#a
      | updateEq{ι}{b} x = q₄
⊢∶ty (⊢𝐍𝐚𝐭 q) = (_ , ⊢𝐔 q)
⊢∶ty (⊢𝐳𝐞𝐫𝐨 q) = (_ , ⊢𝐍𝐚𝐭 q)
⊢∶ty (⊢𝐬𝐮𝐜𝐜 q) = ⊢∶ty q
⊢∶ty (⊢𝐧𝐫𝐞𝐜{C = C}{x = x} _ _ q (q' ∉∪ _) _ h) =
  (_ , concTy C x h q q')

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
  → -----------------------------
  ∑[ ℓ ∈ Lvl ] Γ ⊢ A ＝ B ∶ 𝐒𝐞𝐭 ℓ

svTy (⊢conv q₀ q₁) q' =
  let (ℓ , q'') = svTy q₀ q' in (_ , Trans (Symm q₁) {!!})
svTy q (⊢conv q₀' q₁') = {!!}
svTy q q' = {!!}

-- svTy (⊢conv q₀ q₁) q' = TyTrans (TySymm q₁) (svTy q₀ q')

-- svTy q (⊢conv q₀' q₁') = TyTrans (svTy q q₀') q₁'

-- svTy (⊢𝐯 q₀ q₁) (⊢𝐯 q₀' q₁')
--   with refl ← svVr q₁ q₁' = TyRefl (ok→ty q₀ q₁)

-- svTy (⊢𝚷 q _ _) (⊢𝚷 _ _ _) = TyRefl (⊢𝐔 (⊢ok q))

-- svTy{Γ} (⊢𝛌{A}{B}{b}{x} q₀ q₁ h₀ h₁)
--      (⊢𝛌{B = B'}{x = x'} q₀' q₁' _ _) =
--    𝚷TyCong{x = x'}
--      (TyRefl h₀)
--      (svTy (rnTm¹ {B = B}{b} q₀ q₁) q₀')
--      (x'#B ∉∪ ∉∪₁ q₁')
--      h₀
--   where
--   x'#B : x' # B
--   x'#B = ⊆∉
--     (∉⊆ (∉∪₁ q₁) (⊢supp h₁ ∘ ⟨⟩supp B (𝐯 x)))
--     it

-- svTy (⊢∙{B = B}{a}{x = x} _ q₁ q₂ q₃ _) (⊢∙ _ _ _ _ _) =
--   TyRefl (concTy B x q₂ q₁ q₃)

-- svTy (⊢𝐈𝐝 q _ _) (⊢𝐈𝐝 _ _ _) = TyRefl (⊢𝐔 (⊢ok q))

-- svTy (⊢𝐫𝐞𝐟𝐥 q _) (⊢𝐫𝐞𝐟𝐥 q' _) =
--   𝐈𝐝TyCong (svTy q q') (TmRefl q) (TmRefl q)

-- svTy{Γ} (⊢𝐉{A}{C}{a}{b}{c}{e}{x}{y} q₀ q₁ q₂ _ q₄ q₅ q₆ h₀ _)
--         (⊢𝐉 _ _ _ _ _ _ _ _ _) =
--   TyRefl (concTy² C x y q₀ q₂ q q₅ q₆)
--   where
--   q : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
--   q rewrite ssbFresh x b A (⊆∉ (⊢supp h₀) it)
--     | ssbFresh x b a (⊆∉ (⊢supp q₁ ∘ ∈∪₁) it)
--     | updateEq{ι}{b} x = q₄

-- svTy (⊢𝐍𝐚𝐭 q) (⊢𝐍𝐚𝐭 _) = TyRefl (⊢𝐔 q)

-- svTy (⊢𝐳𝐞𝐫𝐨 q) (⊢𝐳𝐞𝐫𝐨 _) = TyRefl (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 q))

-- svTy (⊢𝐬𝐮𝐜𝐜 q) (⊢𝐬𝐮𝐜𝐜 _) = TyRefl ((⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q))))

-- svTy (⊢𝐧𝐫𝐞𝐜{C = C}{a = a}{x = x} _ _ q₂ (q₃ ∉∪ _) _ h)
--      (⊢𝐧𝐫𝐞𝐜 _ _ _ _ _ _) =
--   TyRefl (concTy C x h q₂ q₃)


----------------------------------------------------------------------
-- Properties of context conversion
----------------------------------------------------------------------

{- Reflexivity (CxRefl) was proved in MLTT.ReflexivityInversion. -}

CxSymm :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  ⊢ Γ' ＝ Γ

CxSymm ◇ = ◇
CxSymm (∷ q₀ q₁ h₀ h₁) = ∷
  (CxSymm q₀)
  (＝⊢ (Symm q₁) (CxSymm q₀))
  h₁
  h₀

CxTrans :
  {Γ Γ' Γ'' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  (_ : ⊢ Γ' ＝ Γ'')
  → ---------------
  ⊢ Γ ＝ Γ''

CxTrans ◇ ◇ = ◇
CxTrans (∷ q₀ q₁ h₀ _) (∷ q₀' q₁' _ h₁') = ∷
  (CxTrans q₀ q₀')
  {!!}
  {!!}
  {!!}
  -- ∷
  -- (CxTrans q₀ q₀')
  -- (Trans q₁ ?) -- (＝⊢ q₁' q₀))
  -- h₀
  -- h₁'

-- ----------------------------------------------------------------------
-- -- Propositional equivalence of the type systems MLTT and MLTT+
-- ----------------------------------------------------------------------

-- open MLTT renaming  (Ok to Ok⁻ ; _⊢_ to _⊢⁻_)
-- -- MLTT⁺ is already open

-- MLTT↔MLTT⁺ : ∀{Γ} → (Ok⁻ Γ ↔ Ok Γ) ∧ ∀{J} → (Γ ⊢⁻ J) ↔ (Γ ⊢ J)

-- MLTT↔MLTT⁺ =
--   (↔i OkMLTT→MLTT⁺ OkMLTT⁺→MLTT)
--   ,
--   (↔i ⊢MLTT→MLTT⁺ ⊢MLTT⁺→MLTT)
--   where
--   OkMLTT→MLTT⁺ :
--     {Γ : Cx}
--     (_ : Ok⁻ Γ)
--     → --------
--     Ok Γ

--   OkMLTT⁺→MLTT :
--     {Γ : Cx}
--     (_ : Ok Γ)
--     → --------
--     Ok⁻ Γ

--   ⊢MLTT→MLTT⁺ :
--     {Γ : Cx}
--     {J : Jg}
--     (_ : Γ ⊢⁻ J)
--     → ----------
--     Γ ⊢ J

--   ⊢MLTT⁺→MLTT :
--     {Γ : Cx}
--     {J : Jg}
--     (_ : Γ ⊢ J)
--     → ---------
--     Γ ⊢⁻ J

--   OkMLTT→MLTT⁺ ◇ = ◇
--   OkMLTT→MLTT⁺ (∷ q) =
--     let q' = ⊢MLTT→MLTT⁺ q in  ∷ q' (⊢ok q')

--   OkMLTT⁺→MLTT ◇ = ◇
--   OkMLTT⁺→MLTT (∷ q _) = ∷ (⊢MLTT⁺→MLTT q)

--   ⊢MLTT→MLTT⁺ (⊢𝚷ty q₀ q₁) =
--     let q' = ⊢MLTT→MLTT⁺ q₀
--     in ⊢𝚷ty q' q₁ (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (⊢𝐈𝐝ty q₀ q₁) =
--     let q' = ⊢MLTT→MLTT⁺ q₀
--     in ⊢𝐈𝐝ty q' (⊢MLTT→MLTT⁺ q₁) (⊢∶ty q')
--   ⊢MLTT→MLTT⁺ (⊢𝐔 q) = ⊢𝐔 (OkMLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (⊢𝐄𝐥 q) = ⊢𝐄𝐥 (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (TyRefl q) = TyRefl (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (TySymm q) = TySymm (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (TyTrans q₀ q₁) = TyTrans
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--   ⊢MLTT→MLTT⁺ (𝚷TyCong q₀ q₁ q₂) =
--     let q' = ⊢MLTT→MLTT⁺ q₀
--     in 𝚷TyCong q' (⊢MLTT→MLTT⁺ q₁) q₂ (⊢Ty₁ q')
--   ⊢MLTT→MLTT⁺ (𝐈𝐝TyCong q₀ q₁ q₂) = 𝐈𝐝TyCong
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--     (⊢MLTT→MLTT⁺ q₂)
--   ⊢MLTT→MLTT⁺ (＝𝐄𝐥 q) = ＝𝐄𝐥 (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (⊢𝐯 q₀ q₁) = ⊢𝐯 (OkMLTT→MLTT⁺ q₀) q₁
--   ⊢MLTT→MLTT⁺ (⊢conv q₀ q₁) = ⊢conv
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--   ⊢MLTT→MLTT⁺ (⊢𝚷 q₀ q₁ q₂) = ⊢𝚷
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--     q₂
--   ⊢MLTT→MLTT⁺ (⊢𝛌 q₀ q₁) =
--     let q' = ⊢MLTT→MLTT⁺ q₀
--     in ⊢𝛌 q' q₁ (π₁ (∷⁻¹ q')) (⊢∶ty q')
--   ⊢MLTT→MLTT⁺ (⊢∙ q₀ q₁ q₂ q₃) =
--     let q' = ⊢MLTT→MLTT⁺ q₁
--     in ⊢∙ (⊢MLTT→MLTT⁺ q₀) q' (⊢MLTT→MLTT⁺ q₂) q₃ (⊢∶ty q')
--   ⊢MLTT→MLTT⁺ (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--     (⊢MLTT→MLTT⁺ q₂)
--   ⊢MLTT→MLTT⁺ (⊢𝐫𝐞𝐟𝐥 q) =
--     let q' = ⊢MLTT→MLTT⁺ q
--     in ⊢𝐫𝐞𝐟𝐥 q' (⊢∶ty q')
--   ⊢MLTT→MLTT⁺ (⊢𝐉 q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
--     let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in ⊢𝐉
--       q'
--       q''
--       (⊢MLTT→MLTT⁺ q₂)
--       (⊢MLTT→MLTT⁺ q₃)
--       (⊢MLTT→MLTT⁺ q₄)
--       q₅
--       q₆
--       (⊢∶ty q'')
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (⊢𝐍𝐚𝐭 q) = ⊢𝐍𝐚𝐭 (OkMLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (OkMLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄) =
--     let q'  = ⊢MLTT→MLTT⁺ q₁
--     in ⊢𝐧𝐫𝐞𝐜
--       (⊢MLTT→MLTT⁺ q₀)
--       q'
--       (⊢MLTT→MLTT⁺ q₂)
--       q₃
--       q₄
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (TmRefl q) = TmRefl (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (TmSymm q) = TmSymm (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (TmTrans q₀ q₁) = TmTrans
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--   ⊢MLTT→MLTT⁺ (＝conv q₀ q₁) = ＝conv
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--   ⊢MLTT→MLTT⁺ (𝚷TmCong q₀ q₁ q₂) =
--     let q'  = ⊢MLTT→MLTT⁺ q₀
--     in 𝚷TmCong q' (⊢MLTT→MLTT⁺ q₁) q₂ (⊢ty₁ q')
--   ⊢MLTT→MLTT⁺ (𝛌Cong q₀ q₁ q₂) =
--    let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in 𝛌Cong q' q'' q₂ (⊢Ty₁ q') (⊢∶ty (⊢ty₁ q''))
--   ⊢MLTT→MLTT⁺ (∙Cong q₀ q₁ q₂ q₃ q₄) =
--     let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in ∙Cong
--       q'
--       q''
--       (⊢MLTT→MLTT⁺ q₂)
--       (⊢MLTT→MLTT⁺ q₃)
--       q₄
--       (⊢Ty₁ q')
--       (⊢Ty₁ q'')
--   ⊢MLTT→MLTT⁺ (𝐈𝐝TmCong q₀ q₁ q₂) = 𝐈𝐝TmCong
--     (⊢MLTT→MLTT⁺ q₀)
--     (⊢MLTT→MLTT⁺ q₁)
--     (⊢MLTT→MLTT⁺ q₂)
--   ⊢MLTT→MLTT⁺ (𝐫𝐞𝐟𝐥Cong q) =
--     let q'  = ⊢MLTT→MLTT⁺ q
--     in 𝐫𝐞𝐟𝐥Cong q' (⊢∶ty (⊢ty₁ q'))
--   ⊢MLTT→MLTT⁺ (𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
--      let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in 𝐉Cong
--       q'
--       q''
--       (⊢MLTT→MLTT⁺ q₂)
--       (⊢MLTT→MLTT⁺ q₃)
--       (⊢MLTT→MLTT⁺ q₄)
--       q₅
--       q₆
--       (⊢∶ty (⊢ty₁ q''))
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (⊢MLTT→MLTT⁺ q)
--   ⊢MLTT→MLTT⁺ (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅) =
--     let q'  = ⊢MLTT→MLTT⁺ q₂
--     in 𝐧𝐫𝐞𝐜Cong
--       (⊢MLTT→MLTT⁺ q₀)
--       (⊢MLTT→MLTT⁺ q₁)
--       q'
--       (⊢MLTT→MLTT⁺ q₃)
--       q₄
--       q₅
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (𝚷Beta q₀ q₁ q₂) =
--     let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in 𝚷Beta q' q'' q₂ (⊢∶ty q'') (⊢∶ty q')
--   ⊢MLTT→MLTT⁺ (𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄) =
--     let
--       q'  = ⊢MLTT→MLTT⁺ q₀
--       q'' = ⊢MLTT→MLTT⁺ q₁
--     in 𝐈𝐝Beta
--       q'
--       q''
--       (⊢MLTT→MLTT⁺ q₂)
--       q₃
--       q₄
--       (⊢∶ty q'')
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃) =
--     let q'  = ⊢MLTT→MLTT⁺ q₁
--     in 𝐍𝐚𝐭Beta₀
--       (⊢MLTT→MLTT⁺ q₀)
--       q'
--       q₂
--       q₃
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄) =
--     let q'  = ⊢MLTT→MLTT⁺ q₁
--     in 𝐍𝐚𝐭Beta₊
--       (⊢MLTT→MLTT⁺ q₀)
--       q'
--       (⊢MLTT→MLTT⁺ q₂)
--       q₃
--       q₄
--       (π₁ (∷⁻¹ q'))
--   ⊢MLTT→MLTT⁺ (𝚷Eta q₀ q₁) =
--     let q'  = ⊢MLTT→MLTT⁺ q₁
--     in 𝚷Eta (⊢MLTT→MLTT⁺ q₀) q' (π₁ (∷⁻¹ q'))

--   ⊢MLTT⁺→MLTT (⊢𝚷ty q₀ q₁ _) = ⊢𝚷ty
--     (⊢MLTT⁺→MLTT q₀)
--     q₁
--   ⊢MLTT⁺→MLTT (⊢𝐈𝐝ty q₀ q₁ _) = ⊢𝐈𝐝ty
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--   ⊢MLTT⁺→MLTT (⊢𝐔 q) = ⊢𝐔 (OkMLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐄𝐥 q) = ⊢𝐄𝐥 (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (TyRefl q) = TyRefl (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (TySymm q) = TySymm (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (TyTrans q q₁) = TyTrans
--     (⊢MLTT⁺→MLTT q)
--     (⊢MLTT⁺→MLTT q₁)
--   ⊢MLTT⁺→MLTT (𝚷TyCong q₀ q₁ q₂ _) = 𝚷TyCong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--   ⊢MLTT⁺→MLTT (𝐈𝐝TyCong q₀ q₁ q₂) = 𝐈𝐝TyCong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--   ⊢MLTT⁺→MLTT (＝𝐄𝐥 q) = ＝𝐄𝐥 (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐯 q₀ q₁) = ⊢𝐯 (OkMLTT⁺→MLTT q₀) q₁
--   ⊢MLTT⁺→MLTT (⊢conv q₀ q₁) = ⊢conv
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--   ⊢MLTT⁺→MLTT (⊢𝚷 q₀ q₁ q₂) = ⊢𝚷
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--   ⊢MLTT⁺→MLTT (⊢𝛌 q₀ q₁ _ _) = ⊢𝛌
--     (⊢MLTT⁺→MLTT q₀)
--     q₁
--   ⊢MLTT⁺→MLTT (⊢∙ q₀ q₁ q₂ q₃ _) = ⊢∙
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     q₃
--   ⊢MLTT⁺→MLTT (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--   ⊢MLTT⁺→MLTT (⊢𝐫𝐞𝐟𝐥 q _) = ⊢𝐫𝐞𝐟𝐥 (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐉 q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = ⊢𝐉
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     (⊢MLTT⁺→MLTT q₃)
--     (⊢MLTT⁺→MLTT q₄)
--     q₅
--     q₆
--   ⊢MLTT⁺→MLTT (⊢𝐍𝐚𝐭 q) = ⊢𝐍𝐚𝐭 (OkMLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (OkMLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ _) = ⊢𝐧𝐫𝐞𝐜
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     q₃
--     q₄
--   ⊢MLTT⁺→MLTT (TmRefl q) = TmRefl (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (TmSymm q) = TmSymm (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (TmTrans q₀ q₁) = TmTrans
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--   ⊢MLTT⁺→MLTT (＝conv q₀ q₁) = ＝conv
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--   ⊢MLTT⁺→MLTT (𝚷TmCong q₀ q₁ q₂ _) = 𝚷TmCong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--   ⊢MLTT⁺→MLTT (𝛌Cong q₀ q₁ q₂ _ _) = 𝛌Cong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--   ⊢MLTT⁺→MLTT (∙Cong q₀ q₁ q₂ q₃ q₄ _ _) = ∙Cong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     (⊢MLTT⁺→MLTT q₃)
--     q₄
--   ⊢MLTT⁺→MLTT (𝐈𝐝TmCong q₀ q₁ q₂) = 𝐈𝐝TmCong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--   ⊢MLTT⁺→MLTT (𝐫𝐞𝐟𝐥Cong q _) = 𝐫𝐞𝐟𝐥Cong (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = 𝐉Cong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     (⊢MLTT⁺→MLTT q₃)
--     (⊢MLTT⁺→MLTT q₄)
--     q₅
--     q₆
--   ⊢MLTT⁺→MLTT (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (⊢MLTT⁺→MLTT q)
--   ⊢MLTT⁺→MLTT (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ _) = 𝐧𝐫𝐞𝐜Cong
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     (⊢MLTT⁺→MLTT q₃)
--     q₄
--     q₅
--   ⊢MLTT⁺→MLTT (𝚷Beta q₀ q₁ q₂ _ _) = 𝚷Beta
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--   ⊢MLTT⁺→MLTT (𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄ _ _) = 𝐈𝐝Beta
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     q₃
--     q₄
--   ⊢MLTT⁺→MLTT (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ _) = 𝐍𝐚𝐭Beta₀
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     q₂
--     q₃
--   ⊢MLTT⁺→MLTT (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ _) = 𝐍𝐚𝐭Beta₊
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)
--     (⊢MLTT⁺→MLTT q₂)
--     q₃
--     q₄
--   ⊢MLTT⁺→MLTT (𝚷Eta q₀ q₁ _) = 𝚷Eta
--     (⊢MLTT⁺→MLTT q₀)
--     (⊢MLTT⁺→MLTT q₁)

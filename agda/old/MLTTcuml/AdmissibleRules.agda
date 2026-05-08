module MLTTcuml.AdmissibleRules where

open import Decidable
open import Empty
open import Equivalence
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

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Congruence properties of substitution
----------------------------------------------------------------------
congSbTy :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A A' : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ＝ A' ty)
  → ------------------------
  Γ' ⊢ σ * A ＝ σ' * A' ty

congSbTy q q' = TyTrans
  (sbJg (⊢sb₁ q) q')
  (＝sbTy q (⊢Ty₂ q') (⊢sb₁ q))

congSbTm :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → ---------------------------
  Γ' ⊢ σ * a ＝ σ' * a' ∶ σ * A

congSbTm q q' = TmTrans
  (sbJg (⊢sb₁ q) q')
  (＝sbTm q (⊢ty₂ q') (⊢sb₁ q))

----------------------------------------------------------------------
-- Substitution properties of concretion
----------------------------------------------------------------------
concTy :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
  (_ : Γ ⊢ a ∶ A)
  (_ : x # B)
  → --------------------------
  Γ ⊢ B ⟨ a ⟩ ty

concTy{Γ}{A}{a} B x q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ty)
    (ssb⟨⟩ x a B q₂)
    (sbJg (ssbUpdate q₁ ⊢A) q₀)

concTy² :
  {Γ : Cx}
  {A B : Ty}
  {a b : Tm}
  (C : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C ⟨ x ⸴ y ⟩ ty)
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B)
  (_ : x # C)
  (_ : y # C)
  → --------------------------------------
  Γ ⊢ C ⟨ a ⸴ b ⟩ ty

concTy²{Γ}{A}{B}{a}{b} C x y q₀ q₁ q₃ q₄ q₅
  with ∷ ⊢B (∷ ⊢A _) ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ty)
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
  → ------------------
  Γ ⊢ A ty

ok→ty (∷ q _) (isInNew refl) = wkJg _ q q
ok→ty (∷ q₀ q₁) (isInOld q₂) = wkJg _ q₀ (ok→ty q₁ q₂)

----------------------------------------------------------------------
-- Well-typed terms have well-formed types
----------------------------------------------------------------------
⊢∶ty :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A)
  → -------------
  Γ ⊢ A ty

⊢∶ty (⊢𝐯 q₀ q₁) = ok→ty q₀ q₁

⊢∶ty (⊢conv q₀ q₁) = ⊢Ty₂ q₁

⊢∶ty (⊢𝚷 q _ _) = ⊢𝐔 (⊢ok q)

⊢∶ty (⊢𝛌 _ (q₁ ∉∪ _) h₀ h₁) = ⊢𝚷ty h₁ q₁ h₀

⊢∶ty (⊢∙{B = B}{x = x} _ q₁ q₂ q₃ _) = concTy B x q₂ q₁ q₃

⊢∶ty (⊢𝐈𝐝 q _ _) = ⊢∶ty q

⊢∶ty (⊢𝐫𝐞𝐟𝐥 q _) = ⊢𝐈𝐝ty q q (⊢∶ty q)

⊢∶ty{Γ} (⊢𝐉{A}{C}{a}{b}{e = e}{x}{y} q₀ q₁ q₂ _ q₄ q₅ q₆ _ _) =
  concTy² C x y q₀ q₂ q₄' q₅ q₆
  where
  x#a : x # a
  x#a = ∉∪₁ (⊢# q₁ it)

  x#A : x # A
  x#A = ∉∪₂ (⊢# q₁ it)

  q₄' : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
  q₄' rewrite ssbFresh x b A x#A
      | ssbFresh x b a x#a
      | updateEq{ι}{b} x = q₄

⊢∶ty (⊢𝐍𝐚𝐭 q) = ⊢𝐔 q

⊢∶ty (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐄𝐥 (⊢𝐍𝐚𝐭 q)

⊢∶ty (⊢𝐬𝐮𝐜𝐜 q) = ⊢∶ty q

⊢∶ty (⊢𝐧𝐫𝐞𝐜{C = C}{x = x} _ _ q (q' ∉∪ _) _ h) =
  concTy C x h q q'

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
  (＝⊢ (TySymm q₁) (CxSymm q₀))
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
  (TyTrans q₁ (＝⊢ q₁' q₀))
  h₀
  h₁'

----------------------------------------------------------------------
-- Propositional equivalence of the type systems MLTT and MLTT+
----------------------------------------------------------------------

open MLTT renaming  (Ok to Ok⁻ ; _⊢_ to _⊢⁻_)
-- MLTT⁺ is already open

MLTT↔MLTT⁺ : ∀{Γ} → (Ok⁻ Γ ↔ Ok Γ) ∧ ∀{J} → (Γ ⊢⁻ J) ↔ (Γ ⊢ J)

MLTT↔MLTT⁺ =
  (↔i OkMLTT→MLTT⁺ OkMLTT⁺→MLTT)
  ,
  (↔i ⊢MLTT→MLTT⁺ ⊢MLTT⁺→MLTT)
  where
  OkMLTT→MLTT⁺ :
    {Γ : Cx}
    (_ : Ok⁻ Γ)
    → --------
    Ok Γ

  OkMLTT⁺→MLTT :
    {Γ : Cx}
    (_ : Ok Γ)
    → --------
    Ok⁻ Γ

  ⊢MLTT→MLTT⁺ :
    {Γ : Cx}
    {J : Jg}
    (_ : Γ ⊢⁻ J)
    → ----------
    Γ ⊢ J

  ⊢MLTT⁺→MLTT :
    {Γ : Cx}
    {J : Jg}
    (_ : Γ ⊢ J)
    → ---------
    Γ ⊢⁻ J

  OkMLTT→MLTT⁺ ◇ = ◇
  OkMLTT→MLTT⁺ (∷ q) =
    let q' = ⊢MLTT→MLTT⁺ q in  ∷ q' (⊢ok q')

  OkMLTT⁺→MLTT ◇ = ◇
  OkMLTT⁺→MLTT (∷ q _) = ∷ (⊢MLTT⁺→MLTT q)

  ⊢MLTT→MLTT⁺ (⊢𝚷ty q₀ q₁) =
    let q' = ⊢MLTT→MLTT⁺ q₀
    in ⊢𝚷ty q' q₁ (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (⊢𝐈𝐝ty q₀ q₁) =
    let q' = ⊢MLTT→MLTT⁺ q₀
    in ⊢𝐈𝐝ty q' (⊢MLTT→MLTT⁺ q₁) (⊢∶ty q')
  ⊢MLTT→MLTT⁺ (⊢𝐔 q) = ⊢𝐔 (OkMLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (⊢𝐄𝐥 q) = ⊢𝐄𝐥 (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (TyRefl q) = TyRefl (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (TySymm q) = TySymm (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (TyTrans q₀ q₁) = TyTrans
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
  ⊢MLTT→MLTT⁺ (𝚷TyCong q₀ q₁ q₂) =
    let q' = ⊢MLTT→MLTT⁺ q₀
    in 𝚷TyCong q' (⊢MLTT→MLTT⁺ q₁) q₂ (⊢Ty₁ q')
  ⊢MLTT→MLTT⁺ (𝐈𝐝TyCong q₀ q₁ q₂) = 𝐈𝐝TyCong
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
    (⊢MLTT→MLTT⁺ q₂)
  ⊢MLTT→MLTT⁺ (＝𝐄𝐥 q) = ＝𝐄𝐥 (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (⊢𝐯 q₀ q₁) = ⊢𝐯 (OkMLTT→MLTT⁺ q₀) q₁
  ⊢MLTT→MLTT⁺ (⊢conv q₀ q₁) = ⊢conv
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
  ⊢MLTT→MLTT⁺ (⊢𝚷 q₀ q₁ q₂) = ⊢𝚷
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
    q₂
  ⊢MLTT→MLTT⁺ (⊢𝛌 q₀ q₁) =
    let q' = ⊢MLTT→MLTT⁺ q₀
    in ⊢𝛌 q' q₁ (π₁ (∷⁻¹ q')) (⊢∶ty q')
  ⊢MLTT→MLTT⁺ (⊢∙ q₀ q₁ q₂ q₃) =
    let q' = ⊢MLTT→MLTT⁺ q₁
    in ⊢∙ (⊢MLTT→MLTT⁺ q₀) q' (⊢MLTT→MLTT⁺ q₂) q₃ (⊢∶ty q')
  ⊢MLTT→MLTT⁺ (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
    (⊢MLTT→MLTT⁺ q₂)
  ⊢MLTT→MLTT⁺ (⊢𝐫𝐞𝐟𝐥 q) =
    let q' = ⊢MLTT→MLTT⁺ q
    in ⊢𝐫𝐞𝐟𝐥 q' (⊢∶ty q')
  ⊢MLTT→MLTT⁺ (⊢𝐉 q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
    let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in ⊢𝐉
      q'
      q''
      (⊢MLTT→MLTT⁺ q₂)
      (⊢MLTT→MLTT⁺ q₃)
      (⊢MLTT→MLTT⁺ q₄)
      q₅
      q₆
      (⊢∶ty q'')
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (⊢𝐍𝐚𝐭 q) = ⊢𝐍𝐚𝐭 (OkMLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (OkMLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄) =
    let q'  = ⊢MLTT→MLTT⁺ q₁
    in ⊢𝐧𝐫𝐞𝐜
      (⊢MLTT→MLTT⁺ q₀)
      q'
      (⊢MLTT→MLTT⁺ q₂)
      q₃
      q₄
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (TmRefl q) = TmRefl (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (TmSymm q) = TmSymm (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (TmTrans q₀ q₁) = TmTrans
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
  ⊢MLTT→MLTT⁺ (＝conv q₀ q₁) = ＝conv
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
  ⊢MLTT→MLTT⁺ (𝚷TmCong q₀ q₁ q₂) =
    let q'  = ⊢MLTT→MLTT⁺ q₀
    in 𝚷TmCong q' (⊢MLTT→MLTT⁺ q₁) q₂ (⊢ty₁ q')
  ⊢MLTT→MLTT⁺ (𝛌Cong q₀ q₁ q₂) =
   let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in 𝛌Cong q' q'' q₂ (⊢Ty₁ q') (⊢∶ty (⊢ty₁ q''))
  ⊢MLTT→MLTT⁺ (∙Cong q₀ q₁ q₂ q₃ q₄) =
    let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in ∙Cong
      q'
      q''
      (⊢MLTT→MLTT⁺ q₂)
      (⊢MLTT→MLTT⁺ q₃)
      q₄
      (⊢Ty₁ q')
      (⊢Ty₁ q'')
  ⊢MLTT→MLTT⁺ (𝐈𝐝TmCong q₀ q₁ q₂) = 𝐈𝐝TmCong
    (⊢MLTT→MLTT⁺ q₀)
    (⊢MLTT→MLTT⁺ q₁)
    (⊢MLTT→MLTT⁺ q₂)
  ⊢MLTT→MLTT⁺ (𝐫𝐞𝐟𝐥Cong q) =
    let q'  = ⊢MLTT→MLTT⁺ q
    in 𝐫𝐞𝐟𝐥Cong q' (⊢∶ty (⊢ty₁ q'))
  ⊢MLTT→MLTT⁺ (𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
     let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in 𝐉Cong
      q'
      q''
      (⊢MLTT→MLTT⁺ q₂)
      (⊢MLTT→MLTT⁺ q₃)
      (⊢MLTT→MLTT⁺ q₄)
      q₅
      q₆
      (⊢∶ty (⊢ty₁ q''))
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (⊢MLTT→MLTT⁺ q)
  ⊢MLTT→MLTT⁺ (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅) =
    let q'  = ⊢MLTT→MLTT⁺ q₂
    in 𝐧𝐫𝐞𝐜Cong
      (⊢MLTT→MLTT⁺ q₀)
      (⊢MLTT→MLTT⁺ q₁)
      q'
      (⊢MLTT→MLTT⁺ q₃)
      q₄
      q₅
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (𝚷Beta q₀ q₁ q₂) =
    let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in 𝚷Beta q' q'' q₂ (⊢∶ty q'') (⊢∶ty q')
  ⊢MLTT→MLTT⁺ (𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄) =
    let
      q'  = ⊢MLTT→MLTT⁺ q₀
      q'' = ⊢MLTT→MLTT⁺ q₁
    in 𝐈𝐝Beta
      q'
      q''
      (⊢MLTT→MLTT⁺ q₂)
      q₃
      q₄
      (⊢∶ty q'')
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃) =
    let q'  = ⊢MLTT→MLTT⁺ q₁
    in 𝐍𝐚𝐭Beta₀
      (⊢MLTT→MLTT⁺ q₀)
      q'
      q₂
      q₃
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄) =
    let q'  = ⊢MLTT→MLTT⁺ q₁
    in 𝐍𝐚𝐭Beta₊
      (⊢MLTT→MLTT⁺ q₀)
      q'
      (⊢MLTT→MLTT⁺ q₂)
      q₃
      q₄
      (π₁ (∷⁻¹ q'))
  ⊢MLTT→MLTT⁺ (𝚷Eta q₀ q₁) =
    let q'  = ⊢MLTT→MLTT⁺ q₁
    in 𝚷Eta (⊢MLTT→MLTT⁺ q₀) q' (π₁ (∷⁻¹ q'))

  ⊢MLTT⁺→MLTT (⊢𝚷ty q₀ q₁ _) = ⊢𝚷ty
    (⊢MLTT⁺→MLTT q₀)
    q₁
  ⊢MLTT⁺→MLTT (⊢𝐈𝐝ty q₀ q₁ _) = ⊢𝐈𝐝ty
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
  ⊢MLTT⁺→MLTT (⊢𝐔 q) = ⊢𝐔 (OkMLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐄𝐥 q) = ⊢𝐄𝐥 (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (TyRefl q) = TyRefl (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (TySymm q) = TySymm (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (TyTrans q q₁) = TyTrans
    (⊢MLTT⁺→MLTT q)
    (⊢MLTT⁺→MLTT q₁)
  ⊢MLTT⁺→MLTT (𝚷TyCong q₀ q₁ q₂ _) = 𝚷TyCong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
  ⊢MLTT⁺→MLTT (𝐈𝐝TyCong q₀ q₁ q₂) = 𝐈𝐝TyCong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
  ⊢MLTT⁺→MLTT (＝𝐄𝐥 q) = ＝𝐄𝐥 (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐯 q₀ q₁) = ⊢𝐯 (OkMLTT⁺→MLTT q₀) q₁
  ⊢MLTT⁺→MLTT (⊢conv q₀ q₁) = ⊢conv
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
  ⊢MLTT⁺→MLTT (⊢𝚷 q₀ q₁ q₂) = ⊢𝚷
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
  ⊢MLTT⁺→MLTT (⊢𝛌 q₀ q₁ _ _) = ⊢𝛌
    (⊢MLTT⁺→MLTT q₀)
    q₁
  ⊢MLTT⁺→MLTT (⊢∙ q₀ q₁ q₂ q₃ _) = ⊢∙
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    q₃
  ⊢MLTT⁺→MLTT (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
  ⊢MLTT⁺→MLTT (⊢𝐫𝐞𝐟𝐥 q _) = ⊢𝐫𝐞𝐟𝐥 (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐉 q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = ⊢𝐉
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    (⊢MLTT⁺→MLTT q₃)
    (⊢MLTT⁺→MLTT q₄)
    q₅
    q₆
  ⊢MLTT⁺→MLTT (⊢𝐍𝐚𝐭 q) = ⊢𝐍𝐚𝐭 (OkMLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (OkMLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ _) = ⊢𝐧𝐫𝐞𝐜
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    q₃
    q₄
  ⊢MLTT⁺→MLTT (TmRefl q) = TmRefl (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (TmSymm q) = TmSymm (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (TmTrans q₀ q₁) = TmTrans
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
  ⊢MLTT⁺→MLTT (＝conv q₀ q₁) = ＝conv
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
  ⊢MLTT⁺→MLTT (𝚷TmCong q₀ q₁ q₂ _) = 𝚷TmCong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
  ⊢MLTT⁺→MLTT (𝛌Cong q₀ q₁ q₂ _ _) = 𝛌Cong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
  ⊢MLTT⁺→MLTT (∙Cong q₀ q₁ q₂ q₃ q₄ _ _) = ∙Cong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    (⊢MLTT⁺→MLTT q₃)
    q₄
  ⊢MLTT⁺→MLTT (𝐈𝐝TmCong q₀ q₁ q₂) = 𝐈𝐝TmCong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
  ⊢MLTT⁺→MLTT (𝐫𝐞𝐟𝐥Cong q _) = 𝐫𝐞𝐟𝐥Cong (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = 𝐉Cong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    (⊢MLTT⁺→MLTT q₃)
    (⊢MLTT⁺→MLTT q₄)
    q₅
    q₆
  ⊢MLTT⁺→MLTT (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (⊢MLTT⁺→MLTT q)
  ⊢MLTT⁺→MLTT (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ _) = 𝐧𝐫𝐞𝐜Cong
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    (⊢MLTT⁺→MLTT q₃)
    q₄
    q₅
  ⊢MLTT⁺→MLTT (𝚷Beta q₀ q₁ q₂ _ _) = 𝚷Beta
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
  ⊢MLTT⁺→MLTT (𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄ _ _) = 𝐈𝐝Beta
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    q₃
    q₄
  ⊢MLTT⁺→MLTT (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ _) = 𝐍𝐚𝐭Beta₀
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    q₂
    q₃
  ⊢MLTT⁺→MLTT (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ _) = 𝐍𝐚𝐭Beta₊
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)
    (⊢MLTT⁺→MLTT q₂)
    q₃
    q₄
  ⊢MLTT⁺→MLTT (𝚷Eta q₀ q₁ _) = 𝚷Eta
    (⊢MLTT⁺→MLTT q₀)
    (⊢MLTT⁺→MLTT q₁)

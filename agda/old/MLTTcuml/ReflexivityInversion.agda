module MLTTcuml.ReflexivityInversion where

open import Decidable
open import Empty
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

{- The Reflexivity rule says that Γ ⊢ A ty (resp. Γ ⊢ a ∶ A) implies
Γ ⊢ A ＝ A ty (resp. Γ ⊢ a ＝ a ∶ A). We will prove the converse, which
because of conversion symmetry/transitivity, is equivalent to proving
that Γ ⊢ A ＝ A' ty (resp. Γ ⊢ a ＝ a' ∶ A) implies Γ ⊢ A ty (resp.
Γ ⊢ a ∶ A). We do this by simultaneously proving symmterically that
Γ ⊢ A ＝ A' ty (resp. Γ ⊢ a ＝ a' ∶ A) implies Γ ⊢ A' ty
(resp. Γ ⊢ a' ∶ A).

Preservation of provable judgements under weakening and substitution
is needed in the proof and in particular the following corollaries of
those results. -}

-- We use the augmented version of the type system
open MLTT⁺

-- Change context up to conversion
＝⊢ι :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ' ＝ Γ)
  → -------------
  Γ' ⊢ˢ  ι ∶ Γ

＝⊢ι ◇ = ◇ ◇
＝⊢ι (∷{Γ}{A = A}{A'}{x} q₀ q₁ h₀ h₁) = ∷
  (wkSb x h₀ (＝⊢ι q₀))
  h₁
  (subst (λ B → (Γ ⸴ x ∶ A) ⊢ 𝐯 x ∶ B)
    (symm (sbUnit A'))
    (⊢conv (⊢𝐯 (∷ h₀ (⊢ok q₁)) (isInNew refl)) (wkJg x h₀ q₁)))

＝⊢ :
  {Γ Γ' : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  (_ : ⊢ Γ' ＝ Γ)
  → -------------
  Γ' ⊢ J

＝⊢{Γ' = Γ'}{J} q q' =
  subst (λ J' → Γ' ⊢ J') (sbUnitJg J) (sbJg (＝⊢ι q') q)

-- Concretion preserves typing and conversion
concTm :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩)
  (_ : Γ ⊢ a ∶ A)
  (_ : x # (B , b))
  → -----------------------------------
  Γ ⊢ b ⟨ a ⟩ ∶ B ⟨ a ⟩

concTm{Γ}{a = a} B b x p q (x#B ∉∪ x#b)
  with ∷ ⊢A _ ← ⊢ok p =
  subst₂ (λ z Z → Γ ⊢ z ∶ Z)
    (ssb⟨⟩ x a b x#b)
    (ssb⟨⟩ x a B x#B)
    (sbJg (ssbUpdate q ⊢A) p)

conc＝Ty :
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (B B' : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ty)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  (_ : x # (B , B'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⊢ a' ∶ A)
  (_ :  Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
  → ---------------------------------------
  Γ ⊢ B ⟨ a ⟩ ＝ B' ⟨ a' ⟩ ty

conc＝Ty{Γ}{A}{a}{a'} B B' x q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁ h₂
  with ∷ ⊢A _ ← ⊢ok q₀ = TyTrans q q'
  where
  q : Γ ⊢ B ⟨ a ⟩ ＝ B ⟨ a' ⟩ ty
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ty)
    (ssb⟨⟩ x a B q₂)
    (ssb⟨⟩ x a' B q₂)
    (＝sbTy (ssb＝Update q₁ ⊢A) h₂ (ssbUpdate h₀ ⊢A))

  q' : Γ ⊢ B ⟨ a' ⟩ ＝ B' ⟨ a' ⟩ ty
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ty)
    (ssb⟨⟩ x a' B q₂)
    (ssb⟨⟩ x a' B' q₂')
    (sbJg (ssbUpdate h₁ ⊢A) q₀)

conc＝Ty² :
  {Γ : Cx}
  {A B : Ty}
  {a a' b b' : Tm}
  (C C' : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢
    C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ty)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  (_ : Γ ⸴ x ∶ A ⊢ B ty)
  (_ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B)
  (_ : x # (C , C'))
  (_ : y # (C , C'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⊢ a' ∶ A)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B)
  (_ : Γ ⊢ b' ∶ (x ≔ a') * B)
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C ⟨ x ⸴ y ⟩ ty)
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C' ⟨ x ⸴ y ⟩ ty)
  → ---------------------------------------
  Γ ⊢ C ⟨ a ⸴ b ⟩ ＝ C' ⟨ a' ⸴ b' ⟩ ty

conc＝Ty²{Γ}{A}{B}{a}{a'}{b}{b'}
  C C' x y q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') (q₅ ∉∪ q₅') h₀ h₁ h₂ h₃ h₄ h₅
  with ∷ ⊢B (∷ ⊢A _) ← ⊢ok q₀ = TyTrans q q'
  where
  q : Γ ⊢ C ⟨ a ⸴ b ⟩ ＝ C ⟨ a' ⸴ b' ⟩ ty
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ty)
    (ssb⟨⟩² x y a b C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (ssb⟨⟩² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (＝sbTy (ssb＝Update² q₁ ⊢B q₃) h₄ (ssbUpdate² h₀ ⊢B h₂))

  q' : Γ ⊢ C ⟨ a' ⸴ b' ⟩ ＝ C' ⟨ a' ⸴ b' ⟩ ty
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ty)
    (ssb⟨⟩² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (ssb⟨⟩² x y a' b' C' q₄' (q₅' ∉∪ (∉∪₂ it)))
    (sbJg (ssbUpdate² h₁ ⊢B h₃) q₀)

----------------------------------------------------------------------
-- Reflexivity Inversion
----------------------------------------------------------------------
⊢Ty₁ :
  {Γ : Cx}
  {A A' : Ty}
  (_ : Γ ⊢ A ＝ A' ty)
  → -------------------
  Γ ⊢ A ty

⊢Ty₂ :
  {Γ : Cx}
  {A A' : Ty}
  (_ : Γ ⊢ A ＝ A' ty)
  → -------------------
  Γ ⊢ A' ty

⊢ty₁ :
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → -------------------
  Γ ⊢ a ∶ A

⊢ty₂ :
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → --------------------
  Γ ⊢ a' ∶ A

⊢Ty₁ (TyRefl q) = q

⊢Ty₁ (TySymm q) = ⊢Ty₂ q

⊢Ty₁ (TyTrans q _) = ⊢Ty₁ q

⊢Ty₁ (𝚷TyCong _ q₁ (q₂ ∉∪ _) q₃) = ⊢𝚷ty
  (⊢Ty₁ q₁)
  q₂
  q₃

⊢Ty₁ (𝐈𝐝TyCong q₀ q₁ q₂) = ⊢𝐈𝐝ty
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)
  (⊢Ty₁ q₀)

⊢Ty₁ (＝𝐄𝐥 q) = ⊢𝐄𝐥 (⊢ty₁ q)

⊢Ty₂ (TyRefl q) = q

⊢Ty₂ (TySymm q) = ⊢Ty₁ q

⊢Ty₂ (TyTrans _ q) = ⊢Ty₂ q

⊢Ty₂ (𝚷TyCong q₀ q₁ (_ ∉∪ q₂) q₃) = ⊢𝚷ty
  (＝⊢
    (⊢Ty₂ q₁)
    (∷ (CxRefl (⊢ok q₀)) (TySymm q₀) (⊢Ty₂ q₀) q₃))
  q₂
  (⊢Ty₂ q₀)

⊢Ty₂ (𝐈𝐝TyCong q₀ q₁ q₂) = ⊢𝐈𝐝ty
  (⊢conv (⊢ty₂ q₁) q₀)
  (⊢conv (⊢ty₂ q₂) q₀)
  (⊢Ty₂ q₀)

⊢Ty₂ (＝𝐄𝐥 q) = ⊢𝐄𝐥 (⊢ty₂ q)

⊢ty₁ (TmRefl q) = q

⊢ty₁ (TmSymm q) = ⊢ty₂ q

⊢ty₁ (TmTrans q _) = ⊢ty₁ q

⊢ty₁ (＝conv q₀ q₁) = ⊢conv (⊢ty₁ q₀) q₁

⊢ty₁ (𝚷TmCong q₀ q₁ (q₂ ∉∪ _) q₃) = ⊢𝚷
  q₃
  (⊢ty₁ q₁)
  q₂

⊢ty₁ (𝛌Cong q₀ q₁ (q₂ ∉∪ q₂' ∉∪ _) h₀ h₁) = ⊢𝛌
  (⊢ty₁ q₁)
  (q₂ ∉∪ q₂')
  h₀
  h₁

⊢ty₁ (∙Cong _ _ q₂ q₃ (q₄ ∉∪ _) h₀ h₁) = ⊢∙
  (⊢ty₁ q₂)
  (⊢ty₁ q₃)
  h₁
  q₄
  h₀

⊢ty₁ (𝐈𝐝TmCong q₀ q₁ q₂) = ⊢𝐈𝐝
  (⊢ty₁ q₀)
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)

⊢ty₁ (𝐫𝐞𝐟𝐥Cong q h) = ⊢𝐫𝐞𝐟𝐥
  (⊢ty₁ q)
  h

⊢ty₁ (𝐉Cong q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ _) (q₆ ∉∪ _) h₀ h₁) = ⊢𝐉
  (⊢Ty₁ q₀)
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)
  (⊢ty₁ q₃)
  (⊢ty₁ q₄)
  q₅
  q₆
  h₀
  h₁

⊢ty₁ (𝐬𝐮𝐜𝐜Cong q) = ⊢𝐬𝐮𝐜𝐜 (⊢ty₁ q)

⊢ty₁ (𝐧𝐫𝐞𝐜Cong _ q₁ q₂ q₃ (q₄ ∉∪ _ ∉∪ q₄' ∉∪ _) (q₅ ∉∪ _) h) = ⊢𝐧𝐫𝐞𝐜
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)
  (⊢ty₁ q₃)
  (q₄ ∉∪ q₄')
  q₅
  h

⊢ty₁ (𝚷Beta q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) = ⊢∙
  (⊢𝛌 q₀ (q₂ ∉∪ q₂') h₀ h₁) q₁ h₁ q₂ h₀

⊢ty₁ (𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄ h₀ h₁) = ⊢𝐉
  q₀ q₁ q₁ q₂ (⊢𝐫𝐞𝐟𝐥 q₁ h₀) q₃ q₄ h₀ h₁

⊢ty₁ (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ h) = ⊢𝐧𝐫𝐞𝐜
  q₀
  q₁
  (⊢𝐳𝐞𝐫𝐨 (⊢ok q₀))
  q₂
  q₃
  h

⊢ty₁ (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ h) = ⊢𝐧𝐫𝐞𝐜
  q₀
  q₁
  (⊢𝐬𝐮𝐜𝐜 q₂)
  q₃
  q₄
  h

⊢ty₁ (𝚷Eta q _ _) = q

⊢ty₂ (TmRefl q) = q

⊢ty₂ (TmSymm q) = ⊢ty₁ q

⊢ty₂ (TmTrans _ q) = ⊢ty₂ q

⊢ty₂ (＝conv q₀ q₁) = ⊢conv (⊢ty₂ q₀) q₁

⊢ty₂ (𝚷TmCong q₀ q₁ (_ ∉∪ q₂') h) = ⊢𝚷
  (⊢ty₂ q₀)
  (＝⊢
    (⊢ty₂ q₁)
    (∷ (CxRefl (⊢ok q₀)) (TySymm (＝𝐄𝐥 q₀)) (⊢𝐄𝐥 (⊢ty₂ q₀)) (⊢𝐄𝐥 h)))
  q₂'

⊢ty₂{Γ} (𝛌Cong{A}{A'}{B}{b}{b'}{x}
  q₀ q₁ (q₂ ∉∪ _ ∉∪ q₂') h₀ h₁) = ⊢conv q q'
  where
  e : ⊢ Γ ⸴ x ∶ A' ＝ Γ ⸴ x ∶ A
  e = ∷ (CxRefl (⊢ok h₀)) (TySymm q₀) (⊢Ty₂ q₀) h₀

  q : Γ ⊢ 𝛌 A' b' ∶ 𝚷 A' B
  q = ⊢𝛌
    (＝⊢ (⊢ty₂ q₁) e)
    (q₂ ∉∪ q₂')
    (⊢Ty₂ q₀)
    (＝⊢ h₁ e)

  q' : Γ ⊢ 𝚷 A' B ＝ 𝚷 A B ty
  q' = 𝚷TyCong
    (TySymm q₀)
    (＝⊢ (TyRefl h₁) e)
    (q₂ ∉∪ q₂)
    (⊢Ty₂ q₀)


⊢ty₂ (∙Cong{B = B}{B'}{x = x}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') h₀ _) = ⊢conv
  (⊢∙
    (⊢conv (⊢ty₂ q₂) (𝚷TyCong q₀ q₁ (q₄ ∉∪ q₄') h₀))
    (⊢conv (⊢ty₂ q₃) q₀)
    (＝⊢ (⊢Ty₂ q₁) (∷ (CxRefl (⊢ok q₀)) (TySymm q₀) (⊢Ty₂ q₀) h₀))
    q₄'
    (⊢Ty₂ q₀))
  (TySymm (conc＝Ty B B' x
    q₁ q₃ (q₄ ∉∪ q₄') (⊢ty₁ q₃) (⊢ty₂ q₃) (⊢Ty₁ q₁)))

⊢ty₂ (𝐈𝐝TmCong q q₁ q₂) = ⊢𝐈𝐝
  (⊢ty₂ q)
  (⊢conv (⊢ty₂ q₁) (＝𝐄𝐥 q))
  (⊢conv (⊢ty₂ q₂) (＝𝐄𝐥 q))

⊢ty₂ (𝐫𝐞𝐟𝐥Cong q h) = ⊢conv
  (⊢𝐫𝐞𝐟𝐥 (⊢ty₂ q) h)
  (𝐈𝐝TyCong (TyRefl h) (TmSymm q) (TmSymm q))

⊢ty₂{Γ} (𝐉Cong{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}{x}{y}
  q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') h₀ h₁) =
  ⊢conv r (TySymm s)
  where
  Γok : Ok Γ
  Γok = ⊢ok h₀

  x#A : x # A
  x#A = ⊢# h₀ it

  x#a : x # a
  x#a = ∉∪₁ (⊢# q₁ it)

  r₁ : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
  r₁ rewrite ssbFresh x b A x#A
     | ssbFresh x b a x#a
     | updateEq{ι}{b} x = ⊢ty₁ q₄

  r₂ :  Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A a b' ty
  r₂ = 𝐈𝐝TyCong (TyRefl h₀) (TmRefl (⊢ty₁ q₁)) q₂

  r₁' : Γ ⊢ e' ∶ (x ≔ b') * 𝐈𝐝 A a (𝐯 x)
  r₁' rewrite ssbFresh x b' A x#A
      | ssbFresh x b' a x#a
      | updateEq{ι}{b'} x = ⊢conv (⊢ty₂ q₄) r₂

  r₁'' : Γ ⊢ e ＝ e' ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x)
  r₁'' rewrite ssbFresh x b A x#A
      | ssbFresh x b a x#a
      | updateEq{ι}{b} x = q₄

  s : Γ ⊢ C ⟨ b ⸴ e ⟩ ＝ C' ⟨ b' ⸴ e' ⟩ ty
  s = conc＝Ty² C C' x y
    q₀ q₂ h₁ r₁'' (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') (⊢ty₁ q₂)
    (⊢ty₂ q₂) r₁ r₁' (⊢Ty₁ q₀) (⊢Ty₂ q₀)

  s₁ : Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ (x ≔ a) * 𝐈𝐝 A a (𝐯 x)
  s₁ rewrite ssbFresh x a A x#A
     | ssbFresh x a a x#a
     | updateEq{ι}{a} x = ⊢𝐫𝐞𝐟𝐥 (⊢ty₁ q₁) h₀

  s₁' : Γ ⊢ 𝐫𝐞𝐟𝐥 a' ∶ (x ≔ a') * 𝐈𝐝 A a (𝐯 x)
  s₁' rewrite ssbFresh x a' A x#A
     | ssbFresh x a' a x#a
     | updateEq{ι}{a'} x = ⊢conv
      (⊢𝐫𝐞𝐟𝐥 (⊢ty₂ q₁) h₀)
       (𝐈𝐝TyCong (TyRefl h₀) (TmSymm q₁) (TmRefl (⊢ty₂ q₁)))

  s₁'' : Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ (x ≔ a) * 𝐈𝐝 A a (𝐯 x)
  s₁'' rewrite ssbFresh x a A x#A
      | ssbFresh x a a x#a
      | updateEq{ι}{a} x = 𝐫𝐞𝐟𝐥Cong q₁ h₀

  s' : Γ ⊢ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ＝ C' ⟨ a' ⸴ 𝐫𝐞𝐟𝐥 a' ⟩ ty
  s' = conc＝Ty² C C' x y q₀ q₁ h₁ s₁'' (q₅ ∉∪ q₅')
    (q₆ ∉∪ q₆') (⊢ty₁ q₁) (⊢ty₂ q₁) s₁ s₁' (⊢Ty₁ q₀) (⊢Ty₂ q₀)

  r₂' :  Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A a' b' ty
  r₂' = 𝐈𝐝TyCong (TyRefl h₀) q₁ q₂

  r₃ : Γ ⸴ x ∶ A ⊢ 𝐈𝐝 A a' (𝐯 x) ty
  r₃ = ⊢𝐈𝐝ty
    (wkJg x h₀ (⊢ty₂ q₁))
    (⊢𝐯 (∷ h₀ Γok) (isInNew refl))
    (wkJg x h₀ h₀)

  r₃' : Γ ⸴ x ∶ A ⊢ 𝐈𝐝 A a' (𝐯 x) ＝ 𝐈𝐝 A a (𝐯 x) ty
  r₃' = 𝐈𝐝TyCong
    (TyRefl (wkJg x h₀ h₀))
    (TmSymm (wkJg x h₀ q₁))
    (TmRefl (⊢𝐯 (∷ h₀ Γok) (isInNew refl)))

  r₄ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a' (𝐯 x) ⊢ C' ⟨ x ⸴ y ⟩ ty
  r₄ = ＝⊢
    (⊢Ty₂ q₀)
    (∷ (∷ (CxRefl Γok) (TyRefl h₀) h₀ h₀) r₃' r₃ h₁)

  r : Γ ⊢ 𝐉 C' a' b' c' e' ∶ C' ⟨ b' ⸴ e' ⟩
  r = ⊢𝐉 r₄ (⊢ty₂ q₁) (⊢ty₂ q₂) (⊢conv (⊢ty₂ q₃) s')
    (⊢conv (⊢ty₂ q₄) r₂') q₅' q₆' h₀ r₃

⊢ty₂ (𝐬𝐮𝐜𝐜Cong q) = ⊢𝐬𝐮𝐜𝐜 (⊢ty₂ q)

⊢ty₂{Γ} (𝐧𝐫𝐞𝐜Cong{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') h) =
  ⊢conv r₀ (TySymm r₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₁

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ty
  ⊢N = ⊢𝐄𝐥 (⊢𝐍𝐚𝐭 Γok)

  r₂ : Γ ⊢ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ＝ C' ⟨ 𝐳𝐞𝐫𝐨 ⟩ ty
  r₂ = conc＝Ty C C' x q₀
    (TmRefl (⊢𝐳𝐞𝐫𝐨 Γok)) (q₄ ∉∪ q₄')
    (⊢𝐳𝐞𝐫𝐨 Γok) (⊢𝐳𝐞𝐫𝐨 Γok) (⊢Ty₁ q₀)

  s : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ˢ (x ≔ 𝐬𝐮𝐜𝐜 (𝐯 x)) ∶ Γ ⸴ x ∶ 𝐍𝐚𝐭
  s = sbUpdate
    (wkSb x (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 Γok)) (⊢ι Γok))
    (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 Γok))
    (⊢𝐬𝐮𝐜𝐜 (⊢𝐯 (∷ ⊢N Γok) (isInNew refl)))

  r₂' : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢
    C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ＝ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ty
  r₂' = subst₂ (λ D D' → Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ D ＝ D' ty)
    (ssb⟨⟩ x (𝐬𝐮𝐜𝐜 (𝐯 x)) C q₄)
    (ssb⟨⟩ x (𝐬𝐮𝐜𝐜 (𝐯 x)) C' q₄')
    (sbJg s q₀)

  r₃ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
    c₊' ⟨ x ⸴ y ⟩ ∶ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩
  r₃ = ⊢conv (⊢ty₂ q₂) (wkJg y (⊢Ty₁ q₀) r₂')

  r₃' : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C' ⟨ x ⟩) ⊢
    c₊' ⟨ x ⸴ y ⟩ ∶ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩
  r₃' = ＝⊢
    r₃
    (∷
      (∷
        (CxRefl Γok)
        (TyRefl ⊢N) ⊢N ⊢N)
      (TySymm q₀)
      (⊢Ty₂ q₀)
      (⊢Ty₁ q₀))

  r₀ : Γ ⊢ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C' ⟨ a' ⟩
  r₀ = ⊢𝐧𝐫𝐞𝐜
    (⊢conv (⊢ty₂ q₁) r₂)
    r₃'
    (⊢ty₂ q₃)
    (q₄' ∉∪ q₄''')
    q₅'
    (⊢Ty₂ q₀)

  r₁ : Γ ⊢ C ⟨ a ⟩ ＝ C' ⟨ a' ⟩ ty
  r₁ = conc＝Ty C C' x q₀ q₃ (q₄ ∉∪ q₄') (⊢ty₁ q₃) (⊢ty₂ q₃) h

⊢ty₂ (𝚷Beta{B = B}{b}{x} q₀ q₁ q₂ q₃ q₄) = concTm B b x q₀ q₁ q₂

⊢ty₂ (𝐈𝐝Beta _ _ q _ _ _ _) = q

⊢ty₂ (𝐍𝐚𝐭Beta₀ q _ _ _ _) = q

⊢ty₂{Γ} (𝐍𝐚𝐭Beta₊{C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h) = subst₂ (λ d D → Γ ⊢ d ∶ D)
  (ssb⟨⟩² x y a (𝐧𝐫𝐞𝐜 C c₀ c₊ a) c₊ q₃' (q₄ ∉∪ (∉∪₂ it)))
  e
  (sbJg s q₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₀

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ty
  ⊢N = ⊢𝐄𝐥 (⊢𝐍𝐚𝐭 Γok)

  r : Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ (x ≔ a) * C ⟨ x ⟩
  r rewrite ssb⟨⟩ x a C q₃ = ⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h

  s : Γ ⊢ˢ (y := 𝐧𝐫𝐞𝐜 C c₀ c₊ a)(x ≔ a) ∶ Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩
  s = sbUpdate (ssbUpdate q₂ ⊢N) h r

  y#C : y # C
  y#C = ⊆∉ (⟨⟩supp C 𝐳𝐞𝐫𝐨) (∉∪₂ (⊢# q₀ (∉∪₁ it)))

  y# : y #  C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩
  y# = ⊆∉ (supp⟨⟩ C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ ∉∪₂ it ∉∪ ∉∅)

  e : (y := 𝐧𝐫𝐞𝐜 C c₀ c₊ a)(x ≔ a) *  C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
    C ⟨ 𝐬𝐮𝐜𝐜 a  ⟩
  e rewrite updateFresh (x ≔ a) y (𝐧𝐫𝐞𝐜 C c₀ c₊ a) (C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩) y#
    | sb⟨⟩ (x ≔ a) C (𝐬𝐮𝐜𝐜 (𝐯 x))
    | ssbFresh x a C q₃
    | updateEq{ι}{a} x = refl

⊢ty₂{Γ} (𝚷Eta{A}{B}{b}{x} q₀ q₁ h)
  with  (y , y#B ∉∪ y#) ← fresh (B , (Γ , x)) = ⊢𝛌
    q
    (x#B ∉∪ (#abs x (b ∙[ A , B ] 𝐯 x)))
    h
    q₁
  where
  instance
    _ : y # (Γ , x)
    _ = y#

  x#B : x # B
  x#B = ∉∪₁ (∉∪₂ (∉∪₂ (⊢# q₀ it)))

  q : (Γ ⸴ x ∶ A) ⊢ (x ． b ∙[ A , B ] 𝐯 x)⟨ x ⟩ ∶ B ⟨ x ⟩
  q rewrite concAbs' x (b ∙[ A , B ] 𝐯 x) = ⊢∙{x = y}
    (wkJg x h q₀)
    (⊢𝐯 (⊢ok q₁) (isInNew refl))
    (subst₂ (λ A' C → Γ ⸴ x ∶ A ⸴ y ∶ A' ⊢ C ty)
      (sbUnit A)
      (ssb⟨⟩ x (𝐯 y) B x#B)
      (sbJg (liftSb (wkSb x h (⊢ι (⊢ok q₀))) h
        (wkJg x h
          (subst (λ A' → Γ ⊢ A' ty)
            (symm (sbUnit A)) h))) q₁))
    y#B
    (wkJg x h h)

----------------------------------------------------------------------
-- Reflexivity Inversion for substitutions
----------------------------------------------------------------------
⊢sb₁ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  (_ : Γ ⊢ˢ σ ＝ σ' ∶ Γ')
  → ---------------------
  Γ ⊢ˢ σ ∶ Γ'

⊢sb₁ (◇ q) = ◇ q
⊢sb₁ (∷ q₀ q₁ q₂) = ∷ (⊢sb₁ q₀) q₁ (⊢ty₁ q₂)

⊢sb₂ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  (_ : Γ ⊢ˢ σ ＝ σ' ∶ Γ')
  → ---------------------
  Γ ⊢ˢ σ' ∶ Γ'

⊢sb₂ (◇ q) = ◇ q
⊢sb₂ (∷ q₀ q₁ q₂) = ∷
  (⊢sb₂ q₀)
  q₁
  (⊢conv (⊢ty₂ q₂) (＝sbTy q₀ q₁ (⊢sb₁ q₀)))

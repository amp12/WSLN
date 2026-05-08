module ETT.ReflexivityInversion where

open import Decidable
open import Empty
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem
open import ETT.ContextConversion
open import ETT.Ok
open import ETT.WellScoped
open import ETT.Renaming
open import ETT.Substitution

{- The Reflexivity rule says that Γ ⊢ a ∶ A ⦂ l implies
Γ ⊢ a ＝ a ∶ A ⦂ l. We will prove the converse, which because of
conversion symmetry/transitivity, is equivalent to proving that
Γ ⊢ a ＝ a' ∶ A ⦂ l implies Γ ⊢ a ∶ A ⦂l. We do this by
simultaneously proving that Γ ⊢ a ＝ a' ∶ A ⦂ l also implies
Γ ⊢ a' ∶ A ⦂ l.

Preservation of provable judgements under weakening and substitution
is needed in the proof and in particular the following corollaries of
those results. -}

-- Change context up to conversion
＝⊢ι :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ' ＝ Γ)
  → -------------
  Γ' ⊢ˢ  ι ∶ Γ

＝⊢ι ◇ = ◇ ◇
＝⊢ι (∷{l}{Γ}{A = A}{A'}{x} q₀ q₁ h₀ h₁) = ∷
  (wkSb x h₀ (＝⊢ι q₀))
  h₁
  (subst (λ B → (Γ ⸴ x ∶ A ⦂ l) ⊢ 𝐯 x ∶ B ⦂ l)
    (symm (sbUnit A'))
    (⊢conv (⊢𝐯 (∷⁻ h₀) isInNew) (wkJg x h₀ q₁)))

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
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : x # (B , b))
  → --------------------------------------------
  Γ ⊢ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ⦂ l'

concTm{l' = l'}{Γ}{a = a} B b x p q (x#B ∉∪ x#b)
  with ∷ ⊢A _ ← ⊢ok p =
  subst₂ (λ z Z → Γ ⊢ z ∶ Z ⦂ l')
    (ssb⟨⟩ x a b x#b)
    (ssb⟨⟩ x a B x#B)
    (sbJg (ssbUpdate q ⊢A) p)

conc＝Ty :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (B B' : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ⦂ l')
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : x # (B , B'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ a' ∶ A ⦂ l)
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
  → -----------------------------------------
  Γ ⊢ B ⟨ a ⟩ ＝ B' ⟨ a' ⟩ ⦂ l'

conc＝Ty{l' = l'}{Γ}{A}{a}{a'} B B' x q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁ h₂
  with ∷ ⊢A _ ← ⊢ok q₀ = TyTrans q q'
  where
  q : Γ ⊢ B ⟨ a ⟩ ＝ B ⟨ a' ⟩ ⦂ l'
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l')
    (ssb⟨⟩ x a B q₂)
    (ssb⟨⟩ x a' B q₂)
    (＝sbTy (ssb＝Update q₁ ⊢A) h₂ (ssbUpdate h₀ ⊢A))

  q' : Γ ⊢ B ⟨ a' ⟩ ＝ B' ⟨ a' ⟩ ⦂ l'
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l')
    (ssb⟨⟩ x a' B q₂)
    (ssb⟨⟩ x a' B' q₂')
    (sbJg (ssbUpdate h₁ ⊢A) q₀)

conc＝Ty² :
  {l l' l'' : Lvl}
  {Γ : Cx}
  {A B : Ty}
  {a a' b b' : Tm}
  (C C' : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ⦂ l'')
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⦂ l')
  (_ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B ⦂ l')
  (_ : x # (C , C'))
  (_ : y # (C , C'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ a' ∶ A ⦂ l)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B ⦂ l')
  (_ : Γ ⊢ b' ∶ (x ≔ a') * B ⦂ l')
  (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢ C ⟨ x ⸴ y ⟩ ⦂ l'')
  (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢ C' ⟨ x ⸴ y ⟩ ⦂ l'')
  → ------------------------------------------------------
  Γ ⊢ C ⟨ a ⸴ b ⟩ ＝ C' ⟨ a' ⸴ b' ⟩ ⦂ l''

conc＝Ty²{l'' = l''}{Γ}{A}{B}{a}{a'}{b}{b'}
  C C' x y q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') (q₅ ∉∪ q₅') h₀ h₁ h₂ h₃ h₄ h₅
  with ∷ ⊢B (∷ ⊢A _) ← ⊢ok q₀ = TyTrans q q'
  where
  q : Γ ⊢ C ⟨ a ⸴ b ⟩ ＝ C ⟨ a' ⸴ b' ⟩ ⦂ l''
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l'')
    (ssb⟨⟩² x y a b C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (ssb⟨⟩² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (＝sbTy (ssb＝Update² q₁ ⊢B q₃) h₄ (ssbUpdate² h₀ ⊢B h₂))

  q' : Γ ⊢ C ⟨ a' ⸴ b' ⟩ ＝ C' ⟨ a' ⸴ b' ⟩ ⦂ l''
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l'')
    (ssb⟨⟩² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (ssb⟨⟩² x y a' b' C' q₄' (q₅' ∉∪ (∉∪₂ it)))
    (sbJg (ssbUpdate² h₁ ⊢B h₃) q₀)

----------------------------------------------------------------------
-- Reflexivity Inversion
----------------------------------------------------------------------
⊢Ty₁ :
  {l : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  → -------------------
  Γ ⊢ A ⦂ l

⊢Ty₂ :
  {l : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  → -------------------
  Γ ⊢ A' ⦂ l

⊢ty₁ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  → -----------------------
  Γ ⊢ a ∶ A ⦂ l

⊢ty₂ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  → -----------------------
  Γ ⊢ a' ∶ A ⦂ l

⊢Ty₁ (TyRefl q) = q

⊢Ty₁ (TySymm q) = ⊢Ty₂ q

⊢Ty₁ (TyTrans q _) = ⊢Ty₁ q

⊢Ty₁ (𝚷Cong _ q₁ (q₂ ∉∪ _) q₃) = ⊢𝚷 q₃ (⊢Ty₁ q₁) q₂

⊢Ty₁ (𝐈𝐝Cong q₀ q₁ q₂) = ⊢𝐈𝐝
  (⊢ty₁ q₀)
  (⊢ty₁ q₁)
  q₂

⊢Ty₁ (=Tm→Ty q) = Tm→Ty (⊢ty₁ q)

⊢Ty₂ (TyRefl q) = q

⊢Ty₂ (TySymm q) = ⊢Ty₁ q

⊢Ty₂ (TyTrans _ q) = ⊢Ty₂ q

⊢Ty₂ (𝚷Cong q₀ q₁ (_ ∉∪ q₂') h) = ⊢𝚷
  (⊢Ty₂ q₀)
  (＝⊢
    (⊢Ty₂ q₁)
    (∷ (CxRefl (⊢ok q₀)) (TySymm q₀) (⊢Ty₂ q₀) h))
  q₂'

⊢Ty₂ (𝐈𝐝Cong q₀ q₁ q₂) = ⊢𝐈𝐝
  (⊢ty₂ q₀)
  (⊢ty₂ q₁)
  q₂

⊢Ty₂ (=Tm→Ty q) = Tm→Ty (⊢ty₂ q)

⊢ty₁ (TmRefl q) = q

⊢ty₁ (TmSymm q) = ⊢ty₂ q

⊢ty₁ (TmTrans q _) = ⊢ty₁ q

⊢ty₁ (＝conv q₀ q₁) = ⊢conv (⊢ty₁ q₀) q₁

⊢ty₁ (=Ty→Tm q) = Ty→Tm (⊢Ty₁ q)

⊢ty₁ (⊢Reflect q _ _ _) = q

⊢ty₁ (𝛌Cong q₀ (q₁ ∉∪ q₁' ∉∪ _) h₀ h₁) = ⊢𝛌
  (⊢ty₁ q₀)
  (q₁ ∉∪ q₁')
  h₀
  h₁

⊢ty₁ (∙Cong q q₁ q₂ h₀ h₁) = ⊢∙
  (⊢ty₁ q)
  (⊢ty₁ q₁)
  h₁
  q₂
  h₀

⊢ty₁ (𝐬𝐮𝐜𝐜Cong q) = ⊢𝐬𝐮𝐜𝐜 (⊢ty₁ q)

⊢ty₁ (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ (q₄ ∉∪ _ ∉∪ q₄' ∉∪ _) (q₅ ∉∪ _) h) = ⊢𝐧𝐫𝐞𝐜
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)
  (⊢ty₁ q₃)
  (q₄ ∉∪ q₄')
  q₅
  h

⊢ty₁ (𝚷Beta{B = B} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) = ⊢∙{B = B}
  (⊢𝛌 q₀ (q₂ ∉∪ q₂') h₀ h₁)
  q₁
  h₁
  q₂
  h₀

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

⊢ty₁ (UIP _ _ q _) = q

⊢ty₂ (TmRefl q) = q

⊢ty₂ (TmSymm q) = ⊢ty₁ q

⊢ty₂ (TmTrans _ q) = ⊢ty₂ q

⊢ty₂ (＝conv q₀ q₁) = ⊢conv (⊢ty₂ q₀) q₁

⊢ty₂ (=Ty→Tm q) = Ty→Tm (⊢Ty₂ q)

⊢ty₂ (⊢Reflect _ q _ _) = q

⊢ty₂ (𝛌Cong q₁ (q₂ ∉∪ _ ∉∪ q₂') h₀ h₁) =  ⊢𝛌
  (⊢ty₂ q₁)
  (q₂ ∉∪ q₂')
  h₀
  h₁

⊢ty₂{Γ = Γ} (∙Cong{l' = l'}{B = B}{a}{a'}{b' = b'}{x} q₀ q₁ q₂ q₃ h) =
  ⊢conv q q'
  where
  q : Γ ⊢ b' ∙ a' ∶ B ⟨ a' ⟩ ⦂ l'
  q = ⊢∙ (⊢ty₂ q₀) (⊢ty₂ q₁) h q₂ q₃

  q' : Γ ⊢ B ⟨ a' ⟩ ＝ B ⟨ a ⟩ ⦂ l'
  q' = TySymm
    (conc＝Ty B B x (TyRefl h) q₁ (q₂ ∉∪ q₂) (⊢ty₁ q₁) (⊢ty₂ q₁) h)

⊢ty₂ (𝐬𝐮𝐜𝐜Cong q) = ⊢𝐬𝐮𝐜𝐜 (⊢ty₂ q)

⊢ty₂{Γ = Γ} (𝐧𝐫𝐞𝐜Cong{l}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') h) =
  ⊢conv r₀ (TySymm r₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₁

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ⦂ 0
  ⊢N = ⊢𝐍𝐚𝐭 Γok

  r₂ : Γ ⊢ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ＝ C' ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l
  r₂ = conc＝Ty C C' x q₀ (TmRefl (⊢𝐳𝐞𝐫𝐨 Γok))
    (q₄ ∉∪ q₄') (⊢𝐳𝐞𝐫𝐨 Γok) (⊢𝐳𝐞𝐫𝐨 Γok) h

  s : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢ˢ (x ≔ 𝐬𝐮𝐜𝐜 (𝐯 x)) ∶ Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0
  s = sbUpdate
    (wkSb x ⊢N (⊢ι Γok))
    (⊢𝐬𝐮𝐜𝐜 (⊢𝐯 (∷⁻ ⊢N) isInNew))
    ⊢N

  r₂' : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢
    C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ＝ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l
  r₂' = subst₂ (λ D D' → (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ D ＝ D' ⦂ l)
    (ssb⟨⟩ x (𝐬𝐮𝐜𝐜 (𝐯 x)) C q₄)
    (ssb⟨⟩ x (𝐬𝐮𝐜𝐜 (𝐯 x)) C' q₄')
    (sbJg s q₀)

  r₃ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
    c₊' ⟨ x ⸴ y ⟩ ∶ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l
  r₃ = ⊢conv (⊢ty₂ q₂) (wkJg y (⊢Ty₁ q₀) r₂')

  r₃' : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C' ⟨ x ⟩ ⦂ l) ⊢
    c₊' ⟨ x ⸴ y ⟩ ∶ C' ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l
  r₃' = ＝⊢
    r₃
    (∷
      (∷
        (CxRefl Γok)
        (TyRefl ⊢N) ⊢N ⊢N)
      (TySymm q₀)
      (⊢Ty₂ q₀)
      (⊢Ty₁ q₀))

  r₀ : Γ ⊢ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C' ⟨ a' ⟩ ⦂ l
  r₀ = ⊢𝐧𝐫𝐞𝐜
    (⊢conv (⊢ty₂ q₁) r₂)
    r₃'
    (⊢ty₂ q₃)
    (q₄' ∉∪ q₄''')
    q₅'
    (⊢Ty₂ q₀)

  r₁ : Γ ⊢ C ⟨ a ⟩ ＝ C' ⟨ a' ⟩ ⦂ l
  r₁ = conc＝Ty C C' x q₀ q₃ (q₄ ∉∪ q₄') (⊢ty₁ q₃) (⊢ty₂ q₃) h

⊢ty₂ (𝚷Beta{B = B}{b}{x} q₀ q₁ q₂ _ _) = concTm B b x q₀ q₁ q₂

⊢ty₂ (𝐍𝐚𝐭Beta₀ q _ _ _ _) = q

⊢ty₂{Γ = Γ} (𝐍𝐚𝐭Beta₊{l}{C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h) = subst₂ (λ d D → Γ ⊢ d ∶ D ⦂ l)
  (ssb⟨⟩² x y a (𝐧𝐫𝐞𝐜 C c₀ c₊ a) c₊ q₃' (q₄ ∉∪ (∉∪₂ it)))
  e
  (sbJg s q₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₀

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ⦂ 0
  ⊢N = ⊢𝐍𝐚𝐭 Γok

  r : Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ (x ≔ a) * C ⟨ x ⟩ ⦂ l
  r rewrite ssb⟨⟩ x a C q₃ = ⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h

  s : Γ ⊢ˢ (y := 𝐧𝐫𝐞𝐜 C c₀ c₊ a)(x ≔ a) ∶ Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l
  s = sbUpdate (ssbUpdate q₂ ⊢N) r h

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

⊢ty₂{Γ = Γ} (𝚷Eta{l}{l'}{A}{B}{b}{x} q₀ q₁ h)
  with  (y , y#B ∉∪ y#) ← fresh (B , (Γ , x)) = ⊢𝛌
    q
    (x#B ∉∪ (#abs x (b ∙ 𝐯 x)))
    h
    q₁
  where
  instance
    _ : y # (Γ , x)
    _ = y#

  x#B : x # B
  x#B = ∉∪₁ (∉∪₂ (∉∪₂ (⊢# q₀ it)))

  q : (Γ ⸴ x ∶ A ⦂ l) ⊢ (x ． b ∙ 𝐯 x)⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l'
  q rewrite concAbs' x (b ∙ 𝐯 x) = ⊢∙{x = y}
    (wkJg x h q₀)
    (⊢𝐯 (⊢ok q₁) isInNew )
    (subst₂ (λ A' C → (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ A' ⦂ l) ⊢ C ⦂ l')
      (sbUnit A)
      (ssb⟨⟩ x (𝐯 y) B x#B)
      (sbJg (liftSb (wkSb x h (⊢ι (⊢ok q₀))) h
        (wkJg x h
          (subst (λ A' → Γ ⊢ A' ⦂ l)
            (symm (sbUnit A)) h))) q₁))
    y#B
    (wkJg x h h)

⊢ty₂ (UIP q₀ q₁ q₂ q₃) = ⊢conv
  (⊢𝐫𝐞𝐟𝐥 q₀ q₃)
  (𝐈𝐝Cong
    (TmRefl q₀)
    (⊢Reflect q₀ q₁ q₂ q₃)
    q₃)

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

----------------------------------------------------------------------
-- Congruence property of substitution
----------------------------------------------------------------------
congSbTm :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  → -------------------------------
  Γ' ⊢ σ * a ＝ σ' * a' ∶ σ * A ⦂ l

congSbTm q q' = TmTrans
  (sbJg (⊢sb₁ q) q')
  (＝sbTm q (⊢ty₂ q') (⊢sb₁ q))

----------------------------------------------------------------------
-- Substitution properties of concretion
----------------------------------------------------------------------
concTy :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : x # B)
  → -----------------------------------
  Γ ⊢ B ⟨ a ⟩ ⦂ l'

concTy{l' = l'}{Γ}{A}{a} B x q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ⦂ l')
    (ssb⟨⟩ x a B q₂)
    (sbJg (ssbUpdate q₁ ⊢A) q₀)

concTy² :
  {l l' l'' : Lvl}
  {Γ : Cx}
  {A B : Ty}
  {a b : Tm}
  (C : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    C ⟨ x ⸴ y ⟩ ⦂ l'')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B ⦂ l')
  (_ : x # C)
  (_ : y # C)
  → ---------------------------------
  Γ ⊢ C ⟨ a ⸴ b ⟩ ⦂ l''

concTy²{l'' = l''}{Γ}{A}{B}{a}{b} C x y q₀ q₁ q₃ q₄ q₅
  with ∷ ⊢B (∷ ⊢A _) ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ⦂ l'')
    (ssb⟨⟩² x y a b C q₄ (q₅ ∉∪ (∉∪₂ it)))
    (sbJg (ssbUpdate² q₁ ⊢B q₃) q₀)

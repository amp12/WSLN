module MLTT.ReflexivityInversion where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem
open import MLTT.Ok
open import MLTT.WellScoped
open import MLTT.Renaming
open import MLTT.Substitution

{- The Reflexivity rule says that Γ ⊢ a ∶ A implies Γ ⊢ a ＝ a ∶ A. We
will prove the converse, which because of conversion
symmetry/transitivity, is equivalent to proving that Γ ⊢ a ＝ a' ∶ A
implies Γ ⊢ a ∶ A. We do this by simultaneously proving that
Γ ⊢ a ＝ a' ∶ A also implies Γ ⊢ a' ∶ A.

Preservation of provable judgements under weakening and substitution
is needed in the proof and in particular the following corollaries of
those results. -}

----------------------------------------------------------------------
-- Reflexivity of context conversion
----------------------------------------------------------------------
CxRefl :
  {Γ : Cx}
  (_ : Ok Γ)
  → --------
  ⊢ Γ ＝ Γ

CxRefl ◇ = ◇
CxRefl ([] q q' q'') = [] (CxRefl q'') (Refl q) (q' ∉∪ q') q q

-- {- Symmetry and transitivity for context conversion are proved later,
-- in MLTT.UniqueTypes. -}

----------------------------------------------------------------------
-- Change context up to conversion
----------------------------------------------------------------------
＝⊢idˢ :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ' ＝ Γ)
  → -------------
  Γ' ⊢ˢ  idˢ ∶ Γ

＝⊢idˢ ◇ = ◇ ◇
＝⊢idˢ ([]{l}{Γ}{A = A}{A'}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) = []
  (wkSb x h₀ (＝⊢idˢ q₀) q₂)
  h₁
  (subst (λ B → (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐯 x ∶ B ⦂ l)
    (symm (sbUnit A'))
    (⊢conv (⊢𝐯 ([]⁻ h₀ q₂) isInNew) (wkJg x h₀ q₁ q₂)))
  q₂'

＝⊢ :
  {Γ Γ' : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  (_ : ⊢ Γ' ＝ Γ)
  → -------------
  Γ' ⊢ J

＝⊢{Γ' = Γ'}{J} q q' =
  subst (λ J' → Γ' ⊢ J') (sbUnitJg J) (sbJg (＝⊢idˢ q') q)

----------------------------------------------------------------------
-- Concretion preserves typing and conversion
----------------------------------------------------------------------
concTm :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (B : Ty[ 1 ])
  (b : Tm[ 1 ])
  (x : 𝔸)
  (_ : (Γ ⨟  x ∶ A ⦂ l) ⊢ b [ x ] ∶ B [ x ] ⦂ l')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : x # (B , b))
  → ---------------------------------------------
  Γ ⊢ b [ a ] ∶ B [ a ] ⦂ l'

concTm{l' = l'}{Γ}{a = a} B b x p q (x#B ∉∪ x#b)
  with [] q' q'' _ ← ⊢ok p =
  subst₂ (λ z Z → Γ ⊢ z ∶ Z ⦂ l')
    (ssb[] x a b x#b)
    (ssb[] x a B x#B)
    (sbJg (ssbUpdate q q'' q') p)

conc＝Ty :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (B B' : Ty[ 1 ])
  (x : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ＝ B' [ x ] ⦂ l')
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : x # (B , B'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ a' ∶ A ⦂ l)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
  → ----------------------------------------------
  Γ ⊢ B [ a ] ＝ B' [ a' ] ⦂ l'

conc＝Ty{l' = l'}{Γ}{A}{a}{a'} B B' x q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁ h₂
  with [] p p' _ ← ⊢ok q₀ = Trans q q'
  where
  q : Γ ⊢ B [ a ] ＝ B [ a' ] ⦂ l'
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l')
    (ssb[] x a B q₂)
    (ssb[] x a' B q₂)
    (＝sbTm (ssb＝Update q₁ p' p) h₂ (ssbUpdate h₀ p' p ))

  q' : Γ ⊢ B [ a' ] ＝ B' [ a' ] ⦂ l'
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l')
    (ssb[] x a' B q₂)
    (ssb[] x a' B' q₂')
    (sbJg (ssbUpdate h₁ p' p) q₀)

conc＝Ty² :
  {l l' l'' : Lvl}
  {Γ : Cx}
  {A B : Ty}
  {a a' b b' : Tm}
  (C C' : Ty[ 2 ])
  (x y : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢
    C [ x ][ y ] ＝ C' [ x ][ y ] ⦂ l'')
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : (Γ  ⨟  x ∶ A ⦂ l) ⊢ B ⦂ l')
  (_ : Γ ⊢ b ＝ b' ∶ (x := a) * B ⦂ l')
  (_ : x # (C , C'))
  (_ : y # (C , C'))
  -- helper hypotheses
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ a' ∶ A ⦂ l)
  (_ : Γ ⊢ b ∶ (x := a) * B ⦂ l')
  (_ : Γ ⊢ b' ∶ (x := a') * B ⦂ l')
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ C [ x ][ y ] ⦂ l'')
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l' ) ⊢ C' [ x ][ y ] ⦂ l'')
  → -------------------------------------------------------
  Γ ⊢ C [ a ][ b ] ＝ C' [ a' ][ b' ] ⦂ l''

conc＝Ty²{l'' = l''}{Γ}{A}{B}{a}{a'}{b}{b'}
  C C' x y q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') (q₅ ∉∪ q₅') h₀ h₁ h₂ h₃ h₄ h₅
  with  [] ⊢B y#Γx _ ← ⊢ok q₀ = Trans q q'
  where
  q : Γ ⊢ C [ a ][ b ] ＝ C [ a' ][ b' ] ⦂ l''
  q = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l'')
    (ssb[]² x y a b C q₄ (q₅ ∉∪ (∉∪₂ y#Γx)))
    (ssb[]² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ y#Γx)))
    (＝sbTm (ssb＝Update² q₁ ⊢B q₃ y#Γx) h₄
      (ssbUpdate² h₀ ⊢B h₂ y#Γx))

  q' : Γ ⊢ C [ a' ][ b' ] ＝ C' [ a' ][ b' ] ⦂ l''
  q' = subst₂ (λ Z Z' → Γ ⊢ Z ＝ Z' ⦂ l'')
    (ssb[]² x y a' b' C q₄ (q₅ ∉∪ (∉∪₂ y#Γx)))
    (ssb[]² x y a' b' C' q₄' (q₅' ∉∪ (∉∪₂ y#Γx)))
    (sbJg (ssbUpdate² h₁ ⊢B h₃ y#Γx) q₀)

----------------------------------------------------------------------
-- Reflexivity Inversion
----------------------------------------------------------------------
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

⊢ty₁ (Refl q) = q

⊢ty₁ (Symm q) = ⊢ty₂ q

⊢ty₁ (Trans q _) = ⊢ty₁ q

⊢ty₁ (＝conv q₀ q₁) = ⊢conv (⊢ty₁ q₀) q₁

⊢ty₁ (𝚷Cong q₀ q₁ (q₂ ∉∪ _) _) = ⊢𝚷 (⊢ty₁ q₀) (⊢ty₁ q₁) q₂

⊢ty₁ (𝛌Cong _ q₁ (q₂ ∉∪ q₂' ∉∪ _) h₀ h₁) = ⊢𝛌
  (⊢ty₁ q₁)
  (q₂ ∉∪ q₂')
  h₀
  (⊢ty₁ (Refl h₁))

⊢ty₁ (∙Cong _ _ q₂ q₃ (q₄ ∉∪ _) h₀ h₁) = ⊢∙
  (⊢ty₁ q₂)
  (⊢ty₁ q₃)
  h₁
  q₄
  h₀

⊢ty₁ (𝐈𝐝Cong q₀ q₁ q₂) = ⊢𝐈𝐝
  (⊢ty₁ q₁)
  (⊢ty₁ q₂)
  (⊢ty₁ q₀)

⊢ty₁ (𝐫𝐞𝐟𝐥Cong q h) = ⊢𝐫𝐞𝐟𝐥
  (⊢ty₁ q)
  h

⊢ty₁ (𝐉Cong q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ _) (q₆ ∉∪ _) h₀ h₁) = ⊢𝐉
  (⊢ty₁ q₀)
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

⊢ty₁ (𝚷Beta q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) =
  ⊢∙ (⊢𝛌 q₀ (q₂ ∉∪ q₂') h₀ h₁) q₁ h₁ q₂ h₀

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

⊢ty₂ (Refl q) = q

⊢ty₂ (Symm q) = ⊢ty₁ q

⊢ty₂ (Trans _ q) = ⊢ty₂ q

⊢ty₂ (＝conv q₀ q₁) = ⊢conv (⊢ty₂ q₀) q₁

⊢ty₂ (𝚷Cong q₀ q₁ (_ ∉∪ q₂') h) =
  let x#Γ = π₁([]⁻¹(⊢ok q₁)) in
  ⊢𝚷
  (⊢ty₂ q₀)
  (＝⊢
    (⊢ty₂ q₁)
    ([] (CxRefl (⊢ok q₀)) (Symm q₀) (x#Γ ∉∪ x#Γ) (⊢ty₂ q₀) h))
  q₂'

⊢ty₂{Γ = Γ} (𝛌Cong{l}{l'}{A}{A'}{B}{b}{b'}{x}
  q₀ q₁ (q₂ ∉∪ _ ∉∪ q₂') h₀ h₁) =  ⊢conv q q'
  where
  x#Γ = π₁([]⁻¹(⊢ok h₁))

  e : ⊢ (Γ ⨟ x ∶ A' ⦂ l) ＝ (Γ ⨟ x ∶ A ⦂ l)
  e = [] (CxRefl (⊢ok h₀)) (Symm q₀) (x#Γ ∉∪ x#Γ) (⊢ty₂ q₀) h₀

  q : Γ ⊢ 𝛌 A' b' ∶ 𝚷 A' B ⦂ max l l'
  q = ⊢𝛌 (＝⊢ (⊢ty₂ q₁) e) (q₂ ∉∪ q₂') (⊢ty₂ q₀) (＝⊢ h₁ e)

  q' : Γ ⊢ 𝚷 A' B ＝ 𝚷 A B ⦂ (max l l')
  q' = 𝚷Cong (Symm q₀) (＝⊢ (Refl h₁) e) (q₂ ∉∪ q₂) (⊢ty₂ q₀)

⊢ty₂ (∙Cong{l' = l'}{B = B}{B'}{x = x}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') h₀ _) =
  let x#Γ = π₁([]⁻¹(⊢ok q₁)) in ⊢conv
  (⊢∙
    (⊢conv (⊢ty₂ q₂) (𝚷Cong q₀ q₁ (q₄ ∉∪ q₄') h₀))
    (⊢conv (⊢ty₂ q₃) q₀)
    (＝⊢ (⊢ty₂ q₁) ([] (CxRefl (⊢ok q₀)) (Symm q₀) (x#Γ ∉∪ x#Γ) (⊢ty₂ q₀) h₀))
    q₄'
    (⊢ty₂ q₀))
  (Symm (conc＝Ty B B' x
    q₁ q₃ (q₄ ∉∪ q₄') (⊢ty₁ q₃) (⊢ty₂ q₃) (⊢ty₁ q₁)))

⊢ty₂ (𝐈𝐝Cong q₀ q₁ q₂) = ⊢𝐈𝐝
  (⊢conv (⊢ty₂ q₁) q₀)
  (⊢conv (⊢ty₂ q₂) q₀)
  (⊢ty₂ q₀)

⊢ty₂ (𝐫𝐞𝐟𝐥Cong q h) = ⊢conv
  (⊢𝐫𝐞𝐟𝐥 (⊢ty₂ q) h)
  (𝐈𝐝Cong (Refl h) (Symm q) (Symm q))

⊢ty₂{Γ = Γ} (𝐉Cong{l}{l'}{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}{x}{y}
  q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') h₀ h₁) =
  ⊢conv r (Symm s)
  where
  Γok : Ok Γ
  Γok = ⊢ok h₀

  x#Γ = π₁([]⁻¹(⊢ok h₁))

  y#Γx = π₁([]⁻¹(⊢ok q₀))

  x#A : x # A
  x#A = ∉∪₁ (⊢# h₀ x#Γ)

  x#a : x # a
  x#a = ∉∪₁ (⊢# q₁ x#Γ)

  r₁ : Γ ⊢ e ∶ (x := b) * 𝐈𝐝 A a (𝐯 x) ⦂ l
  r₁ rewrite ssbFresh x b A x#A
     | ssbFresh x b a x#a
     | updateEq{idˢ}{b} x = ⊢ty₁ q₄

  r₂ :  Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A a b' ⦂ l
  r₂ = 𝐈𝐝Cong (Refl h₀) (Refl (⊢ty₁ q₁)) q₂

  r₁' : Γ ⊢ e' ∶ (x := b') * 𝐈𝐝 A a (𝐯 x) ⦂ l
  r₁' rewrite ssbFresh x b' A x#A
      | ssbFresh x b' a x#a
      | updateEq{idˢ}{b'} x = ⊢conv (⊢ty₂ q₄) r₂

  r₁'' : Γ ⊢ e ＝ e' ∶ (x := b) * 𝐈𝐝 A a (𝐯 x) ⦂ l
  r₁'' rewrite ssbFresh x b A x#A
      | ssbFresh x b a x#a
      | updateEq{idˢ}{b} x = q₄

  s : Γ ⊢ C [ b ][ e ] ＝ C' [ b' ][ e' ] ⦂ l'
  s = conc＝Ty² C C' x y
    q₀ q₂ h₁ r₁'' (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') (⊢ty₁ q₂)
    (⊢ty₂ q₂) r₁ r₁' (⊢ty₁ q₀) (⊢ty₂ q₀)

  s₁ : Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ (x := a) * 𝐈𝐝 A a (𝐯 x) ⦂ l
  s₁ rewrite ssbFresh x a A x#A
     | ssbFresh x a a x#a
     | updateEq{idˢ}{a} x = ⊢𝐫𝐞𝐟𝐥 (⊢ty₁ q₁) h₀

  s₁' : Γ ⊢ 𝐫𝐞𝐟𝐥 a' ∶ (x := a') * 𝐈𝐝 A a (𝐯 x) ⦂ l
  s₁' rewrite ssbFresh x a' A x#A
     | ssbFresh x a' a x#a
     | updateEq{idˢ}{a'} x = ⊢conv
      (⊢𝐫𝐞𝐟𝐥 (⊢ty₂ q₁) h₀)
       (𝐈𝐝Cong (Refl h₀) (Symm q₁) (Refl (⊢ty₂ q₁)))

  s₁'' : Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ (x := a) * 𝐈𝐝 A a (𝐯 x) ⦂ l
  s₁'' rewrite ssbFresh x a A x#A
      | ssbFresh x a a x#a
      | updateEq{idˢ}{a} x = 𝐫𝐞𝐟𝐥Cong q₁ h₀

  s' : Γ ⊢ C [ a ][ 𝐫𝐞𝐟𝐥 a ] ＝ C' [ a' ][ 𝐫𝐞𝐟𝐥 a' ] ⦂ l'
  s' = conc＝Ty² C C' x y q₀ q₁ h₁ s₁'' (q₅ ∉∪ q₅')
    (q₆ ∉∪ q₆') (⊢ty₁ q₁) (⊢ty₂ q₁) s₁ s₁' (⊢ty₁ q₀) (⊢ty₂ q₀)

  r₂' :  Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A a' b' ⦂ l
  r₂' = 𝐈𝐝Cong (Refl h₀) q₁ q₂

  r₃ : (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a' (𝐯 x) ⦂ l
  r₃ = ⊢𝐈𝐝
    (wkJg x h₀ (⊢ty₂ q₁) x#Γ)
    (⊢𝐯 ([]⁻ h₀ x#Γ) isInNew)
    (wkJg x h₀ h₀ x#Γ)

  r₃' : (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a' (𝐯 x) ＝ 𝐈𝐝 A a (𝐯 x) ⦂ l
  r₃' = 𝐈𝐝Cong
    (Refl (wkJg x h₀ h₀ x#Γ))
    (Symm (wkJg x h₀ q₁ x#Γ))
    (Refl (⊢𝐯 ([]⁻ h₀ x#Γ) isInNew))

  r₄ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a' (𝐯 x) ⦂ l) ⊢ C' [ x ][ y ] ⦂ l'
  r₄ = ＝⊢
    (⊢ty₂ q₀)
    ([] ([] (CxRefl Γok) (Refl h₀) (x#Γ ∉∪ x#Γ) h₀ h₀) r₃'
      (y#Γx ∉∪ y#Γx) r₃ h₁)

  r : Γ ⊢ 𝐉 C' a' b' c' e' ∶ C' [ b' ][ e' ] ⦂ l'
  r = ⊢𝐉 r₄ (⊢ty₂ q₁) (⊢ty₂ q₂) (⊢conv (⊢ty₂ q₃) s')
    (⊢conv (⊢ty₂ q₄) r₂') q₅' q₆' h₀ r₃

⊢ty₂ (𝐬𝐮𝐜𝐜Cong q) = ⊢𝐬𝐮𝐜𝐜 (⊢ty₂ q)

⊢ty₂{Γ = Γ} (𝐧𝐫𝐞𝐜Cong{l}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') h) =
  ⊢conv r₀ (Symm r₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₁

  x#Γ = π₁ ([]⁻¹ (⊢ok q₀))

  y#Γx = π₁ ([]⁻¹ (⊢ok q₂))

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ⦂ 0
  ⊢N = ⊢𝐍𝐚𝐭 Γok

  r₂ : Γ ⊢ C [ 𝐳𝐞𝐫𝐨 ] ＝ C' [ 𝐳𝐞𝐫𝐨 ] ⦂ l
  r₂ = conc＝Ty C C' x q₀
    (Refl (⊢𝐳𝐞𝐫𝐨 Γok)) (q₄ ∉∪ q₄')
    (⊢𝐳𝐞𝐫𝐨 Γok) (⊢𝐳𝐞𝐫𝐨 Γok) (⊢ty₁ q₀)

  s : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ˢ (x := 𝐬𝐮𝐜𝐜 (𝐯 x)) ∶ (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0)
  s = sbUpdate
    (wkSb x ⊢N (⊢idˢ Γok) x#Γ)
    (⊢𝐬𝐮𝐜𝐜 (⊢𝐯 ([]⁻ ⊢N x#Γ) isInNew))
    x#Γ
    ⊢N

  r₂' : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢
    C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ＝ C' [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
  r₂' = subst₂ (λ D D' → (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ D ＝ D' ⦂ l)
    (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) C q₄)
    (ssb[] x (𝐬𝐮𝐜𝐜 (𝐯 x)) C' q₄')
    (sbJg s q₀)

  r₃ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l) ⊢
    c₊' [ x ][ y ] ∶ C' [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
  r₃ = ⊢conv (⊢ty₂ q₂) (wkJg y (⊢ty₁ q₀) r₂' y#Γx)

  r₃' : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C' [ x ] ⦂ l) ⊢
    c₊' [ x ][ y ] ∶ C' [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
  r₃' = ＝⊢
    r₃
    ([]
      ([] (CxRefl Γok) (Refl ⊢N) (x#Γ ∉∪ x#Γ) ⊢N ⊢N)
      (Symm q₀)
      (y#Γx ∉∪ y#Γx)
      (⊢ty₂ q₀)
      h)

  r₀ : Γ ⊢ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C' [ a' ] ⦂ l
  r₀ = ⊢𝐧𝐫𝐞𝐜
    (⊢conv (⊢ty₂ q₁) r₂)
    r₃'
    (⊢ty₂ q₃)
    (q₄' ∉∪ q₄''')
    q₅'
    (⊢ty₂ q₀)

  r₁ : Γ ⊢ C [ a ] ＝ C' [ a' ] ⦂ l
  r₁ = conc＝Ty C C' x q₀ q₃ (q₄ ∉∪ q₄') (⊢ty₁ q₃) (⊢ty₂ q₃) h

⊢ty₂ (𝚷Beta{B = B}{b}{x} q₀ q₁ q₂ _ _) = concTm B b x q₀ q₁ q₂

⊢ty₂ (𝐈𝐝Beta _ _ q _ _ _ _) = q

⊢ty₂ (𝐍𝐚𝐭Beta₀ q _ _ _ _) = q

⊢ty₂{Γ = Γ} (𝐍𝐚𝐭Beta₊{l}{C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h) = subst₂ (λ d D → Γ ⊢ d ∶ D ⦂ l)
  (ssb[]² x y a (𝐧𝐫𝐞𝐜 C c₀ c₊ a) c₊ q₃' (q₄ ∉∪ (∉∪₂ y#Γx)))
  e
  (sbJg s q₁)
  where
  Γok : Ok Γ
  Γok = ⊢ok q₀

  x#Γ = π₁ ([]⁻¹ (⊢ok h))

  y#Γx = π₁ ([]⁻¹ (⊢ok q₁))

  ⊢N : Γ ⊢ 𝐍𝐚𝐭 ⦂ 0
  ⊢N = ⊢𝐍𝐚𝐭 Γok

  r : Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ (x := a) * C [ x ] ⦂ l
  r rewrite ssb[] x a C q₃ = ⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h

  s : Γ ⊢ˢ (x := a ∘/ y := 𝐧𝐫𝐞𝐜 C c₀ c₊ a) ∶
    (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l)
  s = sbUpdate (ssbUpdate q₂ x#Γ ⊢N) r y#Γx h

  y#C : y # C
  y#C = ⊆∉ ([]supp C 𝐳𝐞𝐫𝐨) (∉∪₂ (⊢# q₀ (∉∪₁ y#Γx)))

  y# : y #  C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
  y# = ⊆∉ (supp[] C (𝐬𝐮𝐜𝐜 (𝐯 x))) (y#C ∉∪ ∉∪₂ y#Γx ∉∪ ∉∅)

  e : (x := a ∘/ y := 𝐧𝐫𝐞𝐜 C c₀ c₊ a) *  C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
    C [ 𝐬𝐮𝐜𝐜 a  ]
  e rewrite updateFresh (x := a) y (𝐧𝐫𝐞𝐜 C c₀ c₊ a) (C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ]) y#
    | sb[] (x := a) C (𝐬𝐮𝐜𝐜 (𝐯 x))
    | ssbFresh x a C q₃
    | updateEq{idˢ}{a} x = refl

⊢ty₂{Γ = Γ} (𝚷Eta{l}{l'}{A}{B}{b}{x} q₀ q₁ h)
  with  (y , y#B ∉∪ y#) ← fresh (B , (Γ , x)) = ⊢𝛌
    q
    (x#B ∉∪ (#abs x (b ∙[ A , B ] 𝐯 x)))
    h
    q₁

  where
  x#Γ =  π₁ ([]⁻¹ (⊢ok q₁))

  x#B : x # B
  x#B = ∉∪₁ (∉∪₂ (∉∪₂ (⊢# q₀ x#Γ)))

  q : (Γ ⨟ x ∶ A ⦂ l) ⊢ (x ． b ∙[ A , B ] 𝐯 x)[ x ] ∶ B [ x ] ⦂ l'
  q rewrite concAbs' x (b ∙[ A , B ] 𝐯 x) = ⊢∙{x = y}
    (wkJg x h q₀ x#Γ)
    (⊢𝐯 (⊢ok q₁) isInNew)
    (subst₂ (λ A' C → (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ A' ⦂ l) ⊢ C ⦂ l')
      (sbUnit A)
      (ssb[] x (𝐯 y) B x#B)
      (sbJg (liftSb (wkSb x h (⊢idˢ (⊢ok q₀)) x#Γ) h x#Γ y#
        (wkJg x h
          (subst (λ A' → Γ ⊢ A' ⦂ l)
            (symm (sbUnit A)) h) x#Γ)) q₁))
    y#B
    (wkJg x h h x#Γ)

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
⊢sb₁ ([] q₀ q₁ q₂ q₃) = [] (⊢sb₁ q₀) q₁ (⊢ty₁ q₂) q₃

⊢sb₂ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  (_ : Γ ⊢ˢ σ ＝ σ' ∶ Γ')
  → ---------------------
  Γ ⊢ˢ σ' ∶ Γ'

⊢sb₂ (◇ q) = ◇ q
⊢sb₂ ([] q₀ q₁ q₂ q₃) = []
  (⊢sb₂ q₀)
  q₁
  (⊢conv (⊢ty₂ q₂) (＝sbTm q₀ q₁ (⊢sb₁ q₀)))
  q₃

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

congSbTm q q' = Trans
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
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : x # B)
  → -----------------------------------
  Γ ⊢ B [ a ] ⦂ l'

concTy{l' = l'}{Γ}{A}{a} B x q₀ q₁ q₂
  with [] ⊢A x#Γ _ ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ⦂ l')
    (ssb[] x a B q₂)
    (sbJg (ssbUpdate q₁ x#Γ ⊢A) q₀)

concTy² :
  {l l' l'' : Lvl}
  {Γ : Cx}
  {A B : Ty}
  {a b : Tm}
  (C : Ty[ 2 ])
  (x y : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢
    C [ x ][ y ] ⦂ l'')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ b ∶ (x := a) * B ⦂ l')
  (_ : x # C)
  (_ : y # C)
  → ------------------------------------
  Γ ⊢ C [ a ][ b ] ⦂ l''

concTy²{l'' = l''}{Γ}{A}{B}{a}{b} C x y q₀ q₁ q₃ q₄ q₅
  with [] ⊢B y#Γx _ ← ⊢ok q₀ =
  subst (λ Z → Γ ⊢ Z ⦂ l'')
    (ssb[]² x y a b C q₄ (q₅ ∉∪ (∉∪₂ y#Γx)))
    (sbJg (ssbUpdate² q₁ ⊢B q₃ y#Γx) q₀)

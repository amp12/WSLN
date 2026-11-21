module GST.Renaming where

open import Prelude
open import WSLN

open import GST.Syntax
open import GST.Context
open import GST.TypeSystem
open import GST.WellScoped
open import GST.Setoid

----------------------------------------------------------------------
-- Well-typed renaming
----------------------------------------------------------------------
infix 4 _⊢ʳ_∶_
data _⊢ʳ_∶_ (Γ' : Cx) : Rn → Cx → Set where
  ◇ :
    {ρ : Rn}
    → ------------
    Γ' ⊢ʳ ρ ∶ ◇
  [] :
    {Γ : Cx}
    {ρ : Rn}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ʳ ρ ∶ Γ)
    (q₁ : (ρ x , A) isIn Γ')
    → ----------------------
    Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A)

[]₀ :
  {Γ Γ' : Cx}
  {ρ : Rn}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A))
  → -------------------------
  Γ' ⊢ʳ ρ ∶ Γ

[]₀ ([] q _) = q

[]₁ :
  {Γ Γ' : Cx}
  {ρ : Rn}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A))
  → -------------------------
  (ρ x , A) isIn Γ'

[]₁ ([] _ q) = q

----------------------------------------------------------------------
-- Setoid of renamings of variables in a given context
----------------------------------------------------------------------
Rn[_] : Cx → Setd

∣ Rn[ Γ ] ∣ = Rn
Rn[ Γ ] ∋ ρ ~ ρ' = ∀ x → x ∈ dom Γ → ρ x ≡ ρ' x
~Refl Rn[ Γ ] _ _ _ = refl
~Symm Rn[ Γ ] e x r = symm (e x r )
~Trans Rn[ Γ ] e e' x r = trans (e x r) (e' x r)

rnUpdate# :
  {Γ : Cx}
  {x x' : 𝔸}
  (ρ : Rn)
  (_ : x # Γ)
  → --------------------------
  Rn[ Γ ] ∋  ρ ~ (ρ ∘/ x := x')

rnUpdate# {x = x} _ x#Γ y y∈Γ with x ≐ y
... | no _ = refl
... | equ = Øelim ((∉→¬∈ x#Γ) y∈Γ)

----------------------------------------------------------------------
-- Renaming is well scoped
----------------------------------------------------------------------
rnDom :
  {Γ Γ' : Cx}
  {ρ : Rn}
  {x : 𝔸}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : x ∈ dom Γ)
  → ---------------
  ρ x ∈ dom Γ'

rnDom ([] p _) (∈∪₁ q)    = rnDom p q
rnDom ([] _ q) (∈∪₂ ∈｛｝) = isIn→dom q

Rn[]∘ :
  {Γ Γ' : Cx}
  {ρ ρ' ρ₁ ρ₁' : Rn}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Rn[ Γ ] ∋ ρ ~ ρ')
  (_ : Rn[ Γ' ] ∋ ρ₁ ~ ρ₁')
  → -------------------------
  Rn[ Γ ] ∋ ρ₁ ∘ ρ ~ ρ₁' ∘ ρ'

Rn[]∘ {ρ = ρ}{ρ₁' = ρ₁'} p e e₁ x r =
  trans (e₁ (ρ x) (rnDom p r)) (cong ρ₁' (e x r))

----------------------------------------------------------------------
-- Types of variables under renaming
----------------------------------------------------------------------
⊢rnVar :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : (x , A) isIn Γ)
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ------------------
  (ρ x , A) isIn Γ'

⊢rnVar (isInNew refl) ([] _ q) = q
⊢rnVar (isInOld p)    ([] q _) = ⊢rnVar p q

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wkRn :
  {Γ Γ' : Cx}
  {ρ : Rn}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → -------------------
  Γ' ⨟ x ∶ A ⊢ʳ ρ ∶ Γ

wkRn ◇ = ◇
wkRn ([] q₀ q₁) = [] (wkRn q₀) (isInOld q₁)

----------------------------------------------------------------------
-- Identity renaming
----------------------------------------------------------------------
⊢ʳid :
  {Γ : Cx}
  → ---------
  Γ ⊢ʳ id ∶ Γ

⊢ʳid {◇} = ◇
⊢ʳid {_ ⨟ _ ∶ _} = [] (wkRn ⊢ʳid) (isInNew refl)

----------------------------------------------------------------------
-- Composing renamings
----------------------------------------------------------------------
⊢ʳ∘ :
  {Γ Γ' Γ'' : Cx}
  {ρ ρ' : Rn}
  (_ : Γ'' ⊢ʳ ρ' ∶ Γ')
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ------------------
  Γ'' ⊢ʳ ρ' ∘ ρ ∶ Γ

⊢ʳ∘ q ◇  = ◇
⊢ʳ∘ q ([] q₀ q₁) = [] (⊢ʳ∘ q q₀) (⊢rnVar q₁ q)

----------------------------------------------------------------------
-- Extensionality property of well-typed renamings
----------------------------------------------------------------------
⊢ʳExt :
  {ρ ρ' : Rn}
  {Γ Γ' : Cx}
  (_ : Rn[ Γ ] ∋ ρ ~ ρ')
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → --------------------
  Γ' ⊢ʳ ρ' ∶ Γ

⊢ʳExt _ ◇ = ◇
⊢ʳExt e ([]{x = x} q q')
  rewrite e x (∈∪₂ ∈｛｝) = []
  (⊢ʳExt (λ x' x'∈Γ → e x' (∈∪₁ x'∈Γ)) q) q'

----------------------------------------------------------------------
-- Lifting
----------------------------------------------------------------------
liftRn :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → -----------------------------------------
  Γ' ⨟ x' ∶ A ⊢ʳ (ρ ∘/ x := x') ∶ (Γ ⨟ x ∶ A)

liftRn{ρ}{Γ}{Γ'}{A}{x}{x'} q = []
  (⊢ʳExt (rnUpdate# ρ it) (wkRn q))
  (subst (λ z → (z , A) isIn (Γ' ⨟ x' ∶ A))
    (symm (:=Eq{f = ρ}{x'} x))
    (isInNew refl))

----------------------------------------------------------------------
-- Renaming preserves typing
----------------------------------------------------------------------
rn⊢ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ a ∶ A)
  → ---------------
  Γ' ⊢ ρ * a ∶ A

rn⊢ p (Var q) = Var (⊢rnVar q p)
rn⊢{ρ}{Γ' = Γ'} p (Lam{A}{B}{b}{x} q x#b)
  with (x' , x'#ρb ∉∪ x'#Γ') ← fresh (ρ * b , Γ') = Lam
    (subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
      (rnUpdate[] ρ x x' b x#b)
      (rn⊢ (liftRn p) q))
    x'#ρb
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
rn⊢ p (App q₀ q₁) = App (rn⊢ p q₀) (rn⊢ p q₁)
rn⊢ p Zero = Zero
rn⊢ p (Succ q) = Succ (rn⊢ p q)
rn⊢ p (Nrec q₀ q₁ q₂) = Nrec (rn⊢ p q₀) (rn⊢ p q₁) (rn⊢ p q₂)

rn⊢¹ :
  {Γ : Cx}
  {A B : Ty}
  (x x' : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ ⦄
  (b : Tm[ 1 ])
  (_ : Γ ⨟ x ∶ A ⊢ b [ x ] ∶ B)
  (_ : x # b)
  (_ : x' # b)
  → ----------------------------
  Γ ⨟ x' ∶ A ⊢ b [ x' ] ∶ B

rn⊢¹{Γ}{A}{B} x x' b q x#b x'∉b =
  subst (λ c → Γ ⨟ x' ∶ A ⊢ c ∶ B)
    e
    (rn⊢ (liftRn ⊢ʳid) q)
  where
  e : (x := x') * (b [ x ]) ≡ b [ x' ]
  e rewrite rnUpdate[] id x x' b x#b
    | rnUnit b = refl

----------------------------------------------------------------------
-- Renaming preserves conversion
----------------------------------------------------------------------
rn＝ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → ----------------------
  Γ' ⊢ ρ * a ＝ ρ * a' ∶ A

rn＝ p (Refl q) = Refl (rn⊢ p q)
rn＝ p (Symm q) = Symm (rn＝ p q)
rn＝ p (Trans q₀ q₁) = Trans (rn＝ p q₀) (rn＝ p q₁)
rn＝{ρ}{Γ' = Γ'} p (Lam{A}{B}{b}{b'}{x} q (x#b ∉∪ x#b'))
  with (x' , x'# ∉∪ x'#Γ') ← fresh ((ρ * b , ρ * b') , Γ') = Lam
    (subst₂ (λ c c' → Γ' ⨟ x' ∶ A ⊢ c ＝ c' ∶ B)
      (rnUpdate[] ρ x x' b x#b)
      (rnUpdate[] ρ x x' b' x#b')
      (rn＝ (liftRn p) q))
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
rn＝ p (App q₀ q₁) = App (rn＝ p q₀) (rn＝ p q₁)
rn＝ p (Succ q) = Succ (rn＝ p q)
rn＝ p (Nrec q₀ q₁ q₂) =
  Nrec (rn＝ p q₀) (rn＝ p q₁) (rn＝ p q₂)
rn＝{ρ}{Γ' = Γ'} p (BetaLam{A}{B}{a}{b}{x} q₀ q₁ x#b)
  with (x' , x'# ∉∪ x'#Γ') ← fresh (ρ * b , Γ')
  rewrite rn[] ρ b a =
  BetaLam{b = ρ * b}
    (subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
        (rnUpdate[] ρ x x' b x#b)
        (rn⊢ (liftRn p) q₀))
    (rn⊢ p q₁)
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
rn＝ p (BetaZero q₀ q₁) =
  BetaZero (rn⊢ p q₀) (rn⊢ p q₁)
rn＝ p (BetaSucc q₀ q₁ q₂) =
  BetaSucc (rn⊢ p q₀) (rn⊢ p q₁) (rn⊢ p q₂)
rn＝{ρ}{Γ' = Γ'} p (Eta{b = b}{x} q x#b)
  with (x' , x'# ∉∪ x'∉Γ') ← fresh (ρ * b , Γ')
  rewrite
    (rnAbs ρ x x' (b ∙ 𝐯 x) λ{
      _ (∈∪₁ q') _ refl →
        ∉→¬∈ x'∉Γ' (rnDom  p (supp⊢ q q')) ;
      _ (∈∪₂ (∈∪₁ ∈｛｝)) q' refl → q' refl})
  | :=Eq {f = ρ}{x'} x
  | updateFreshRn ρ x x' b x#b =
  Eta{x = x'} (rn⊢ p q) x'#

rn＝¹ :
  {Γ : Cx}
  {A B : Ty}
  (x x' : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ ⦄
  (b b' : Tm[ 1 ])
  (_ : Γ ⨟ x ∶ A ⊢ b [ x ] ＝ b' [ x ] ∶ B)
  (_ : x # (b , b'))
  (_ : x' # (b , b'))
  → ---------------------------------------
  Γ ⨟ x' ∶ A ⊢ b [ x' ] ＝ b' [ x' ] ∶ B

rn＝¹{Γ}{A}{B} x x' b b' q (x#b ∉∪ x#b') (x'∉b ∉∪ x'#b') =
  subst₂ (λ c c' → Γ ⨟ x' ∶ A ⊢ c ＝ c' ∶ B)
    e
    e'
    (rn＝ (liftRn ⊢ʳid) q)
  where
  e : (x := x') * (b [ x ]) ≡ b [ x' ]
  e rewrite rnUpdate[] id x x' b x#b
    | rnUnit b = refl
  e' : (x := x') * (b' [ x ]) ≡ b' [ x' ]
  e' rewrite rnUpdate[] id x x' b' x#b'
    | rnUnit b' = refl

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wk⊢ :
  {Γ : Cx}
  {A A' : Ty}
  {a : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ a ∶ A)
  ⦃ _ : x # Γ ⦄
  → ----------------
  Γ ⨟ x ∶ A' ⊢ a ∶ A

wk⊢ {Γ}{A}{A'}{a}{x} q = subst (λ b → Γ ⨟ x ∶ A' ⊢ b ∶ A)
  (rnUnit a)
  (rn⊢ (wkRn ⊢ʳid) q)

wk＝ :
  {Γ : Cx}
  {A A' : Ty}
  {a a' : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ a ＝ a' ∶ A)
  ⦃ _ : x # Γ ⦄
  → ----------------------
  Γ ⨟ x ∶ A' ⊢ a ＝ a' ∶ A

wk＝ {Γ}{A}{A'}{a}{a'}{x} q =
  subst₂ (λ b b' → Γ ⨟ x ∶ A' ⊢ b ＝ b' ∶ A)
    (rnUnit a)
    (rnUnit a')
    (rn＝ (wkRn ⊢ʳid) q)

----------------------------------------------------------------------
-- Support-respecting renaming of terms
----------------------------------------------------------------------
rnRespSuppTm :
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  {ρ ρ' : Rn}
  (_ : Γ ⊢ a ＝ a' ∶ A)
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Rn[ Γ ] ∋ ρ ~ ρ')
  → -----------------------
  Γ' ⊢ ρ * a ＝ ρ' * a' ∶ A

rnRespSuppTm {Γ' = Γ'}{A}{a}{a'}{ρ}{ρ'} q p e =
  subst (λ b → Γ' ⊢ ρ * a ＝ b ∶ A)
  (rnRespSupp ρ ρ' a' λ x x∈a' → e x (supp＝₂ q x∈a'))
  (rn＝ p q)

----------------------------------------------------------------------
-- Unitary and associative laws
----------------------------------------------------------------------
⊢rnUnit :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A)
  → ------------------
  Γ ⊢ idʳ * a ＝ a ∶ A

⊢rnUnit {a = a} q rewrite rnUnit a = Refl q

⊢rnAssoc :
  {Γ Γ' Γ'' : Cx}
  {A : Ty}
  {a : Tm}
  {ρ ρ' : Rn}
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ'' ⊢ʳ ρ' ∶ Γ')
  → ----------------------------------
  Γ'' ⊢ (ρ' ∘ ρ) * a ＝ ρ' * ρ * a ∶ A

⊢rnAssoc {a = a}{ρ}{ρ'} q p p'
  rewrite rnAssoc ρ ρ' a = Refl (rn⊢ p' (rn⊢ p q))

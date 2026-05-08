module GST.NormalForm where

open import Prelude
open import WSLN

open import GST.Syntax
open import GST.Context
open import GST.TypeSystem
open import GST.WellScoped
open import GST.Setoid
open import GST.Renaming
open import GST.Substitution
open import GST.Admissible
open import GST.UniqueTypes

----------------------------------------------------------------------
-- Normal and neutral forms
----------------------------------------------------------------------
infix 3 _⊢ⁿ_∶_ _⊢ᵘ_∶_
data _⊢ⁿ_∶_  (Γ : Cx) : Tm → Ty → Set
data _⊢ᵘ_∶_  (Γ : Cx) : Tm → Ty → Set

data _⊢ⁿ_∶_ Γ where
  Lam :
    {A B : Ty}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⨟ x ∶ A ⊢ⁿ b [ x ] ∶ B)
    (q₁ : x # b)
    → -------------------------------
    Γ ⊢ⁿ 𝛌 A b ∶ A ⇒ B
  Zero : Γ ⊢ⁿ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭
  Succ :
    {a : Tm}
    (q : Γ ⊢ⁿ a ∶ 𝐍𝐚𝐭)
    → ----------------
    Γ ⊢ⁿ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭
  Neu :
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ᵘ a ∶ A)
    → --------------
    Γ ⊢ⁿ a ∶ A

data _⊢ᵘ_∶_ Γ where
  Var :
    {A : Ty}
    {x : 𝔸}
    (q : (x , A) isIn Γ)
    → ------------------
    Γ ⊢ᵘ 𝐯 x ∶ A

  App :
    {A B : Ty}
    {a b : Tm}
    (q₀ : Γ ⊢ᵘ b ∶ A ⇒ B)
    (q₁ : Γ ⊢ⁿ a ∶ A)
    → -------------------
    Γ ⊢ᵘ b ∙ a ∶ B

  Nrec :
    {C : Ty}
    {c₀ a c₊ : Tm}
    (q₀ : Γ ⊢ⁿ c₀ ∶ C)
    (q₁ : Γ ⊢ⁿ c₊ ∶ 𝐍𝐚𝐭 ⇒ C ⇒ C)
    (q₂ : Γ ⊢ᵘ a ∶ 𝐍𝐚𝐭)
    → --------------------------
    Γ ⊢ᵘ 𝐧𝐫𝐞𝐜 c₀ c₊ a ∶ C

----------------------------------------------------------------------
-- Normal and neutral forms are typeable terms
----------------------------------------------------------------------
tyⁿ :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ⁿ a ∶ A)
  → --------------
  Γ ⊢ a ∶ A

tyᵘ :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ᵘ a ∶ A)
  → --------------
  Γ ⊢ a ∶ A

tyⁿ (Lam q₀ q₁) = Lam (tyⁿ q₀) q₁
tyⁿ Zero = Zero
tyⁿ (Succ q) = Succ (tyⁿ q)
tyⁿ (Neu q) = tyᵘ q

tyᵘ (Var q₁) = Var q₁
tyᵘ (App q₀ q₁) = App (tyᵘ q₀) (tyⁿ q₁)
tyᵘ (Nrec q₀ q₁ q₂) = Nrec (tyⁿ q₀) (tyⁿ q₁) (tyᵘ q₂)

----------------------------------------------------------------------
-- Renaming preserves normal/neutral forms
----------------------------------------------------------------------
rn⊢ⁿ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ⁿ a ∶ A)
  → ---------------
  Γ' ⊢ⁿ ρ * a ∶ A

rn⊢ᵘ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ᵘ a ∶ A)
  → ---------------
  Γ' ⊢ᵘ ρ * a ∶ A


rn⊢ⁿ{ρ}{Γ' = Γ'} p (Lam{A}{B}{b}{x} q x#b)
  with (x' , x'#ρb ∉∪ x'#Γ') ← fresh (ρ * b , Γ') = Lam
  (subst (λ c → Γ' ⨟ x' ∶ A ⊢ⁿ c ∶ B)
    (rnUpdate[] ρ x x' b x#b)
    (rn⊢ⁿ (liftRn p) q))
  x'#ρb
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
rn⊢ⁿ p Zero = Zero
rn⊢ⁿ p (Succ q) = Succ (rn⊢ⁿ p q)
rn⊢ⁿ p (Neu q) = Neu (rn⊢ᵘ p q)

rn⊢ᵘ p (Var q) = Var (⊢rnVar q p)
rn⊢ᵘ p (App q₀ q₁) = App (rn⊢ᵘ p q₀) (rn⊢ⁿ p q₁)
rn⊢ᵘ p (Nrec q₀ q₁ q₂) =
  Nrec (rn⊢ⁿ p q₀) (rn⊢ⁿ p q₁) (rn⊢ᵘ p q₂)

----------------------------------------------------------------------
-- Neutral substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢᵘ_∶_
data _⊢ˢᵘ_∶_ (Γ' : Cx) : Sb → Cx → Set where
  ◇ :
    {σ : Sb}
    → ------------
    Γ' ⊢ˢᵘ σ ∶ ◇
  [] :
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ˢᵘ σ ∶ Γ)
    (q₁ : Γ' ⊢ᵘ σ x ∶ A)
    → --------------------
    Γ' ⊢ˢᵘ σ ∶ (Γ ⨟ x ∶ A)

-- Neutral substitutions are substitutions
sbᵘ :
  {Γ Γ' : Cx}
  {σ : Sb}
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → ------------------
  Γ' ⊢ˢ σ ∶ Γ

sbᵘ ◇ = ◇
sbᵘ ([] q₀ q₁) = [] (sbᵘ q₀) (tyᵘ q₁)

-- Renaming neutral substitutions
rnSbᵘ :
  {Γ Γ' Γ'' : Cx}
  {ρ : Rn}
  {σ : Sb}
  (_ : Γ'' ⊢ʳ ρ ∶ Γ')
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → -------------------
  Γ'' ⊢ˢᵘ 𝐚∘ ρ ∘ˢ σ ∶ Γ

rnSbᵘ q ◇ = ◇
rnSbᵘ q ([] p₀ p₁) = [] (rnSbᵘ q p₀) (rn⊢ᵘ q p₁)

-- Identity substitution is neutral
⊢ᵘidˢ :
  {Γ : Cx}
  → --------
  Γ ⊢ˢᵘ idˢ ∶ Γ

⊢ᵘidˢ {◇} = ◇
⊢ᵘidˢ {Γ ⨟ x ∶ A} = []
  (rnSbᵘ (wkRn ⊢ʳid) ⊢ᵘidˢ)
  (Var (isInNew refl))

-- Extensionality property of neutral substitutions
⊢ˢᵘExt :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  (_ : Sb[ Γ ] ∋ σ ~ σ')
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → --------------------
  Γ' ⊢ˢᵘ σ' ∶ Γ

⊢ˢᵘExt _ ◇ = ◇
⊢ˢᵘExt{σ}{σ'} e ([]{x = x} ⊢σ ⊢σx)
  rewrite e x (∈∪₂ ∈｛｝) = []
  (⊢ˢᵘExt (λ x' x'∈Γ → e x' (∈∪₁ x'∈Γ)) ⊢σ) ⊢σx

-- Weakening
wkSbᵘ :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → --------------------
  Γ' ⨟ x ∶ A ⊢ˢᵘ σ ∶ Γ

wkSbᵘ{σ = σ} q = ⊢ˢᵘExt
  (λ x _ → sbUnit (σ x))
  (rnSbᵘ (wkRn ⊢ʳid) q)

-- Lifting
[]ᵘ :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (⊢σ : Γ' ⊢ˢᵘ σ ∶ Γ)
  (⊢a : Γ' ⊢ᵘ a ∶ A)
  → --------------------------------
  Γ' ⊢ˢᵘ (σ ∘/ x := a) ∶ (Γ ⨟ x ∶ A)

[]ᵘ{Γ}{Γ'}{σ}{A}{a}{x} ⊢σ ⊢a = []
  (⊢ˢᵘExt (sbUpdate# σ it) ⊢σ )
  (subst (λ z → Γ' ⊢ᵘ z ∶ A)
    (symm (:=Eq{f = σ}{a} x))
    ⊢a)

liftSbᵘ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x y : 𝔸}
  ⦃ _ : x # dom Γ ⦄
  ⦃ _ : y # dom Γ' ⦄
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → --------------------------------------------
  Γ' ⨟ y ∶ A ⊢ˢᵘ (σ ∘/ x := 𝐯 y) ∶ Γ ⨟ x ∶ A

liftSbᵘ q = []ᵘ (wkSbᵘ q) (Var (isInNew refl))

-- Single substitution
ssbᵘ :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ᵘ a ∶ A)
  → ------------------------
  Γ ⊢ˢᵘ (x := a) ∶ (Γ ⨟ x ∶ A)

ssbᵘ = []ᵘ ⊢ᵘidˢ

-- Types of variables under neutral substitution
⊢ᵘsbVar :
  {σ : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : (x , A) isIn Γ)
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  → ------------------
  Γ' ⊢ᵘ σ x ∶ A

⊢ᵘsbVar (isInNew refl) ([] _ ⊢σx) = ⊢σx
⊢ᵘsbVar (isInOld p)    ([] q _)   = ⊢ᵘsbVar p q

----------------------------------------------------------------------
-- Neutral substitution preserves normal and neutral forms
----------------------------------------------------------------------
sb⊢ⁿ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  (_ : Γ ⊢ⁿ a ∶ A)
  → ----------------
  Γ' ⊢ⁿ σ * a ∶ A

sb⊢ᵘ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢᵘ σ ∶ Γ)
  (_ : Γ ⊢ᵘ a ∶ A)
  → ----------------
  Γ' ⊢ᵘ σ * a ∶ A

sb⊢ⁿ{σ}{Γ' = Γ'} p (Lam{A}{B}{b}{x} q x#b)
  with (x' , x'#σb ∉∪ x'#Γ') ← fresh (σ * b , Γ') = Lam
  (subst (λ c → Γ' ⨟ x' ∶ A ⊢ⁿ c ∶ B)
    (sbUpdate[] σ x (𝐯 x') b x#b)
    (sb⊢ⁿ (liftSbᵘ p) q))
  x'#σb
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
sb⊢ⁿ p Zero = Zero
sb⊢ⁿ p (Succ q) = Succ (sb⊢ⁿ p q)
sb⊢ⁿ p (Neu q) = Neu (sb⊢ᵘ p q)
sb⊢ᵘ{σ} p (Var{x = x} q)
  rewrite ‿unit (σ x) ⦃ ≤refl ⦄ = ⊢ᵘsbVar q p
sb⊢ᵘ p (App q₀ q₁) = App (sb⊢ᵘ p q₀) (sb⊢ⁿ p q₁)
sb⊢ᵘ p (Nrec q₀ q₁ q₂) = Nrec (sb⊢ⁿ p q₀) (sb⊢ⁿ p q₁) (sb⊢ᵘ p q₂)

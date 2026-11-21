module GST.Substitution where

open import Prelude
open import WSLN

open import GST.Syntax
open import GST.Context
open import GST.TypeSystem
open import GST.WellScoped
open import GST.Setoid
open import GST.Renaming

----------------------------------------------------------------------
-- Well-typed and convertible substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢ_∶_
data _⊢ˢ_∶_ (Γ' : Cx) : Sb → Cx → Set where
  ◇ :
    {σ : Sb}
    → ---------
    Γ' ⊢ˢ σ ∶ ◇
  [] :
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # dom Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ∶ Γ)
    (q₁ : Γ' ⊢ σ x ∶ A)
    → -------------------
    Γ' ⊢ˢ σ ∶ Γ ⨟ x ∶ A

infix 4 _⊢ˢ_＝_∶_
data _⊢ˢ_＝_∶_ (Γ' : Cx) : Sb → Sb → Cx → Set where
  ＝◇ :
    {σ σ' : Sb}
    → --------------
    Γ' ⊢ˢ σ ＝ σ' ∶ ◇
  ＝[] :
    {Γ : Cx}
    {σ σ' : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # dom Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
    (q₁ : Γ' ⊢ σ x ＝ σ' x ∶ A)
    → -------------------------
    Γ' ⊢ˢ σ ＝ σ' ∶ Γ ⨟ x ∶ A

⊢ʳ→⊢ˢ :
  {Γ Γ' : Cx}
  {ρ : Rn}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ---------------
  Γ' ⊢ˢ 𝐚∘ ρ ∶ Γ

⊢ʳ→⊢ˢ ◇ = ◇
⊢ʳ→⊢ˢ ([] q₀ q₁) = [] (⊢ʳ→⊢ˢ q₀) (Var q₁)

----------------------------------------------------------------------
-- Provable substitutions are well-scoped
----------------------------------------------------------------------
supp⊢ˢ :
  {Γ Γ' : Cx}
  {σ : Sb}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : x ∈ dom Γ)
  → -----------------
  supp (σ x) ⊆ dom Γ'

supp⊢ˢ ([] q _) (∈∪₁ p) = supp⊢ˢ q p
supp⊢ˢ ([] _ q) (∈∪₂ ∈｛｝) = supp⊢ q

supp⊢ˢ＝₁ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : x ∈ dom Γ)
  → ---------------------
  supp (σ x) ⊆ dom Γ'

supp⊢ˢ＝₁ (＝[] q _) (∈∪₁ p) = supp⊢ˢ＝₁ q p
supp⊢ˢ＝₁ (＝[] _ q) (∈∪₂ ∈｛｝) = supp＝₁ q

supp⊢ˢ＝₂ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : x ∈ dom Γ)
  → ---------------------
  supp (σ' x) ⊆ dom Γ'

supp⊢ˢ＝₂ (＝[] q _) (∈∪₁ p) = supp⊢ˢ＝₂ q p
supp⊢ˢ＝₂ (＝[] _ q) (∈∪₂ ∈｛｝) = supp＝₂ q

----------------------------------------------------------------------
-- Renaming well-typed substitutions
----------------------------------------------------------------------
rnSb :
  {Γ Γ' Γ'' : Cx}
  {ρ : Rn}
  {σ : Sb}
  (_ : Γ'' ⊢ʳ ρ ∶ Γ')
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -----------------
  Γ'' ⊢ˢ 𝐚∘ ρ ∘ σ ∶ Γ

rnSb q ◇ = ◇
rnSb q ([] p₀ p₁) = [] (rnSb q p₀) (rn⊢ q p₁)

rn＝Sb :
  {Γ Γ' Γ'' : Cx}
  {ρ : Rn}
  {σ₁ σ₂ : Sb}
  (_ : Γ'' ⊢ʳ ρ ∶ Γ')
  (_ : Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ)
  → -----------------------------
  Γ'' ⊢ˢ 𝐚∘ ρ ∘ σ₁ ＝ 𝐚∘ ρ ∘ σ₂ ∶ Γ

rn＝Sb q ＝◇ = ＝◇
rn＝Sb q (＝[] p₀ p₁) = ＝[] (rn＝Sb q p₀) (rn＝ q p₁)

----------------------------------------------------------------------
-- Renamings as substitutions
----------------------------------------------------------------------
rn2sb :
  {Γ Γ' : Cx}
  {ρ : Rn}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ---------------
  Γ' ⊢ˢ 𝐚∘ ρ ∶ Γ

rn2sb ◇         = ◇
rn2sb ([] p₀ p₁) = [] (rn2sb p₀) (Var p₁)

----------------------------------------------------------------------
-- Identity substitution is well-typed
----------------------------------------------------------------------
⊢idˢ :
  {Γ : Cx}
  → --------
  Γ ⊢ˢ idˢ ∶ Γ

⊢idˢ {◇} = ◇
⊢idˢ {Γ ⨟ x ∶ A} = []
  (rnSb (wkRn ⊢ʳid) ⊢idˢ)
  (Var (isInNew refl))

⊢idˢ＝idˢ :
  {Γ : Cx}
  → -------------
  Γ ⊢ˢ idˢ ＝ idˢ ∶ Γ

⊢idˢ＝idˢ {◇} = ＝◇
⊢idˢ＝idˢ {Γ ⨟ x ∶ A} = ＝[]
  (rn＝Sb (wkRn ⊢ʳid) ⊢idˢ＝idˢ)
  (Refl (Var (isInNew refl)))

----------------------------------------------------------------------
-- Eqivalence relation
----------------------------------------------------------------------
＝∶Refl :
  {σ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  Γ' ⊢ˢ σ ＝ σ ∶ Γ
＝∶Refl ◇        = ＝◇
＝∶Refl ([] p₀ p₁) = ＝[] (＝∶Refl p₀) (Refl p₁)

＝∶Symm :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → --------------------
  Γ' ⊢ˢ σ' ＝ σ ∶ Γ

＝∶Symm ＝◇ = ＝◇
＝∶Symm (＝[] q₀ q₁) = ＝[] (＝∶Symm q₀) (Symm q₁)

＝∶Trans :
  {σ σ' σ'' : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ' ⊢ˢ σ' ＝ σ'' ∶ Γ)
  → --------------------
  Γ' ⊢ˢ σ ＝ σ'' ∶ Γ

＝∶Trans ＝◇ ＝◇ = ＝◇
＝∶Trans (＝[] q₀ q₁) (＝[] q₀' q₁') =
  ＝[] (＝∶Trans q₀ q₀') (Trans q₁ q₁')

----------------------------------------------------------------------
-- Setoid of substitutions in a given context
----------------------------------------------------------------------
Sb[_] : Cx → Setd

∣ Sb[ Γ ] ∣ = Sb
Sb[ Γ ] ∋ σ ~ σ' = ∀ x → x ∈ dom Γ → σ x ≡ σ' x
~Refl Sb[ Γ ] _ _ _ = refl
~Symm Sb[ Γ ] e x r = symm (e x r )
~Trans Sb[ Γ ] e e' x r = trans (e x r) (e' x r)

sbUpdate# :
  {Γ : Cx}
  {x : 𝔸}
  {a : Tm}
  (σ : Sb)
  (_ : x # Γ)
  → -------------------------
  Sb[ Γ ] ∋  σ ~ (σ ∘/ x := a)

sbUpdate# {x = x} _ x#Γ y y∈Γ with x ≐ y
... | no _ = refl
... | equ = Øelim (∉→¬∈ x#Γ y∈Γ)

----------------------------------------------------------------------
-- Extensionality properties of well-typed substitutions
----------------------------------------------------------------------
⊢ˢExt :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  (_ : Sb[ Γ ] ∋ σ ~ σ')
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → --------------------
  Γ' ⊢ˢ σ' ∶ Γ

⊢ˢExt _ ◇ = ◇
⊢ˢExt{σ}{σ'} e ([]{x = x} ⊢σ ⊢σx)
  rewrite e x (∈∪₂ ∈｛｝) = []
  (⊢ˢExt (λ x' x'∈Γ → e x' (∈∪₁ x'∈Γ)) ⊢σ) ⊢σx

⊢ˢ＝Ext :
  {σ' τ' σ τ : Sb}
  {Γ Γ' : Cx}
  (_ : Sb[ Γ ] ∋ σ ~ σ')
  (_ : Sb[ Γ ] ∋ τ ~ τ')
  (_ : Γ' ⊢ˢ σ ＝ τ ∶ Γ)
  → --------------------
  Γ' ⊢ˢ σ' ＝ τ' ∶ Γ

⊢ˢ＝Ext _ _ ＝◇ = ＝◇
⊢ˢ＝Ext{σ'}{τ'} e e' (＝[]{σ = σ}{τ}{A = A}{x} σ=τ σx=σ'x)
  rewrite e x (∈∪₂ ∈｛｝)
  | e' x (∈∪₂ ∈｛｝) = ＝[]
  (⊢ˢ＝Ext (λ y y∈Γ → e y (∈∪₁ y∈Γ)) (λ y y∈Γ → e' y (∈∪₁ y∈Γ)) σ=τ)
  σx=σ'x

⊢ˢ≡Ext :
  {σ' σ  : Sb}
  {Γ Γ' : Cx}
  (_ : Sb[ Γ ] ∋ σ ~ σ')
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → --------------------
  Γ' ⊢ˢ σ ＝ σ' ∶ Γ

⊢ˢ≡Ext e q = ⊢ˢ＝Ext (λ _ _ → refl) e (＝∶Refl q)

----------------------------------------------------------------------
-- Action of equal renamings on equal substitutions
----------------------------------------------------------------------
rn＝Sb' :
  {Γ Γ' Γ'' : Cx}
  {ρ ρ' : Rn}
  {σ₁ σ₂ : Sb}
  (_ : Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ)
  (_ : Γ'' ⊢ʳ ρ ∶ Γ')
  (_ : Rn[ Γ' ] ∋ ρ ~ ρ')
  → ----------------------------------
  Γ'' ⊢ˢ 𝐚∘ ρ ∘ˢ σ₁ ＝ 𝐚∘ ρ' ∘ˢ σ₂ ∶ Γ

rn＝Sb'{ρ = ρ}{ρ'}{σ₂ = σ₂} q p e = ⊢ˢ＝Ext
  (λ _ _ → refl)
  (λ x r → rnRespSupp ρ ρ'
    (σ₂ x)
    λ y s → e y (supp⊢ˢ＝₂ q r s))
  (rn＝Sb p q)

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wkSb :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  ⦃ _ : x # Γ' ⦄
  → -------------------
  Γ' ⨟ x ∶ A ⊢ˢ σ ∶ Γ

wkSb{σ = σ} q = ⊢ˢExt
  (λ x _ → sbUnit (σ x))
  (rnSb (wkRn ⊢ʳid) q)

wk＝Sb :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  ⦃ _ : x # dom Γ' ⦄
  → -------------------------
  Γ' ⨟ x ∶ A ⊢ˢ σ ＝ σ' ∶ Γ

wk＝Sb{σ = σ}{σ'} q = ⊢ˢ＝Ext
  (λ x _ → sbUnit (σ x))
  (λ x _ → sbUnit (σ' x))
  (rn＝Sb (wkRn ⊢ʳid) q)

----------------------------------------------------------------------
-- Lifting
----------------------------------------------------------------------
[]' :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (⊢σ : Γ' ⊢ˢ σ ∶ Γ)
  (⊢a : Γ' ⊢ a ∶ A)
  → -------------------------------
  Γ' ⊢ˢ (σ ∘/ x := a) ∶ Γ ⨟ x ∶ A

[]'{Γ}{Γ'}{σ}{A}{a}{x} ⊢σ ⊢a = []
  (⊢ˢExt (sbUpdate# σ it) ⊢σ )
  (subst (λ z → Γ' ⊢ z ∶ A)
    (symm (:=Eq{f = σ}{a} x))
    ⊢a)

＝[]' :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (σ=σ' : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (a=a' : Γ' ⊢ a ＝ a' ∶ A)
  → --------------------------------------------------
  Γ' ⊢ˢ (σ ∘/ x := a) ＝ (σ' ∘/ x := a') ∶ Γ ⨟ x ∶ A

＝[]'{Γ}{Γ'}{σ}{σ'}{A}{a}{a'}{x} σ=σ' a=a' = ＝[]
  (⊢ˢ＝Ext (sbUpdate# σ it) (sbUpdate# σ' it) σ=σ')
  (subst₂ (λ z z' → Γ' ⊢ z ＝ z' ∶ A)
    (symm (:=Eq{f = σ}{a} x))
    (symm (:=Eq{f = σ'}{a'} x))
    a=a')

[]'# :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (⊢σ : Γ' ⊢ˢ σ ∶ Γ)
  (⊢a : Γ' ⊢ a ∶ A)
  → --------------------------
  Γ' ⊢ˢ (σ ∘/ x := a) ＝ σ ∶ Γ

[]'# {Γ}{σ = σ} ⊢σ ⊢a = ⊢ˢ＝Ext
  (sbUpdate# σ it)
  (~Refl (Sb[ Γ ]) σ)
  (＝∶Refl ⊢σ)

liftSb :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x y : 𝔸}
  ⦃ _ : x # dom Γ ⦄
  ⦃ _ : y # dom Γ' ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -------------------------------------------
  Γ' ⨟ y ∶ A ⊢ˢ (σ ∘/ x := 𝐯 y) ∶ Γ ⨟ x ∶ A

liftSb q = []' (wkSb q) (Var (isInNew refl))


lift＝Sb :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x y : 𝔸}
  ⦃ _ : x # dom Γ ⦄
  ⦃ _ : y # dom Γ' ⦄
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → ---------------------------------------------------------------
  Γ' ⨟ y ∶ A ⊢ˢ (σ ∘/ x := 𝐯 y) ＝ (σ' ∘/ x := 𝐯 y) ∶ Γ ⨟ x ∶ A

lift＝Sb q = ＝[]' (wk＝Sb q) (Refl (Var (isInNew refl)))

----------------------------------------------------------------------
-- Single substitution
----------------------------------------------------------------------
ssb∶ :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # dom Γ ⦄
  (_ : Γ ⊢ a ∶ A)
  → -------------------------
  Γ ⊢ˢ (x := a) ∶ Γ ⨟ x ∶ A

ssb∶ = []' ⊢idˢ

ssb＝∶ :
  {Γ : Cx}
  {x : 𝔸}
  {a a' : Tm}
  {A : Ty}
  ⦃ _ : x # dom Γ ⦄
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → --------------------------------------
  Γ ⊢ˢ (x := a) ＝ (x := a') ∶ Γ ⨟ x ∶ A

ssb＝∶ = ＝[]' ⊢idˢ＝idˢ

----------------------------------------------------------------------
-- Types of variables under substitution
----------------------------------------------------------------------
⊢sbVar :
  {σ : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : (x , A) isIn Γ)
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ------------------
  Γ' ⊢ σ x ∶ A

⊢sbVar (isInNew refl) ([] _ ⊢σx) = ⊢σx
⊢sbVar (isInOld p)    ([] q _)   = ⊢sbVar p q

⊢sbConvVar :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_  : (x , A) isIn Γ)
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → --------------------
  Γ' ⊢ σ x ＝ σ' x ∶ A

⊢sbConvVar (isInNew refl) (＝[] _ σx＝σ'x) = σx＝σ'x
⊢sbConvVar (isInOld p)    (＝[] q _)       = ⊢sbConvVar p q

----------------------------------------------------------------------
-- Substitution preserves typing
----------------------------------------------------------------------
sb⊢ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ a ∶ A)
  → --------------
  Γ' ⊢ σ * a ∶ A

sb⊢{σ} p (Var{x = x} q)
  rewrite ‿unit (σ x) ⦃ ≤refl ⦄ = ⊢sbVar q p
sb⊢{σ}{Γ' = Γ'} p (Lam{A}{B}{b}{x} q x#b)
  with (x' , x'#σb ∉∪ x'#Γ') ← fresh (σ * b , Γ') = Lam
  (subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
    (sbUpdate[] σ x (𝐯 x') b x#b)
    (sb⊢ (liftSb p) q))
  x'#σb
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
sb⊢ p (App q₀ q₁) = App (sb⊢ p q₀) (sb⊢ p q₁)
sb⊢ p Zero = Zero
sb⊢ p (Succ q) = Succ (sb⊢ p q)
sb⊢ p (Nrec q₀ q₁ q₂) = Nrec (sb⊢ p q₀) (sb⊢ p q₁) (sb⊢ p q₂)

sb⊢¹ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A B : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (b : Tm[ 1 ])
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⨟ x ∶ A ⊢ b [ x ] ∶ B)
  (_ : x # b)
  (_ : x' # b)
  → --------------------------------
  Γ' ⨟ x' ∶ A ⊢ (σ * b) [ x' ] ∶ B

sb⊢¹{σ}{Γ' = Γ'}{A}{B}{x}{x'} b p q x#b x'#b =
  subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
    (sbUpdate[] σ x (𝐯 x') b x#b)
    (sb⊢ (liftSb p) q)

----------------------------------------------------------------------
-- Substitution preserves conversion
----------------------------------------------------------------------
sbConv :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → ----------------------
  Γ' ⊢ σ * a ＝ σ * a' ∶ A

sbConv p (Refl q) = Refl (sb⊢ p q)
sbConv p (Symm q) = Symm (sbConv p q)
sbConv p (Trans q₀ q₁) = Trans (sbConv p q₀) (sbConv p q₁)
sbConv{σ}{Γ' = Γ'} p (Lam{A}{B}{b}{b'}{x} q (x#b ∉∪ x#b'))
  with (x' , x'# ∉∪ x'#Γ') ← fresh ((σ * b , σ * b') , Γ') = Lam
    (subst₂ (λ c c' → Γ' ⨟ x' ∶ A ⊢ c ＝ c' ∶ B)
      (sbUpdate[] σ x (𝐯 x') b x#b)
      (sbUpdate[] σ x (𝐯 x') b' x#b')
      (sbConv (liftSb p) q))
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
sbConv p (App q₀ q₁) = App (sbConv p q₀) (sbConv p q₁)
sbConv p (Succ q) = Succ (sbConv p q)
sbConv p (Nrec q₀ q₁ q₂) =
  Nrec (sbConv p q₀) (sbConv p q₁) (sbConv p q₂)
sbConv{σ}{Γ' = Γ'} p (BetaLam{A}{B}{a}{b}{x} q₀ q₁ x#b)
  with (x' , x'# ∉∪ x'#Γ') ← fresh (σ * b , Γ')
  rewrite sb[] σ b a =
  BetaLam{b = σ * b}
    (subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
        (sbUpdate[] σ x (𝐯 x') b x#b)
        (sb⊢ (liftSb p) q₀))
    (sb⊢ p q₁)
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
sbConv p (BetaZero q₀ q₁) =
  BetaZero (sb⊢ p q₀) (sb⊢ p q₁)
sbConv p (BetaSucc q₀ q₁ q₂) =
  BetaSucc (sb⊢ p q₀) (sb⊢ p q₁) (sb⊢ p q₂)
sbConv{σ}{Γ' = Γ'} p (Eta{b = b}{x} q x#b)
  with (x' , x'# ∉∪ x'∉Γ') ← fresh (σ * b , Γ')
  rewrite
    (sbAbs σ x x' (b ∙ 𝐯 x)
      λ{y (∈∪₁ q') _ → ⊆∉ (supp⊢ˢ p (supp⊢ q q')) x'∉Γ' ;
        y (∈∪₂ (∈∪₁ ∈｛｝)) q' → Øelim (q' refl)})
  | :=Eq {f = σ}{𝐯 x'} x
  | updateFresh σ x (𝐯 x') b x#b =
  Eta{x = x'} (sb⊢ p q) x'#

sb＝Conv :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ∶ A)
  → ----------------------
  Γ' ⊢ σ * a ＝ σ' * a ∶ A

sb＝Conv{σ}{σ'} p (Var{x = x} q)
  rewrite ‿unit (σ x) ⦃ ≤refl ⦄
  | ‿unit (σ' x) ⦃ ≤refl ⦄ = ⊢sbConvVar q p
sb＝Conv{σ}{σ'}{Γ' = Γ'} p (Lam{A}{B}{b}{x} q x#b)
  with (x' , x'# ∉∪ x'#Γ') ← fresh ((σ * b , σ' * b) , Γ') =
  Lam
    (subst₂ (λ c c' → Γ' ⨟ x' ∶ A ⊢ c ＝ c' ∶ B)
      (sbUpdate[] σ x (𝐯 x') b x#b)
      (sbUpdate[] σ' x (𝐯 x') b x#b)
      (sb＝Conv (lift＝Sb p) q))
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'
sb＝Conv p (App q₀ q₁) = App
  (sb＝Conv p q₀)
  (sb＝Conv p q₁)
sb＝Conv p Zero = Refl Zero
sb＝Conv p (Succ q) = Succ (sb＝Conv p q)
sb＝Conv p (Nrec q₀ q₁ q₂) = Nrec
  (sb＝Conv p q₀)
  (sb＝Conv p q₁)
  (sb＝Conv p q₂)

----------------------------------------------------------------------
-- Concretion preserves typing
----------------------------------------------------------------------
⊢conc :
  {Γ : Cx}
  {A B : Ty}
  {a : Tm}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⨟ x ∶ A ⊢ b [ x ] ∶ B)
  (_ : Γ ⊢ a ∶ A)
  (_ : x # b)
  → ---------------------------
  Γ ⊢ b [ a ] ∶ B

⊢conc{Γ}{B = B}{a} b x p q x#b =
  subst (λ z → Γ ⊢ z ∶ B)
    (ssb[] x a b x#b)
    (sb⊢ (ssb∶ q) p)

----------------------------------------------------------------------
-- Reflexivity Inversion
----------------------------------------------------------------------
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
  → -------------------
  Γ ⊢ a' ∶ A

⊢ty₁ (Refl q) = q
⊢ty₁ (Symm q) = ⊢ty₂ q
⊢ty₁ (Trans q _) = ⊢ty₁ q
⊢ty₁ (Lam q (x#b ∉∪ _)) = Lam (⊢ty₁ q) x#b
⊢ty₁ (App q₀ q₁) = App (⊢ty₁ q₀) (⊢ty₁ q₁)
⊢ty₁ (Succ q) = Succ (⊢ty₁ q)
⊢ty₁ (Nrec q₀ q₁ q₂) =
  Nrec (⊢ty₁ q₀) (⊢ty₁ q₁) (⊢ty₁ q₂)
⊢ty₁ (BetaLam q₀ q₁ x#b) = App (Lam q₀ x#b) q₁
⊢ty₁ (BetaZero q₀ q₁) = Nrec q₀ q₁ Zero
⊢ty₁ (BetaSucc q₀ q₁ q₂) = Nrec q₀ q₁ (Succ q₂)
⊢ty₁ (Eta q _) = q

⊢ty₂ (Refl q) = q
⊢ty₂ (Symm q) = ⊢ty₁ q
⊢ty₂ (Trans _ q) = ⊢ty₂ q
⊢ty₂ (Lam q (_ ∉∪ x#b')) = Lam (⊢ty₂ q) x#b'
⊢ty₂ (App q₀ q₁) = App (⊢ty₂ q₀) (⊢ty₂ q₁)
⊢ty₂ (Succ q) = Succ (⊢ty₂ q)
⊢ty₂ (Nrec q₀ q₁ q₂) =
  Nrec (⊢ty₂ q₀) (⊢ty₂ q₁) (⊢ty₂ q₂)
⊢ty₂ (BetaLam{b = b}{x} q₀ q₁ x#b) =
  -- here we need the fact that concretion preserves typing,
  -- which in turn depends on the fact that
  -- susbtitution preserves typing
  ⊢conc b x q₀ q₁ x#b
⊢ty₂ (BetaZero q _) = q
⊢ty₂ (BetaSucc q₀ q₁ q₂) = App (App q₁ q₂) (Nrec q₀ q₁ q₂)
⊢ty₂{Γ} (Eta{A}{B}{b}{x} q  x#b)
  with (x' , x'#x ∉∪ x'#b ∉∪ x'#Γ) ← fresh (x , b , Γ) =
  Lam{x = x'}  q' (#abs' (b ∙ 𝐯 x) (x'#b ∉∪ x'#x ∉∪ ∉∅))
  where
  instance
   _ : x' # Γ
   _ = x'#Γ
  q' : Γ ⨟ x' ∶ A ⊢ (x ． b ∙ 𝐯 x)[ x' ] ∶ B
  q' rewrite concAbs x (b ∙ 𝐯 x) (𝐯 x')
     | ssbFresh x (𝐯 x') b x#b
     | updateEq{idˢ}{𝐯 x'} x =
    App (wk⊢ q) (Var (isInNew refl))

----------------------------------------------------------------------
-- Reflexivity Inversion for substitutions
----------------------------------------------------------------------
⊢sb₁ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  (_ : Γ ⊢ˢ σ ＝ σ' ∶ Γ')
  → ---------------------
  Γ ⊢ˢ σ ∶ Γ'

⊢sb₁ ＝◇         = ◇
⊢sb₁ (＝[] q₀ q₁) = [] (⊢sb₁ q₀) (⊢ty₁ q₁)

⊢sb₂ :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  (_ : Γ ⊢ˢ σ ＝ σ' ∶ Γ')
  → ---------------------
  Γ ⊢ˢ σ' ∶ Γ'

⊢sb₂ ＝◇         = ◇
⊢sb₂ (＝[] q₀ q₁) = [] (⊢sb₂ q₀) (⊢ty₂ q₁)

----------------------------------------------------------------------
-- Substitution preserves conversion, continued
----------------------------------------------------------------------
-- Now we have reflexivity inversion, we can prove:
sb＝ :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  → -----------------------
  Γ' ⊢ σ * a ＝ σ' * a' ∶ A

sb＝ p q = Trans (sb＝Conv p (⊢ty₁ q)) (sbConv (⊢sb₂ p) q)

sb＝¹ :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A B : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (b b' : Tm[ 1 ])
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⨟ x ∶ A ⊢ b [ x ] ＝ b' [ x ] ∶ B)
  (_ : x # (b , b'))
  (_ : x' # (b , b'))
  → --------------------------------------------------
  Γ' ⨟ x' ∶ A ⊢ (σ * b) [ x' ] ＝ (σ' * b') [ x' ] ∶ B

sb＝¹{σ}{σ'}{Γ' = Γ'}{A}{B}{x}{x'}
  b b' p q (x#b ∉∪ x#b') (x'#b ∉∪ x'#b') =
  subst₂ (λ c c' → Γ' ⨟ x' ∶ A ⊢ c ＝ c' ∶ B)
    (sbUpdate[] σ x (𝐯 x') b x#b)
    (sbUpdate[] σ' x (𝐯 x') b' x#b')
    (sb＝ (lift＝Sb p) q)

----------------------------------------------------------------------
-- Composing well-typed substitutions
----------------------------------------------------------------------
⊢ˢ∘ :
  {Γ Γ' Γ'' : Cx}
  {σ σ' : Sb}
  (_ : Γ'' ⊢ˢ σ' ∶ Γ')
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -----------------
  Γ'' ⊢ˢ σ' ∘ˢ σ ∶ Γ

⊢ˢ∘ q ◇ = ◇
⊢ˢ∘ q ([] p₀ p₁) = [] (⊢ˢ∘ q p₀) (sb⊢ q p₁)

⊢ˢ＝∘ :
  {Γ Γ' Γ'' : Cx}
  {σ₁ σ₂ σ₁' σ₂' : Sb}
  (_ : Γ'' ⊢ˢ σ₁' ＝ σ₂' ∶ Γ')
  (_ : Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ)
  → -------------------------------
  Γ'' ⊢ˢ σ₁' ∘ˢ σ₁ ＝ σ₂' ∘ˢ σ₂ ∶ Γ

⊢ˢ＝∘ q ＝◇ = ＝◇
⊢ˢ＝∘ q (＝[] p₀ p₁) = ＝[] (⊢ˢ＝∘ q p₀) (sb＝ q p₁)

----------------------------------------------------------------------
-- Unitary and associative laws for substitution composition
----------------------------------------------------------------------
⊢sbUnit :
  {σ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -------------------
  Γ' ⊢ˢ idˢ ∘ˢ σ ＝ σ ∶ Γ
⊢sbUnit {σ} q = ＝∶Symm (⊢ˢ≡Ext
  (λ x _ → symm (sbUnit (σ x)))
  q)

⊢sbAssoc :
  {σ₁ σ₂ σ₃ : Sb}
  {Γ Γ' Γ'' Γ''' : Cx}
  (_ : Γ''' ⊢ˢ σ₃ ∶ Γ'')
  (_ : Γ'' ⊢ˢ σ₂ ∶ Γ')
  (_ : Γ' ⊢ˢ σ₁ ∶ Γ)
  → ----------------------------------------------
  Γ''' ⊢ˢ (σ₃ ∘ˢ σ₂) ∘ˢ σ₁ ＝ σ₃ ∘ˢ (σ₂ ∘ˢ σ₁) ∶ Γ
⊢sbAssoc {σ₁}{σ₂}{σ₃} q₃ q₂ q₁ = ⊢ˢ≡Ext
  (λ x r → sbAssoc σ₂ σ₃ (σ₁ x))
  (⊢ˢ∘ (⊢ˢ∘ q₃ q₂) q₁)

----------------------------------------------------------------------
-- Concretion preserves conversion
----------------------------------------------------------------------
＝conc :
  {Γ : Cx}
  {A B : Ty}
  {a a' : Tm}
  (b b' : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⨟ x ∶ A ⊢
    b [ x ] ＝ b' [ x ] ∶ B)
  (_ : Γ ⊢ a ＝ a' ∶ A)
  (_ : x # (b , b'))
  → --------------------------
  Γ ⊢ b [ a ] ＝ b' [ a' ] ∶ B

＝conc{Γ}{B = B}{a}{a'} b b' x p q (x#b ∉∪ x#b') =
  subst₂ (λ z z' → Γ ⊢ z ＝ z' ∶ B)
    (ssb[] x a b x#b)
    (ssb[] x a' b' x#b')
    (sb＝ (ssb＝∶ q) p)

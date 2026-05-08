module GST.TypeSemantics where

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
open import GST.NormalForm
open import GST.Presheaf

----------------------------------------------------------------------
-- Presheaf of normal forms
----------------------------------------------------------------------
record ∣Norm∣ (A : Ty)(Γ : Cx) : Set where
  constructor mk∣Norm∣
  field
    nt : Tm
    pf : Γ ⊢ⁿ nt ∶ A

open ∣Norm∣ public

Norm : Ty → ℝ^

∣ Norm A ⊙ Γ ∣ = ∣Norm∣ A Γ
Norm A ⊙ Γ ∋ a ~ a' = nt a ≡ nt a'
~Refl (Norm _ ⊙ _) _ = refl
~Symm (Norm _ ⊙ _) refl = refl
~Trans (Norm _ ⊙ _) refl refl = refl
(⊙cong (Norm A) ₀ p) ₀ a =
  mk∣Norm∣ (rn p * nt a) (rn⊢ⁿ (pf p) (pf a))
(⊙cong (Norm _) ₀ _) ₁ refl = refl
(_₁_ (⊙cong (Norm A)) {p}{p'} e) a =
  rnRespSupp (rn p) (rn p') (nt a)
  (λ x r → e x (supp⊢ (tyⁿ (pf a)) r))
⊙unit (Norm _) _ a = rnUnit (nt a)
⊙assoc (Norm _) p q a =
  rnAssoc (rn p) (rn q) (nt a)

----------------------------------------------------------------------
-- Presheaf of neutral forms
----------------------------------------------------------------------
record ∣Neut∣ (A : Ty)(Γ : Cx) : Set where
  constructor mk∣Neut∣
  field
    ut : Tm
    pf :  Γ ⊢ᵘ ut ∶ A

open ∣Neut∣ public

Neut : Ty → ℝ^

∣ Neut A ⊙ Γ ∣ = ∣Neut∣ A Γ
Neut _ ⊙ _ ∋ a ~ a' = ut a ≡ ut a'
~Refl (Neut _ ⊙ _) _ = refl
~Symm (Neut _ ⊙ _) refl = refl
~Trans (Neut _ ⊙ _) refl refl = refl
(⊙cong (Neut A) ₀ p) ₀ a =
  mk∣Neut∣ (rn p * ut a) (rn⊢ᵘ (pf p) (pf a))
(⊙cong (Neut _) ₀ _) ₁ refl = refl
(_₁_ (⊙cong (Neut A)) {p}{p'} e) a =
  rnRespSupp (rn p) (rn p') (ut a)
  (λ x r → e x (supp⊢ (tyᵘ (pf a)) r))
⊙unit (Neut _) _ a = rnUnit (ut a)
⊙assoc (Neut _) p q a =
  rnAssoc (rn p) (rn q) (ut a)

-- Fresh variable
newvar :
  {Γ : Cx}
  (x : 𝔸)
  (A : Ty)
  ⦃ _ : x # Γ ⦄
  → ------------------------
  ∣ Neut A ⊙ (Γ ⨟ x ∶ A) ∣

newvar x A =
  mk∣Neut∣ (𝐯 x) (Var (isInNew refl))

-- Natural transformation from neutral forms to normal forms
neu : ∀{A} → ℝ^[ Neut A ⟶ Norm A ]

nt (hom neu ₀ a) = ut a
pf (hom neu ₀ a) = Neu (pf a)
hom neu ₁ refl = refl
ntl neu _ _ = refl

----------------------------------------------------------------------
-- Presheaf semantics of types
----------------------------------------------------------------------
𝓓 : Ty → ℝ^

𝓓 𝐍𝐚𝐭     = Norm 𝐍𝐚𝐭
𝓓 (A ⇒ B) = 𝓓 A →^ 𝓓 B

----------------------------------------------------------------------
-- Presheaf semantics of contexts : semantic environments
----------------------------------------------------------------------
𝓔 : Cx → ℝ^

𝓔 ◇             = 1^
𝓔 (Γ ⨟ _ ∶ A) = 𝓔 Γ ×^ 𝓓 A

-- Value of an environment at a variable
val :
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : (x , A) isIn  Γ)
  → ---------------------
  ℝ^[ 𝓔 Γ ⟶ 𝓓 A ]

hom (val (isInNew refl)) ₀ (_ , 𝓪) = 𝓪
hom (val (isInOld q)) ₀ (𝓼 , _) =
  hom (val q) ₀ 𝓼
hom (val (isInNew refl)) ₁ (_ , e) = e
hom (val (isInOld q)) ₁ (e , _) =
  hom (val q) ₁ e
ntl (val{_ ⨟ _ ∶ A} (isInNew refl)) {_}{Γ} p (_ , 𝓪) =
  ~Refl (𝓓 A ⊙ Γ) (𝓓 A ⊙′ p ₀ 𝓪)
ntl (val (isInOld q)) p (𝓼 , _) = ntl (val q) p 𝓼

val₁ :
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  {𝓼 𝓼' : ∣ 𝓔 Γ ⊙ Γ' ∣}
  (q : (x , A) isIn  Γ)
  (q' : (x' , A) isIn  Γ)
  (_ : x ≡ x')
  (_ : 𝓔 Γ ⊙ Γ' ∋ 𝓼 ~ 𝓼')
  → --------------------------------------------
  𝓓 A ⊙ Γ' ∋ hom (val q) ₀ 𝓼 ~ hom (val q') ₀ 𝓼'

val₁ {Γ} q q' refl 𝓮
  with refl ← ! ⦃ isPropIsIn ⦄ q q' = hom (val q) ₁ 𝓮

----------------------------------------------------------------------
-- Post-composing a semantic enviroment with a variable renaming
----------------------------------------------------------------------
infixr 6 _⊚_
_⊚_ :
  {Γ Γ' Γ'' : Cx}
  (p : ℝ[ Γ' ⟶ Γ ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  → ------------------
  ∣ 𝓔 Γ ⊙ Γ'' ∣

_⊚_ {◇} _ _ = tt
_⊚_ {_ ⨟ _ ∶ _} (mkℝ[⟶] ρ ([] p q)) 𝓼 =
  (mkℝ[⟶] ρ p ⊚ 𝓼 , hom (val q) ₀ 𝓼)

infixr 6 _⊚₁_
_⊚₁_ :
  {Γ Γ' Γ'' : Cx}
  {p p' : ℝ[ Γ' ⟶ Γ ]}
  {𝓼 𝓼' : ∣ 𝓔 Γ' ⊙ Γ'' ∣}
  (_ : Γ' →ᵣ Γ ∋ p ~ p')
  (_ : 𝓔 Γ' ⊙ Γ'' ∋ 𝓼 ~ 𝓼')
  → -------------------------
  𝓔 Γ ⊙ Γ'' ∋ p ⊚ 𝓼 ~ p' ⊚ 𝓼'

_⊚₁_ {◇} _ _ = tt
_⊚₁_ {Γ ⨟ x ∶ A}{Γ'' = Γ''}
     {p = mkℝ[⟶] ρ ([] p q)}
     {mkℝ[⟶] ρ' ([] p' q')} {𝓼} {𝓼'} e 𝓮 =
     ((λ x r → e x (∈∪₁ r)) ⊚₁ 𝓮 , val₁ q q' (e x (∈∪₂ ∈｛｝)) 𝓮)

ntl⊚ :
  {Γ Γ' Γ'' Γ''' : Cx}
  (p : ℝ[ Γ' ⟶ Γ ])
  (p' : ℝ[ Γ''' ⟶ Γ'' ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  → -----------------------------------------
  𝓔 Γ ⊙ Γ''' ∋
  p ⊚ (𝓔 Γ' ⊙′ p' ₀ 𝓼) ~ (𝓔 Γ ⊙′ p') ₀ (p ⊚ 𝓼)

ntl⊚ {◇} _ _ _ = tt
ntl⊚ {_ ⨟ _ ∶ _} (mkℝ[⟶] ρ ([] p q)) p' 𝓼 =
  (ntl⊚ (mkℝ[⟶] ρ p) p' 𝓼 , ntl (val q) p' 𝓼)

renVal :
  {Γ Γ' Γ'' : Cx}
  {A : Ty}
  {x : 𝔸}
  (p : ℝ[ Γ' ⟶ Γ ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (q : (x , A) isIn  Γ)
  -- helper hypotheses
  (q' : (rn p x , A) isIn  Γ')
  → --------------------------------------------------
  𝓓 A ⊙ Γ'' ∋ hom (val q') ₀ 𝓼 ~ hom (val q) ₀ (p ⊚ 𝓼)

renVal{Γ ⨟ _ ∶ A}{Γ'' = Γ''}
  (mkℝ[⟶] _ ([] p p')) 𝓼 (isInNew refl) q
  with refl ← ! ⦃ isPropIsIn ⦄ p' q =
  ~Refl (𝓓 A ⊙ Γ'') (hom (val p') ₀ 𝓼)
renVal{Γ ⨟ _ ∶ _}
  (mkℝ[⟶] ρ ([] p _))  𝓼 (isInOld q) q' =
  renVal{Γ} (mkℝ[⟶] ρ p) 𝓼 q q'

renWk :
  {Γ Γ' Γ'' : Cx}
  {x : 𝔸}
  (p : ℝ[ Γ' ⟶ Γ ])
  ⦃ _ : x # Γ' ⦄
  (A : Ty)
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (𝓪 : ∣ 𝓓 A ⊙ Γ'' ∣)
  → -----------------------------
  (wkrn p A) ⊚ (𝓼 , 𝓪) ≡ p ⊚ 𝓼

renWk {◇} _ _ _ _ = refl
renWk {Γ ⨟ _ ∶ A'} (mkℝ[⟶] ρ ([] p q)) A 𝓼 𝓪
   rewrite renWk{Γ} (mkℝ[⟶] ρ p) A 𝓼 𝓪 = refl

⊚unit :
  {Γ Γ' : Cx}
  (𝓼 : ∣ 𝓔 Γ ⊙ Γ' ∣)
  → ----------------
  idr Γ ⊚ 𝓼 ≡ 𝓼

⊚unit {◇} _ = refl
⊚unit {Γ ⨟ _ ∶ A} (𝓼 , 𝓪)
   = cong (_, 𝓪) (trans
     (renWk (mkℝ[⟶] id ⊢ʳid) A 𝓼 𝓪)
     (⊚unit {Γ} 𝓼))

renUpdate :
  {Γ Γ' Γ'' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (p : ℝ[ Γ' ⟶ Γ ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (𝓪 : ∣ 𝓓 A ⊙ Γ'' ∣)
  → -----------------------------------
  𝓔 (Γ ⨟ x ∶ A) ⊙ Γ'' ∋
  (p ⋉[ x , x' ] A) ⊚ (𝓼 , 𝓪) ~ (p ⊚ 𝓼 , 𝓪)

renUpdate {Γ}{Γ'}{Γ''}{A}{x}{x'} p 𝓼 𝓪 = (e₁ , e₂)
  where
  e₁' : 𝓔 Γ ⊙ Γ'' ∋ (wkrn p A) ⊚ (𝓼 , 𝓪)
        ~
        p ⊚ 𝓼
  e₁' rewrite renWk p A 𝓼 𝓪 = ~Refl (𝓔 Γ ⊙ Γ'') (p ⊚ 𝓼)

  e₁ : 𝓔 Γ ⊙ Γ'' ∋
    mkℝ[⟶] (rn p ∘/ x := x')
      (⊢ʳExt (rnUpdate# (rn p) it) (wkRn (pf p)))
      ⊚ (𝓼 , 𝓪)
    ~
    p ⊚ 𝓼
  e₁ = ~Trans (𝓔 Γ ⊙ Γ'')
    (~Symm Rn[ _ ] (rnUpdate# (rn p) it)
     ⊚₁
     ~Refl (𝓔 (Γ' ⨟ x' ∶ A) ⊙ Γ'') (𝓼 , 𝓪))
    e₁'

  e₂ : 𝓓 A ⊙ Γ'' ∋
    hom (val{Γ' ⨟ x' ∶ A}{A}
      (subst (λ z → (z , A) isIn  Γ' ⨟ x' ∶ A)
        (symm (:=Eq{f = rn p} x))
        (isInNew refl))) ₀ (𝓼 , 𝓪)
    ~
    𝓪
  e₂ rewrite :=Eq{f = rn p}{x'} x = ~Refl (𝓓 A ⊙ Γ'') 𝓪

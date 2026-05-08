module GST.Presheaf where

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

----------------------------------------------------------------------
-- Category ℝ of renamings
----------------------------------------------------------------------
-- Objects are contexts

-- Set of morphisms
infix 6 ℝ[_⟶_]
record ℝ[_⟶_] (Γ' Γ : Cx) : Set where
  constructor mkℝ[⟶]
  field
    rn : Rn
    pf : Γ' ⊢ʳ rn ∶ Γ

open ℝ[_⟶_] public

-- Setoid of morphisms
infix 6 _→ᵣ_
_→ᵣ_ : Cx → Cx → Setd
∣ Γ' →ᵣ Γ ∣ = ℝ[ Γ' ⟶ Γ ]
Γ' →ᵣ Γ ∋ p ~ p' = Rn[ Γ ] ∋ (rn p) ~ (rn p')
~Refl (_ →ᵣ Γ) p = ~Refl Rn[ Γ ] (rn p)
~Symm  (_ →ᵣ Γ) = ~Symm Rn[ Γ ]
~Trans (_ →ᵣ Γ) = ~Trans Rn[ Γ ]

-- Identity
idr : (Γ : Cx) → ℝ[ Γ ⟶ Γ ]
rn (idr Γ) = id
pf (idr Γ) = ⊢ʳid

-- Composition
infixr 5 _∘ᵣ_
_∘ᵣ_ :
  {Γ Γ' Γ'' : Cx}
  (_ : ℝ[ Γ' ⟶ Γ ])
  (_ : ℝ[ Γ'' ⟶ Γ' ])
  → -----------------
  ℝ[ Γ'' ⟶ Γ ]

rn (p ∘ᵣ q) = rn q ∘ rn p
pf (p ∘ᵣ q) = ⊢ʳ∘ (pf q) (pf p)

-- Projection
proj :
  {Γ : Cx}
  {x : 𝔸}
  (A : Ty)
  ⦃ _ : x # Γ ⦄
  → ------------------
  ℝ[ Γ ⨟ x ∶ A ⟶ Γ ]

rn (proj _)    = id
pf (proj _) = wkRn ⊢ʳid

-- Weakening
wkrn :
  {Γ Γ' : Cx}
  {x : 𝔸}
  ⦃ _ : x # Γ' ⦄
  (_ : ℝ[ Γ' ⟶ Γ ])
  (A : Ty)
  → -------------------
  ℝ[ Γ' ⨟ x ∶ A ⟶ Γ ]

wkrn p _ = mkℝ[⟶] (rn p) (wkRn (pf p))

-- Extension
infix 6 _⋉[_]_
_⋉[_]_ :
  {Γ Γ' : Cx}
  (_ : ℝ[ Γ' ⟶ Γ ])
  ((x , x') : 𝔸 × 𝔸)
  (A : Ty)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  → --------------------------
  ℝ[ Γ' ⨟ x' ∶ A ⟶ Γ ⨟ x ∶ A ]

p ⋉[ x , x' ] _  = mkℝ[⟶] (rn p ∘/ x := x') (liftRn (pf p))

----------------------------------------------------------------------
-- Presheaves on ℝ
----------------------------------------------------------------------
record ℝ^  : Set₁ where
  constructor mkℝ^
  infix 9  _⊙_ _⊙′_
  field
    _⊙_ : Cx → Setd
    ⊙cong : ∀{Γ Γ'} → Setd[ (Γ' →ᵣ Γ) ⟶ (_⊙_ Γ ⇨ _⊙_ Γ') ]
    ⊙unit :
      (Γ : Cx)
      → --------------------
      _⊙_ Γ ⇨ _⊙_ Γ ∋
        ⊙cong ₀ (idr Γ) ~ id
    ⊙assoc :
       {Γ Γ' Γ'' : Cx}
       (p : ∣ Γ' →ᵣ Γ ∣)
       (q : ∣ Γ'' →ᵣ Γ' ∣)
       → --------------------------------------------
       _⊙_ Γ ⇨ _⊙_ Γ'' ∋
         ⊙cong ₀ (p ∘ᵣ q) ~ (⊙cong ₀ q) ∘ (⊙cong ₀ p)

  _⊙′_ :
    {Γ Γ' : Cx}
    (p : ∣ Γ' →ᵣ Γ ∣)
    → --------------------
    Setd[ _⊙_ Γ ⟶ _⊙_ Γ' ]
  _⊙′_ p = ⊙cong ₀ p

open ℝ^  public

----------------------------------------------------------------------
-- Natural transformations
----------------------------------------------------------------------
infix 6 ℝ^[_⟶_]
record ℝ^[_⟶_] (A B : ℝ^) : Set where
  constructor mkℝ^[⟶]
  field
    hom : ∀{Γ} → Setd[ A ⊙ Γ ⟶ B ⊙ Γ ]
    ntl :
      {Γ Γ' : Cx}
      (p : ∣ Γ' →ᵣ Γ ∣)
      → --------------------------------
      A ⊙ Γ ⇨ B ⊙ Γ' ∋
        hom ∘ (A ⊙′ p) ~ (B ⊙′ p) ∘ hom

open ℝ^[_⟶_] public

-- Identity natural transformation
id^ : (A : ℝ^) → ℝ^[ A ⟶ A ]
hom (id^ A) = id
ntl (id^ A) p x = ~Refl (A ⊙ _) ((hom (id^ A) ∘ A ⊙′ p) ₀ x)

instance
  Identity^ℝ :
    {A : ℝ^ }
    → ------------------
    Identity ℝ^[ A ⟶ A ]
  id ⦃ Identity^ℝ {A} ⦄ = id^ A

-- Composition of natural transformations
comp^ :
  (A B C : ℝ^ )
  (_ : ℝ^[ B ⟶ C ])
  (_ : ℝ^[ A ⟶ B ])
  → ----------------
  ℝ^[ A ⟶ C ]

hom (comp^ _ _ _ g f) = hom g ∘ hom f
ntl (comp^ _ _ C g f) {Γ' = Γ'} p x = ~Trans (C ⊙ Γ')
  (hom g ₁ ntl f p x )
  (ntl g p (hom f ₀ x))

instance
  Composition^ℝ :
    {A B C : ℝ^}
    → ---------------------------------------------
    Composition ℝ^[ B ⟶ C ] ℝ^[ A ⟶ B ] ℝ^[ A ⟶ C ]
  _∘_ ⦃ Composition^ℝ ⦄ g f = comp^ _ _ _ g f

-- Setoid of natural transformations
infix 5 _⟶^_
_⟶^_ : ℝ^ → ℝ^ → Setd

∣ A ⟶^ B ∣ = ℝ^[ A ⟶ B ]
A ⟶^ B ∋ φ ~ ψ = ∀{Γ} x → B ⊙ Γ ∋ hom φ ₀ x ~ hom ψ ₀ x
~Refl (A ⟶^ B) φ x = ~Refl (B ⊙ _) (hom φ ₀ x)
~Symm (A ⟶^ B) e x = ~Symm (B ⊙ _) (e x)
~Trans (A ⟶^ B) e e' x = ~Trans (B ⊙ _) (e x) (e' x)

----------------------------------------------------------------------
-- Terminal presheaf
----------------------------------------------------------------------
1^ : ℝ^

1^ ⊙ _ = １
⊙cong 1^ ₀ _ = id
(⊙cong 1^ ₁ _) _ = tt
⊙unit 1^ _ _ = tt
⊙assoc 1^ _ _ _ = tt

!^ : ∀{A} → ℝ^[ A ⟶ 1^ ]

hom !^ ₀ _ = tt
hom !^ ₁ _ = tt
ntl !^ p _ = tt

----------------------------------------------------------------------
-- Presheaf product
----------------------------------------------------------------------
infixl 6 _×^_
_×^_ : ℝ^ → ℝ^ → ℝ^

(A ×^ B) ⊙ Γ  = (A ⊙ Γ) ⊗ (B ⊙ Γ)
(⊙cong (A ×^ B) ₀ p) ₀ (a , b) =
  ((⊙cong A ₀ p) ₀ a , (⊙cong B ₀ p) ₀ b)
(⊙cong (A ×^ B) ₀ p) ₁ (e , e') =
  ((⊙cong A ₀ p) ₁ e , (⊙cong B ₀ p) ₁ e')
(⊙cong (A ×^ B) ₁ e) (a , b) =
  ((⊙cong A ₁ e) a , (⊙cong B ₁ e) b)
⊙unit (A ×^ B) Γ (a , b) =
  (⊙unit A Γ a , ⊙unit B Γ b)
⊙assoc (A ×^ B) p q (a , b) =
  (⊙assoc A p q a , ⊙assoc B p q b)

fst^ : {A B : ℝ^} → ℝ^[ A ×^ B ⟶ A ]

hom fst^ = fst
ntl (fst^{A}) {Γ' = Γ'} p (a , _) = ~Refl (A ⊙ Γ') (A ⊙′ p ₀ a)

snd^ : {A B : ℝ^} → ℝ^[ A ×^ B ⟶ B ]

hom snd^ = snd
ntl (snd^{B = B}) {Γ' = Γ'} p (_ , b) = ~Refl (B ⊙ Γ') (B ⊙′ p ₀ b)

pair^ :
  {A B C : ℝ^}
  (_ : ℝ^[ C ⟶ A ])
  (_ : ℝ^[ C ⟶ B ])
  → ---------------
  ℝ^[ C ⟶ A ×^ B ]

hom (pair^ φ ψ) = pair (hom φ) (hom ψ)
ntl (pair^ φ ψ) p c = (ntl φ p c , ntl ψ p c)

infixl 6 _×^′_

_×^′_ :
  {A A' B B' : ℝ^}
  (_ : ℝ^[ A ⟶ A' ])
  (_ : ℝ^[ B ⟶ B' ])
  → ---------------------
  ℝ^[ A ×^ B ⟶ A' ×^ B' ]

φ ×^′ ψ = pair^ (φ ∘ fst^) (ψ ∘ snd^)

----------------------------------------------------------------------
-- Representable presheaf
----------------------------------------------------------------------
よ : Cx → ℝ^

よ Γ ⊙ Γ' = Γ' →ᵣ Γ
(⊙cong (よ _) ₀ p) ₀ q = q ∘ᵣ p
((⊙cong (よ _) ₀ p) ₁ e) x r rewrite e x r = refl
(⊙cong (よ _) ₁ e) p x r = e (rn p x) (rnDom (pf p) r)
⊙unit (よ _) _ _ _ _ = refl
⊙assoc (よ _) _ _ _ _ _ = refl

よ′ : {Γ Γ' : Cx} → ℝ[ Γ' ⟶ Γ ] → ℝ^[ よ Γ' ⟶ よ Γ ]

hom (よ′ p) ₀ q = p ∘ᵣ q
(hom (よ′ p) ₁ e) x r = e (rn p x) (rnDom (pf p) r)
ntl (よ′ _) _ _ _ _ = refl

----------------------------------------------------------------------
-- Presheaf exponential
----------------------------------------------------------------------
infixr 5 _→^_
_→^_ : ℝ^ → ℝ^ → ℝ^

(A →^ B) ⊙ Γ = よ Γ ×^ A ⟶^ B
(⊙cong (_ →^ _) ₀ p) ₀ φ = φ ∘ (よ′ p ×^′ id)
((⊙cong (A →^ _) ₀ p) ₁ e) {Γ} (q , a) =
  e (hom (よ′ p ×^′ id^ A) ₀ (q , a))
(⊙cong (A →^ _) ₁ e) φ (q , a) =
  hom φ ₁ ((λ x r → cong (rn q) (e x r)) , ~Refl (A ⊙ _) a)
⊙unit (A →^ _) _ φ {Γ'} (_ , a) =
  hom φ ₁ ((λ _ _ → refl) , ~Refl (A ⊙ Γ') a)
⊙assoc (A →^ _) _ _ φ {Γ'} (_ , a) =
  hom φ ₁ ((λ _ _ → refl) , ~Refl (A ⊙ Γ') a)

ev^ : {A B : ℝ^} → ℝ^[ (A →^ B) ×^ A ⟶ B ]

hom ev^ ₀ (φ , a) = hom φ ₀ (idr _ , a)
_₁_ (hom (ev^{B = B}) {Γ}) {_ , a} {φ' , _} (e , e') =
  ~Trans (B ⊙ Γ) (e (idr Γ , a)) (hom φ' ₁ ((λ _ _ → refl) , e'))
ntl (ev^{A}{B}) {Γ' = Γ'} p (φ , a) = ~Trans (B ⊙ Γ')
  (hom φ ₁ ((λ _ _ → refl) , (~Refl (A ⊙ Γ') (A ⊙′ p ₀ a))))
  (ntl φ p (idr _ , a))

cur^ :
  {A B C : ℝ^}
  (_ : ℝ^[ C ×^ A ⟶ B ])
  → --------------------
  ℝ^[ C ⟶ (A →^ B) ]

hom (hom (cur^{C = C} φ) ₀ c) ₀ (p , a) =
  hom φ ₀ (C ⊙′ p ₀ c , a)
hom (hom (cur^{C = C} φ) ₀ c) ₁ (e , e') =
  hom φ ₁ ((⊙cong C ₁ e) c , e')
ntl (hom (cur^{A}{B}{C} φ) ₀ c) {Γ' = Γ'} p (q , a) = ~Trans (B ⊙ Γ')
  (hom φ ₁ (⊙assoc C q p c , ((⊙cong A ₁ (λ _ _ → refl)) a)))
  (ntl φ p (C ⊙′ q ₀ c , a))
(hom (cur^{A}{C = C} φ) ₁ e) (p , a) =
  hom φ ₁ ((⊙cong C ₀ p) ₁ e , ~Refl (A ⊙ _) a)
ntl (cur^{A}{B}{C} φ) p c {Γ} (q , a) =
  hom φ ₁ ((~Symm (C ⊙ Γ) (⊙assoc C p q c)) , ~Refl (A ⊙ Γ) a)

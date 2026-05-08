module MLTTomega.Setoid where

open import Empty
open import Identity
open import Level
open import Nat
open import Notation
open import Product
open import Unit

----------------------------------------------------------------------
-- Setoids
----------------------------------------------------------------------
record Setd : Set₁ where
  constructor mkSetd
  infix 4 _∋_~_
  infix 8 ∣_∣
  field
    -- an underlying set
    ∣_∣   : Set
    -- a propositionally-relevant equivalence relation
    _∋_~_ : ∣_∣ → ∣_∣ → Set
    ~Refl :
      (x : ∣_∣)
      → --------
      _∋_~_ x x
    ~Symm :
      {x y : ∣_∣}
      (_ : _∋_~_ x y)
      → -------------
      _∋_~_ y x
    ~Trans :
      {x y z : ∣_∣}
      (_ : _∋_~_ x y)
      (_ : _∋_~_ y z)
      → -------------
      _∋_~_ x z

  -- a convenient alternative form of the reflexivity axiom
  ~Refl' :
    {x x' : ∣_∣}
    (_ : x ≡ x')
    → ----------
    _∋_~_ x x'
  ~Refl' refl = ~Refl _

open Setd public

----------------------------------------------------------------------
-- Morphism of setoids
----------------------------------------------------------------------
infix 5 Setd[_⟶_]
record Setd[_⟶_] (A B : Setd) : Set
  where
  constructor mkSetd[⟶]
  infixr 8  _₀_ _₁_
  field
    -- underlying function
    _₀_ : ∣ A ∣ → ∣ B ∣
    -- the function is equality preserving
    _₁_ :
      {x x' : ∣ A ∣}
      (_ : A ∋ x ~ x')
      → ----------------
      B ∋ _₀_ x ~ _₀_ x'

open Setd[_⟶_] public

-- Identity morphism
instance
  SetdIdentity : ∀{A} → Identity Setd[ A ⟶ A ]
  id ⦃ SetdIdentity ⦄ ₀ x = x
  id ⦃ SetdIdentity ⦄ ₁ e = e

-- Composition of morphisms
instance
  SetdComp : ∀{A B C} →
    Composition Setd[ B ⟶ C ] Setd[ A ⟶ B ] Setd[ A ⟶ C ]
  _∘_ ⦃ SetdComp ⦄ g f ₀ x = g ₀ f ₀ x
  _∘_ ⦃ SetdComp ⦄ g f ₁ e = g ₁ f ₁ e

-- The setoid of setoid morphisms
infixr 5 _⊸_
_⊸_ : Setd → Setd → Setd

∣ Δ ⊸ Γ ∣ = Setd[ Δ ⟶ Γ ]
Δ ⊸ Γ ∋ γ ~ γ'  = ∀ x → Γ ∋ γ ₀ x ~ γ' ₀ x
~Refl (Δ ⊸ Γ) γ x = ~Refl Γ (γ ₀ x)
~Symm (Δ ⊸ Γ) e x = ~Symm Γ (e x)
~Trans (Δ ⊸ Γ) e e' x = ~Trans Γ (e x) (e' x)

----------------------------------------------------------------------
-- Product of setoids
----------------------------------------------------------------------
infixl 5 _⊗_
_⊗_ : Setd → Setd → Setd

∣ A ⊗ B ∣ = ∣ A ∣ × ∣ B ∣
A ⊗ B ∋ (x , y) ~ (x' , y')  = (A ∋ x ~ x') × (B ∋ y ~ y')
~Refl (A ⊗ B) (x , y) = (~Refl A x , ~Refl B y)
~Symm (A ⊗ B) (e , e') = (~Symm A e , ~Symm B e')
~Trans (A ⊗ B) (e , e') (f , f') = (~Trans A e f , ~Trans B e' f')

----------------------------------------------------------------------
-- Families of setoids over a setoid
----------------------------------------------------------------------
infix 5 Setd[_]
record Setd[_] (Γ : Setd) : Set₁ where
  constructor mkSetd[]
  infix 4 ∥_∥ _∋_≈_
  field
    -- underlying family of sets
    ∥_∥   : ∣ Γ ∣ → Set
    -- a propositionally-relevant heterogeneous equality relation
    _∋_≈_ :
      {x x' : ∣ Γ ∣}
      → ------------------
      ∥_∥ x → ∥_∥ x' → Set

    ≈Refl :
      {x : ∣ Γ ∣}
      (a : ∥_∥ x)
      → ---------
      _∋_≈_ a a
    ≈Symm :
      {x x' : ∣ Γ ∣}
      {a : ∥_∥ x}
      {a' : ∥_∥ x'}
      -- Note the presence of the next argument
      -- needed for Pi-types, at least.
      -- Cf. Hofmann's thesis, page ?
      (_ : Γ ∋ x ~ x')
      (_ : _∋_≈_ a a')
      → --------------
      _∋_≈_ a' a
    ≈Trans :
      {x x' x'' : ∣ Γ ∣}
      {a : ∥_∥ x}
      {a' : ∥_∥ x'}
      {a'' : ∥_∥ x''}
      -- Note the presence of the next two arguments
      -- needed for Pi-types, at least.
      -- Cf. Hofmann's thesis, page ?
      (_ : Γ ∋ x ~ x')
      (_ : Γ ∋ x' ~ x'')
      (_ : _∋_≈_ a a')
      (_ : _∋_≈_ a' a'')
      → ----------------
      _∋_≈_ a a''
    -- coercion function
    coe :
      {x y : ∣ Γ ∣}
      (e : Γ ∋ x ~ y)
      → -------------
      ∥_∥ x → ∥_∥ y
    -- coherence property
    coh :
      {x y : ∣ Γ ∣}
      {a : ∥_∥ x}
      (e : Γ ∋ x ~ y)
      → ---------------
      _∋_≈_ a (coe e a)

open Setd[_] public

-- Re-indexing families
rx₀ :
  {Δ Γ : Setd}
  (_ : Setd[ Δ ⟶ Γ ])
  → -------------------
  Setd[ Γ ] → Setd[ Δ ]

∥ rx₀ γ A ∥ y = ∥ A ∥ (γ ₀ y)

rx₀{Δ} _ A ∋ a ≈ a' = A ∋ a ≈ a'

≈Refl (rx₀ _ A) = ≈Refl A

≈Symm (rx₀ γ A) e = ≈Symm A (γ ₁ e)

≈Trans (rx₀ γ A) e e' = ≈Trans A (γ ₁ e) (γ ₁ e')

coe (rx₀ γ A) e = coe A (γ ₁ e)

coh (rx₀ γ A) e = coh A (γ ₁ e)

-- Notation
infixl 6 _∙₀_
_∙₀_ :
  {Δ Γ : Setd}
  (_ : Setd[ Γ ] )
  (_ : Setd[ Δ ⟶ Γ ])
  → -------------------
  Setd[ Δ ]

A ∙₀ γ = rx₀ γ A

----------------------------------------------------------------------
-- Elements of a family of setoids
----------------------------------------------------------------------
infix 5 Setd[_⊢_]
record Setd[_⊢_] (Γ : Setd)(A : Setd[ Γ ]) : Set where
  constructor mkSetd[⊢]
  field
    -- underlying dependent function
    _₀_ : (x : ∣ Γ ∣) → ∥ A ∥ x
    -- the function is equality preserving
    _₁_ :
      {x y : ∣ Γ ∣}
      (_ : Γ ∋ x ~ y)
      → ---------------
      A ∋ _₀_ x ≈ _₀_ y

open Setd[_⊢_] public

-- Setoid of elements of a family
infix 5 _⊩_
_⊩_ : (Γ : Setd) → Setd[ Γ ] → Setd

∣ Γ ⊩ A ∣ = Setd[ Γ ⊢ A ]
Γ ⊩ A ∋ a ~ a' = ∀{x x'} → Γ ∋ x ~ x' → A ∋ a ₀ x ≈ a' ₀ x'
~Refl (Γ ⊩ A) a x = a ₁ x
~Symm (Γ ⊩ A) f e = ≈Symm A (~Symm Γ e) (f (~Symm Γ e))
~Trans (Γ ⊩ A) f f' {x} e =
  ≈Trans A (~Refl Γ x) e (f (~Refl Γ x)) (f' e)

-- Re-indexing
rx₁ :
  {Δ Γ : Setd}
  {A : Setd[ Γ ]}
  (γ : Setd[ Δ ⟶ Γ ])
  → ----------------------------
  Setd[ (Γ ⊩ A) ⟶ (Δ ⊩ A ∙₀ γ) ]

(rx₁ γ ₀ a) ₀ x  = a ₀ (γ ₀ x)
(rx₁ γ ₀ a) ₁ e  = a ₁ (γ ₁ e)
(rx₁ γ ₁ f) e    = f (γ ₁ e)

-- Notation
infixl 5 _∙₁_
_∙₁_ :
  {Δ Γ : Setd}
  {A : Setd[ Γ ]}
  (_ : Setd[ Γ ⊢ A ])
  (γ : Setd[ Δ ⟶ Γ ])
  → -----------------
  Setd[ Δ ⊢ A ∙₀ γ ]

a ∙₁ γ = rx₁ γ ₀ a

----------------------------------------------------------------------
-- Comprehension structure
----------------------------------------------------------------------
infixl 6 _⋉_
_⋉_ :
  (Γ : Setd)
  (_ : Setd[ Γ ])
  → -------------
  Setd

∣ Γ ⋉ A ∣ = ∑ ∣ Γ ∣ ∥ A ∥
Γ ⋉ A ∋ (x , a) ~ (y , b) = (Γ ∋ x ~ y) × (A ∋ a ≈ b)
~Refl (Γ ⋉ A) (x , a) = (~Refl Γ x , ≈Refl A a)
~Symm (Γ ⋉ A) (e₁ , e₂) = (~Symm Γ e₁ , ≈Symm A e₁ e₂)
~Trans (Γ ⋉ A) (e₁ , e₂) (e₁' , e₂') =
  (~Trans Γ e₁ e₁' , ≈Trans A e₁ e₁' e₂ e₂')

infixl 6 _⋉′_
_⋉′_ :
  {Γ Γ' : Setd}
  (γ : Setd[ Γ' ⟶ Γ ])
  (A : Setd[ Γ ])
  → ---------------------------
  Setd[ Γ' ⋉ (A ∙₀ γ) ⟶ Γ ⋉ A ]

(γ ⋉′ A) ₀ (x , a) = (γ ₀ x , a)
(γ ⋉′ A) ₁ (e , r) = (γ ₁ e , r)

𝓅 :
  {Γ : Setd}
  (A : Setd[ Γ ])
  → ---------------
  Setd[ Γ ⋉ A ⟶ Γ ]

𝓅 _ ₀ (x , _) = x
𝓅 _ ₁ (e , _) = e

𝓆 :
  {Γ : Setd}
  (A : Setd[ Γ ])
  → ----------------------
  Setd[ Γ ⋉ A ⊢ A ∙₀ 𝓅 A ]

𝓆 _ ₀ (_ , a) = a
𝓆 _ ₁ (_ , e) = e

𝓅𝒶𝒾𝓇  :
  {Δ Γ : Setd}
  (A : Setd[ Γ ])
  (γ : Setd[ Δ ⟶ Γ ])
  (_ : Setd[ Δ ⊢ A ∙₀ γ ])
  → ----------------------
  Setd[ Δ ⟶ Γ ⋉ A ]

𝓅𝒶𝒾𝓇 A γ a ₀ y = (γ ₀ y , a ₀ y)
𝓅𝒶𝒾𝓇 A γ a ₁ e = (γ ₁ e , a ₁ e)

𝓅-𝓅𝒶𝒾𝓇 :
  {Γ Δ : Setd}
  (A : Setd[ Γ ])
  (γ : Setd[ Δ ⟶ Γ ])
  (a : Setd[ Δ ⊢ A ∙₀ γ ])
  → ---------------------------
  Δ ⊸ Γ ∋ 𝓅 A ∘ 𝓅𝒶𝒾𝓇 A γ a ~ γ

𝓅-𝓅𝒶𝒾𝓇{Γ} _ γ _ x = ~Refl Γ (γ ₀ x)

𝓆-𝓅𝒶𝒾𝓇 :
  {Γ Δ : Setd}
  (A : Setd[ Γ ])
  (γ : Setd[ Δ ⟶ Γ ])
  (a : Setd[ Δ ⊢ A ∙₀ γ ])
  → -----------------------------------
  Δ ⊩ A ∙₀ γ ∋ 𝓆 A ∙₁ (𝓅𝒶𝒾𝓇  A γ a) ~ a
  -- N.B. this only type checks because
  -- A ∙₀ (𝓅 A ∘ 𝓅𝒶𝒾𝓇 A γ a)
  -- is definitionally equal to
  -- A ∙₀ γ

𝓆-𝓅𝒶𝒾𝓇 _ _ a e = a ₁ e

𝓅𝒶𝒾𝓇-𝓅𝓺 :
  {Γ Γ' : Setd}
  (A : Setd[ Γ ])
  (γ : Setd[ Γ' ⟶ Γ ⋉ A ])
  → --------------------------------------------
  (Γ' ⊸ Γ ⋉ A) ∋ γ ~ 𝓅𝒶𝒾𝓇 A (𝓅 A ∘ γ) (𝓆 A ∙₁ γ)

𝓅𝒶𝒾𝓇-𝓅𝓺 {Γ} A γ x =
  (~Refl Γ (π₁ (γ ₀ x)) , ≈Refl A (π₂ (γ ₀ x)))

infixl 8 [id,_]
[id,_] :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  (a : Setd[ Γ ⊢ A ])
  → -----------------
  Setd[ Γ ⟶ Γ ⋉ A ]

[id, a ] = 𝓅𝒶𝒾𝓇 _ id a

[id]₂ :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  (B : Setd[ Γ ⋉ A ])
  (a : Setd[ Γ ⊢ A ])
  (b : Setd[ Γ ⊢ B ∙₀ [id, a ] ])
  → -------------------------
  Setd[ Γ ⟶ Γ ⋉ A ⋉ B ]

[id]₂ B a b = 𝓅𝒶𝒾𝓇 B (𝓅𝒶𝒾𝓇 _ id a) b

----------------------------------------------------------------------
-- The zeroth universe of setoids
----------------------------------------------------------------------
data ∣𝒰₀∣ : Set
∥ℰ₀∥ : ∣𝒰₀∣ → Set
𝒰₀eq : ∣𝒰₀∣ → ∣𝒰₀∣ → Set
ℰ₀eq : ∀ A B → ∥ℰ₀∥ A → ∥ℰ₀∥ B → Set

data ∣𝒰₀∣ where
  Id :
    (A : ∣𝒰₀∣)
    (a a' : ∥ℰ₀∥ A)
    → -------------
   ∣𝒰₀∣
  Pi :
    (A : ∣𝒰₀∣)
    (B : ∥ℰ₀∥ A → ∣𝒰₀∣)
    (_ : (a a' : ∥ℰ₀∥ A) → ℰ₀eq A A a a' → 𝒰₀eq (B a) (B a'))
    → -------------------------------------------------------
    ∣𝒰₀∣
  Nat : ∣𝒰₀∣

∥ℰ₀∥ (Id A a a') = ℰ₀eq A A a a'
∥ℰ₀∥ (Pi A B _) =
  ∑[ f ∈ ((a : ∥ℰ₀∥ A) → ∥ℰ₀∥ (B a)) ]
  (∀ a a' → ℰ₀eq A A a a' → ℰ₀eq (B a) (B a') (f a) (f a'))
∥ℰ₀∥ Nat = ℕ

𝒰₀eq (Id A a a') (Id B b b') =
  𝒰₀eq A B × ℰ₀eq A B a b × ℰ₀eq A B a' b'
𝒰₀eq (Id _ _ _) (Pi _ _ _) = Ø
𝒰₀eq (Id _ _ _) Nat = Ø
𝒰₀eq (Pi _ _ _) (Id _ _ _) = Ø
𝒰₀eq (Pi A B _) (Pi A' B' _) =
  𝒰₀eq A A' × (∀ a a' → ℰ₀eq A A' a a' → 𝒰₀eq (B a)(B' a'))
𝒰₀eq (Pi _ _ _) Nat = Ø
𝒰₀eq Nat (Id _ _ _) = Ø
𝒰₀eq Nat (Pi _ _ _) = Ø
𝒰₀eq Nat Nat = 𝟙

ℰ₀eq (Id _ _ _) (Id _ _ _) _ _ = 𝟙
ℰ₀eq (Id _ _ _) (Pi _ _ _) _ _ = Ø
ℰ₀eq (Id _ _ _) Nat _ _ = Ø
ℰ₀eq (Pi _ _ _) (Id _ _ _) _ _ = Ø
ℰ₀eq (Pi A B _) (Pi A' B' _) (f , _) (f' , _) =
  ∀ a a' → ℰ₀eq A A' a a' → ℰ₀eq (B a) (B' a') (f a) (f' a')
ℰ₀eq (Pi _ _ _) Nat _ _ = Ø
ℰ₀eq Nat (Id _ _ _) _ _ = Ø
ℰ₀eq Nat (Pi _ _ _) _ _ = Ø
ℰ₀eq Nat Nat a b = a ≡ b

Refl𝒰₀ :
  (A : ∣𝒰₀∣)
  → --------
  𝒰₀eq A A

Reflℰ₀ :
  {A : ∣𝒰₀∣}
  (a : ∥ℰ₀∥ A)
  → ----------
  ℰ₀eq A A a a

Refl𝒰₀ (Id A a a') = (Refl𝒰₀ A , Reflℰ₀ a , Reflℰ₀ a')

Refl𝒰₀ (Pi A _ e) = (Refl𝒰₀ A , e)

Refl𝒰₀ Nat = tt

Reflℰ₀ {Id _ _ _} _ = tt

Reflℰ₀ {Pi _ _ _} (_ , e) = e

Reflℰ₀ {Nat} _ = refl

Symm𝒰₀ :
  {A A' :  ∣𝒰₀∣}
  (_ : 𝒰₀eq A A')
  → -------------
  𝒰₀eq A' A

Symmℰ₀ :
  {A A' : ∣𝒰₀∣}
  {a : ∥ℰ₀∥ A}
  {a' : ∥ℰ₀∥ A'}
  (_ : 𝒰₀eq A A')
  (_ : ℰ₀eq A A' a a')
  → ------------------
  ℰ₀eq A' A a' a

Symm𝒰₀ {Id A a b} {Id A' a' b'} (q , q' , q'') =
  Symm𝒰₀ q
  ,
  Symmℰ₀ q q'
  ,
  Symmℰ₀ q q''

Symm𝒰₀ {Pi A B _} {Pi A' B' _} (e , f) =
  Symm𝒰₀ e
  ,
  λ a a' r →
    Symm𝒰₀ (f a' a (Symmℰ₀ (Symm𝒰₀ e) r))

Symm𝒰₀ {Nat} {Nat} _ = tt

Symmℰ₀ {Id _ _ _} {Id _ _ _} _ _ = tt

Symmℰ₀ {Pi A B x} {Pi A' B' _} (f₁ , f₂) g a a' r =
  let r' = Symmℰ₀ (Symm𝒰₀ f₁) r in
  Symmℰ₀ (f₂ a' a r') (g a' a r')

Symmℰ₀ {Nat} {Nat} _ refl = refl

Trans𝒰₀ :
  {A A' A'' : ∣𝒰₀∣}
  (_ : 𝒰₀eq A A')
  (_ : 𝒰₀eq A' A'')
  → ---------------
  𝒰₀eq A A''

Transℰ₀ :
  {A A' A'' : ∣𝒰₀∣}
  {a : ∥ℰ₀∥ A}
  {a' : ∥ℰ₀∥ A'}
  {a'' : ∥ℰ₀∥ A''}
  (_ : 𝒰₀eq A A')
  (_ : 𝒰₀eq A' A'')
  (_ : ℰ₀eq A A' a a')
  (_ : ℰ₀eq A' A'' a' a'')
  → ----------------------
  ℰ₀eq A A'' a a''

coeℰ₀ :
  {A A' : ∣𝒰₀∣}
  (_ : 𝒰₀eq A A')
  (_ : ∥ℰ₀∥ A)
  → ------------
  ∥ℰ₀∥ A'

cohℰ₀ :
  {A A' : ∣𝒰₀∣}
  (e : 𝒰₀eq A A')
  (a : ∥ℰ₀∥ A)
  → ---------------------
  ℰ₀eq A A' a (coeℰ₀ e a)

Trans𝒰₀ {Id _ _ _} {Id _ _ _} {Id _ _ _} (q₀ , q₁ , q₂) (q₀' , q₁' , q₂') =
  (Trans𝒰₀ q₀ q₀' , Transℰ₀ q₀ q₀' q₁ q₁' , Transℰ₀ q₀ q₀' q₂ q₂')

Trans𝒰₀ {Pi _ _ _} {Pi _ _ _} {Pi _ _ _} (q₀ , q₁) (q₀' , q₁') =
  (Trans𝒰₀ q₀ q₀')
  ,
  (λ a a'' r → let
    a' = coeℰ₀ q₀ a
    r' = cohℰ₀ q₀ a
  in Trans𝒰₀
    (q₁ a a' r')
    (q₁' a' a''
      (Transℰ₀
        (Symm𝒰₀ q₀)
        (Trans𝒰₀ q₀ q₀')
        (Symmℰ₀ q₀ r')
        r)))

Trans𝒰₀ {Nat} {Nat} {Nat} _ _ = tt

Transℰ₀ {Id _ _ _} {Id _ _ _} {Id _ _ _} _ _ _ _ = tt

Transℰ₀ {Pi _ _ _} {Pi _ _ _} {Pi _ _ _}
  (q₀ , q₁) (q₀' , q₁') f f' a a'' r =
  let
    a'  = coeℰ₀ q₀ a
    r'  = cohℰ₀ q₀ a
    r'' = Transℰ₀ (Symm𝒰₀ q₀) (Trans𝒰₀ q₀ q₀') (Symmℰ₀ q₀ r') r
  in Transℰ₀
    (q₁ a a' r')
    (q₁' a' a'' r'')
    (f a a' r')
    (f' a' a'' r'')

Transℰ₀ {Nat} {Nat} {Nat} _ _ refl refl = refl

coeℰ₀ {Id _ a a'} {Id _ b b'} (e , r , r') s = Transℰ₀
  (Symm𝒰₀ e)
  e
  (Symmℰ₀ e r)
  (Transℰ₀ (Refl𝒰₀ _) e s r')

coeℰ₀ {Pi _ _ e} {Pi _ _ _} (e₁ , e₂) (f₁ , f₂) =
  let e₁' = Symm𝒰₀ e₁ in
  (λ a → let a₁ = coeℰ₀ e₁' a in coeℰ₀
    (e₂ a₁ a (Symmℰ₀ e₁' (cohℰ₀ e₁' a)))
    (f₁ a₁))
  ,
  (λ a a' r →
    let
       a₁    = coeℰ₀ e₁' a
       a₁'   = coeℰ₀ e₁' a'
       r₁    = Symmℰ₀ e₁' (cohℰ₀ e₁' a)
       r₁'   = Symmℰ₀ e₁' (cohℰ₀ e₁' a')
       a₁a₁' = Transℰ₀ e₁ e₁' r₁ (Transℰ₀ (Refl𝒰₀ _) e₁' r (cohℰ₀ e₁' a'))
       b     = coeℰ₀ (e₂ a₁ a r₁) (f₁ a₁)
       b'    = coeℰ₀ (e₂ a₁' a' r₁') (f₁ a₁')
    in Transℰ₀
         (Symm𝒰₀ (e₂ a₁ a r₁))
         (e₂ a₁ a' (Transℰ₀ e₁ (Refl𝒰₀ _) r₁ r))
         (Symmℰ₀ (e₂ a₁ a r₁) (cohℰ₀ (e₂ a₁ a r₁) (f₁ a₁)))
         (Transℰ₀
           (e a₁ a₁' a₁a₁')
           (e₂ a₁' a' r₁')
           (f₂ a₁ a₁' a₁a₁')
           (cohℰ₀ (e₂ a₁' a' r₁') (f₁ a₁'))))

coeℰ₀ {Nat} {Nat} _ a = a

cohℰ₀ {Id _ _ _} {Id _ _ _} _ _ = tt

cohℰ₀ {Pi _ _ e} {Pi _ _ _} (e₁ , e₂) (f₁ , f₂) a a' r =
  let
    e₁'   = Symm𝒰₀ e₁
    a''   = coeℰ₀ e₁' a'
    r''   = cohℰ₀ e₁' a'
    aa''  = Transℰ₀ e₁ e₁' r r''
    a''a' = Symmℰ₀ e₁' r''
    b     = coeℰ₀ (e₂ a'' a' a''a') (f₁ a'')
    s     = cohℰ₀ (e₂ a'' a' a''a') (f₁ a'')
  in Transℰ₀
    (e a a'' aa'')
    (e₂ a'' a' a''a')
    (f₂ a a'' aa'')
    s

cohℰ₀ {Nat} {Nat} _ _ = refl

-- The zeroth setoid universe of setoids
𝒰₀ : {Γ : Setd} → Setd[ Γ ]
ℰ₀ : {Γ : Setd} → Setd[ Γ ⋉ 𝒰₀ ]

∥ 𝒰₀ ∥ _ = ∣𝒰₀∣
𝒰₀ ∋ A ≈ B = 𝒰₀eq A B
≈Refl 𝒰₀ = Refl𝒰₀
≈Symm 𝒰₀ _ = Symm𝒰₀
≈Trans 𝒰₀ _ _ = Trans𝒰₀
coe 𝒰₀ _ A = A
coh 𝒰₀ _ = Refl𝒰₀ _

∥ ℰ₀ ∥ (_ , A) = ∥ℰ₀∥ A
_∋_≈_ ℰ₀ {_ , A} {_ , A'} a a' = ℰ₀eq A A' a a'
≈Refl ℰ₀ a = Reflℰ₀ a
≈Symm ℰ₀ (_ , e) = Symmℰ₀ e
≈Trans ℰ₀ (_ , e) (_ , e') = Transℰ₀ e e'
coe ℰ₀ (_ , e) = coeℰ₀ e
coh ℰ₀ (_ , e) = cohℰ₀ e _











----------------------------------------------------------------------
-- Setoid identity type
----------------------------------------------------------------------
ℐ𝒹 :
  {Γ : Setd}
  (A : Setd[ Γ ])
  (_ _ : Setd[ Γ ⊢ A ])
  → -------------------
  Setd[ Γ ]

∥ ℐ𝒹 A a a' ∥ x = (A ∋ a ₀ x ≈ a' ₀ x)
ℐ𝒹 A a a' ∋ _ ≈ _ = 𝟙
≈Refl (ℐ𝒹 A a a') _ = tt
≈Symm (ℐ𝒹 A a a') _ _ = tt
≈Trans (ℐ𝒹 A a a') _ _ _ _ = tt
coe (ℐ𝒹{Γ} A a a') {x} e e' =
  ≈Trans A (~Symm Γ e) e (a ₁ ~Symm Γ e)
    (≈Trans A (~Refl Γ x) e e' (a' ₁ e))
coh (ℐ𝒹 A a a') _ = tt

𝓇ℯ𝒻𝓁 :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  (a : Setd[ Γ ⊢ A ])
  → ------------------
  Setd[ Γ ⊢ ℐ𝒹 A a a ]

𝓇ℯ𝒻𝓁{Γ} a ₀ x = a ₁ ~Refl Γ x
𝓇ℯ𝒻𝓁 _ ₁ _ = tt

-- Uniqueness of identity proofs
𝓊𝒾𝓅 :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {a : Setd[ Γ ⊢ A ]}
  (r :  Setd[ Γ ⊢ ℐ𝒹 A a a ])
  → ----------------------------------
  Setd[ Γ ⊢ ℐ𝒹 (ℐ𝒹 A a a) r (𝓇ℯ𝒻𝓁 a) ]

𝓊𝒾𝓅 _ ₀ _ = tt
𝓊𝒾𝓅 _ ₁ _ = tt

-- Transport
𝓈𝓊𝒷𝓈𝓉 :
  -- This special case of the usual J rule is all that is needed
  -- in the presence of 𝓊𝒾𝓅.
  {Γ : Setd}
  (A : Setd[ Γ ])
  (B : Setd[ Γ ⋉ A ])
  {a a' : Setd[ Γ ⊢ A ]}
  (_ : Setd[ Γ ⊢ ℐ𝒹 A a a' ])
  (_ : Setd[ Γ ⊢ B ∙₀ [id, a ] ])
  → -----------------------------
  Setd[ Γ ⊢ B ∙₀ [id, a' ] ]

_₀_ (𝓈𝓊𝒷𝓈𝓉{Γ} A B e b) x = coe B (~Refl Γ x , e ₀ x) (b ₀ x)
_₁_ (𝓈𝓊𝒷𝓈𝓉{Γ} A B {a}{a'} e b) {x} {x'} e' =
  ≈Trans B
    (~Refl Γ x , ≈Symm A (~Refl Γ x) (e ₀ x))
    (e' , ≈Trans A (~Refl Γ x) e' (e ₀ x) (a' ₁ e'))
    (≈Symm B (~Refl Γ x , e ₀ x) (coh B (~Refl Γ x , e ₀ x)))
    (≈Trans B
      (e' , a ₁ e')
      (~Refl Γ x' , e ₀ x')
      (b ₁ e')
      (coh B (~Refl Γ x' , e ₀ x')))

𝓈𝓊𝒷𝓈𝓉Beta :
  {Γ : Setd}
  (A : Setd[ Γ ])
  (B : Setd[ Γ ⋉ A ])
  (a : Setd[ Γ ⊢ A ])
  (b : Setd[ Γ ⊢ B ∙₀ [id, a ] ])
  → ------------------------------------------
  Γ ⊩ B ∙₀ [id, a ] ∋ 𝓈𝓊𝒷𝓈𝓉 A B (𝓇ℯ𝒻𝓁 a) b ~ b

𝓈𝓊𝒷𝓈𝓉Beta{Γ} A B a b {x} {x'} e = ≈Trans B
  (~Refl Γ x , ≈Refl A (a ₀ x))
  (e , a ₁ e)
  (≈Symm B
    (~Refl Γ x , ≈Refl A (a ₀ x))
    (coh B (~Refl Γ x , 𝓇ℯ𝒻𝓁 a ₀ x)))
  (b ₁ e)

----------------------------------------------------------------------
-- Dependent function types
----------------------------------------------------------------------
{- Starting from

  R. O. Gandy, "On the axiom of extensionality – Part I", J. Symb. Log.
  21(1956)36-48

studies of extensionality in Type Theory, in the simply typed case,
have used partial equivalence relations at function types. In
dependent type theory, the ability to define sub-types (in a strong
sense of "sub", using Σ-types) allows one to build the
existence part of the PER for function types into the underlying
set, and hence just use equivalence relations (setoids) rather than
partial equivalence relations. I believe this fact was used for the
first time (without comment) in section 4.4. of

  T. Altenkirch. "Extensional equality in intensional type theory". In
  Proceedings 14th Symposium on Logic in Computer Science, 1999. IEEE
  Comput. Soc, Trento, Italy, 412–420.

Using this approach ∥ 𝚷 A B ∥ is a Σ-type whose second component is
treated as a proposition even though we are not forcing all proofs
of propositions to be definitionally equal. -}

𝒫𝒾 :
  {Γ : Setd}
  (A : Setd[ Γ ])
  (_ : Setd[ Γ ⋉ A ])
  → -----------------
  Setd[ Γ ]

∥ 𝒫𝒾 A B ∥ x =
  ∑[ f ∈ ((a : ∥ A ∥ x) → ∥ B ∥ (x , a)) ]
  (∀ a a' → (A ∋ a ≈ a') → B ∋ f a ≈ f a')

𝒫𝒾 A B ∋ (f , _) ≈ (f' , _) =
  ∀ a a' → A ∋ a ≈ a' → B ∋ f a ≈ f' a'

≈Refl (𝒫𝒾 A B) (_ , e) = e

≈Symm (𝒫𝒾{Γ} A B) e fg _ _ r =
  let r' = ≈Symm A (~Symm Γ e) r in
  ≈Symm B (e , r') (fg _ _ r')

≈Trans (𝒫𝒾{Γ} A B) xy yz fg gh a _ ac =
  let b  = coe A xy a
      ab = coh A {a = a} xy
      bc = ≈Trans A (~Symm Γ xy) (~Trans Γ xy yz) (≈Symm A xy ab) ac
  in ≈Trans B (xy , ab) (yz , bc) (fg _ _ ab) (gh _ _ bc)

coe (𝒫𝒾{Γ} A B) xy (f , ff) =
  let yx = ~Symm Γ xy in
  (λ a → coe B (xy , (≈Symm A yx (coh A yx))) (f (coe A yx a)))
  ,
  λ a b ab →
    let
      ea  = ≈Symm A yx (coh A {a = a} yx)
      eb  = ≈Symm A yx (coh A {a = b} yx)
      ab' = ≈Trans A xy yx ea (≈Trans A (~Refl Γ _) yx ab (≈Symm A xy eb))
    in ≈Trans B
      (yx , ≈Symm A xy ea)
      (xy , ≈Trans A (~Refl Γ _) xy ab' (≈Symm A yx (coh A yx)))
      (≈Symm B (xy , (≈Symm A yx (coh A yx))) (coh B (xy , ea)))
      (≈Trans B
        (~Refl Γ _ , ab')
        (xy , (≈Symm A yx (coh A yx)))
        (ff _ _ ab')
        (coh B (xy , eb)))

coh (𝒫𝒾{Γ} A B) {x} {a = _ , ff} xy _ _ ab =
  let
    yx  = ~Symm Γ xy
    ab' = ≈Trans A xy yx ab (coh A yx)
    e   = (xy , ≈Symm A yx (coh A yx))
  in ≈Trans B (~Refl Γ _ , ab') e (ff _ _ ab') (coh B e)

-- 𝒫𝒾∙ :
--   {Γ Δ : Setd}
--   (γ : Setd[ Δ ⟶ Γ ])
--   (A : Setd[ Γ ])
--   (B : Setd[ Γ ⋉ A ])
--   →
--   𝒫𝒾 A B ∙₀ γ ≡ 𝒫𝒾 (A ∙₀ γ) (B ∙₀ (γ ⋉′ A))

-- 𝒫𝒾∙ {Γ} {Δ} γ A B = {!!}

𝓁𝒶𝓂 :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⋉ A ⊢ B ])
  → ---------------------
  Setd[ Γ ⊢ 𝒫𝒾 A B ]

𝓁𝒶𝓂{Γ} b ₀ x =
  (λ a → b ₀ (x , a))
  ,
  λ _ _ r → b ₁ (~Refl Γ _ , r)
(𝓁𝒶𝓂 b ₁ xy) _ _ ab = b ₁ (xy , ab)

𝒶𝓅𝓅 :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⊢ 𝒫𝒾 A B ])
  (a : Setd[ Γ ⊢ A ])
  → -----------------------
  Setd[ Γ ⊢ B ∙₀ [id, a ] ]

𝒶𝓅𝓅 b a ₀ x = π₁ (b ₀ x) (a ₀ x)
𝒶𝓅𝓅 b a ₁ e = (b ₁ e) _ _ (a ₁ e)

𝒫𝒾Beta :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⋉ A ⊢ B ])
  (a : Setd[ Γ ⊢ A ])
  → ---------------------------------------------------------
  Γ ⊩ B ∙₀ [id, a ] ∋ 𝒶𝓅𝓅{A = A}{B} (𝓁𝒶𝓂 b) a ~ b ∙₁ [id, a ]

𝒫𝒾Beta b a x = b ₁ (x , a ₁ x)

-- 𝒫𝒾Eta :
--   {Γ : Setd}
--   {A : Setd[ Γ ]}
--   {B : Setd[ Γ ⋉ A ]}
--   (b : Setd[ Γ ⊢ 𝒫𝒾 A B ])
--   → ---------------------------------------------
--   Γ ⊩ 𝒫𝒾 A B ∋ b ~
--   𝓁𝒶𝓂{B = B} (𝒶𝓅𝓅{A = A ∙₀ 𝓅 A}{{!!}} (b ∙₁ 𝓅 A) (𝓆 A))

-- 𝒫𝒾Eta b x = b ₁ x

𝓁𝒶𝓂⁻¹ :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⊢ 𝒫𝒾 A B ])
  → ---------------------
  Setd[ Γ ⋉ A ⊢ B ]

𝓁𝒶𝓂⁻¹ b ₀ (x , a) = π₁ (b ₀ x) a
𝓁𝒶𝓂⁻¹ b ₁ (e , r) = (b ₁ e) _ _ r

𝓁𝒶𝓂⁻¹𝓁𝒶𝓂 :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⋉ A ⊢ B ])
  → ----------------------------------
  Γ ⋉ A ⊩ B ∋ 𝓁𝒶𝓂⁻¹{A = A} (𝓁𝒶𝓂 b) ~ b

𝓁𝒶𝓂⁻¹𝓁𝒶𝓂 b x = b ₁ x

𝓁𝒶𝓂𝓁𝒶𝓂⁻¹ :
  {Γ : Setd}
  {A : Setd[ Γ ]}
  {B : Setd[ Γ ⋉ A ]}
  (b : Setd[ Γ ⊢ 𝒫𝒾 A B ])
  → ------------------------------------------
  Γ ⊩ 𝒫𝒾 A B ∋ b ~ 𝓁𝒶𝓂{B = B} (𝓁𝒶𝓂⁻¹{A = A} b)

𝓁𝒶𝓂𝓁𝒶𝓂⁻¹ b x _ _ r = (b ₁ x) _ _ r

----------------------------------------------------------------------
-- Natural number type
----------------------------------------------------------------------
𝒩𝒶𝓉 : {Γ : Setd} → Setd[ Γ ]

∥ 𝒩𝒶𝓉 ∥ _ = ℕ
𝒩𝒶𝓉 ∋ x ≈ y = x ≡ y
≈Refl 𝒩𝒶𝓉 _ = refl
≈Symm 𝒩𝒶𝓉 _ refl = refl
≈Trans 𝒩𝒶𝓉 _ _ refl refl = refl
coe 𝒩𝒶𝓉 _ x = x
coh 𝒩𝒶𝓉 _ = refl

𝓏ℯ𝓇ℴ :
  {Γ : Setd}
  → -------------
  Setd[ Γ ⊢ 𝒩𝒶𝓉 ]

𝓏ℯ𝓇ℴ ₀ _ = 0
𝓏ℯ𝓇ℴ ₁ _ = refl

𝓈𝓊𝒸𝒸 :
  {Γ Γ' : Setd}
  {γ : Setd[ Γ' ⟶ Γ ]}
  (_ : Setd[ Γ' ⊢ 𝒩𝒶𝓉 ∙₀ γ ])
  → ------------------------
  Setd[ Γ' ⊢ 𝒩𝒶𝓉 ∙₀ γ ]

𝓈𝓊𝒸𝒸 a ₀ x = 1+ (a ₀ x)
𝓈𝓊𝒸𝒸 a ₁ e = cong 1+ (a ₁ e)

module _
  {Γ : Setd}
  (C : Setd[ Γ ⋉ 𝒩𝒶𝓉 ])
  (c₀ : Setd[ Γ ⊢ C ∙₀ [id,  𝓏ℯ𝓇ℴ ] ])
  (c₊ : Setd[ Γ ⋉ 𝒩𝒶𝓉 ⋉ C ⊢
     C ∙₀ ((𝓅𝒶𝒾𝓇 𝒩𝒶𝓉 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉))) ∘ 𝓅 C) ])
  where
  nrec : ∀ x → (n : ℕ) → ∥ C ∥ (x , n)
  nrec x 0      = c₀ ₀ x
  nrec x (1+ n) = c₊ ₀ ((x , n) , nrec x n)

  nreceq :
    {x y  : ∣ Γ ∣}
    (_ : Γ ∋ x ~ y)
    (n : ℕ)
    → ---------------------
    C ∋ nrec x n ≈ nrec y n

  nreceq e 0 = c₀ ₁ e
  nreceq e (1+ n) = c₊ ₁ ((e , refl) , nreceq e n)

  𝓃𝓇ℯ𝒸 :
    (a : Setd[ Γ ⊢ 𝒩𝒶𝓉 ])
    → -----------------------
    Setd[ Γ ⊢ C ∙₀ [id, a ] ]

  𝓃𝓇ℯ𝒸 a = mkSetd[⊢]
    (λ x → nrec x (a ₀ x))
    λ {x}{y} e →
       subst (λ n → C ∋ nrec x (a ₀ x) ≈ nrec y n)
      (a ₁ e) (nreceq e (a ₀ x))

𝒩𝒶𝓉Beta₀ :
  {Γ : Setd}
  (C : Setd[ Γ ⋉ 𝒩𝒶𝓉 ])
  (c₀ : Setd[ Γ ⊢ C ∙₀ [id, 𝓏ℯ𝓇ℴ ] ])
  (c₊ : Setd[ Γ ⋉ 𝒩𝒶𝓉 ⋉ C ⊢
    C ∙₀ ((𝓅𝒶𝒾𝓇 𝒩𝒶𝓉 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉))) ∘ 𝓅 C) ])
  → -------------------------------------------------
  Γ ⊩ C ∙₀ [id, 𝓏ℯ𝓇ℴ ] ∋ 𝓃𝓇ℯ𝒸 C c₀ c₊  𝓏ℯ𝓇ℴ ~ c₀

𝒩𝒶𝓉Beta₀ _ c₀ _ e = c₀ ₁ e

𝒩𝒶𝓉Beta₊ :
  {Γ : Setd}
  (C : Setd[ Γ ⋉ 𝒩𝒶𝓉 ])
  (c₀ : Setd[ Γ ⊢ C ∙₀ [id, 𝓏ℯ𝓇ℴ ] ])
  (c₊ : Setd[ Γ ⋉ 𝒩𝒶𝓉 ⋉ C ⊢
    C ∙₀ ((𝓅𝒶𝒾𝓇 𝒩𝒶𝓉 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉))) ∘ 𝓅 C) ])
  (a : Setd[ Γ ⊢ 𝒩𝒶𝓉 ])
  → -------------------------------------------------
  Γ ⊩ C ∙₀ [id, 𝓈𝓊𝒸𝒸 a ] ∋
    𝓃𝓇ℯ𝒸 C c₀ c₊ (𝓈𝓊𝒸𝒸 a) ~
    c₊ ∙₁ [id]₂ C a (𝓃𝓇ℯ𝒸 C c₀ c₊ a)

𝒩𝒶𝓉Beta₊{Γ} C c₀ c₊ a {x}{x'} e = c₊ ₁
  ((e , a ₁ e)
  ,
  ≈Trans C
    (e , refl)
    (~Refl Γ x' , a ₁ e)
    (nreceq C c₀ c₊ e (a ₀ x))
    (subst (λ c' → C ∋ nrec C c₀ c₊ x' c' ≈ 𝓃𝓇ℯ𝒸 C c₀ c₊ a ₀ x')
      (symm (a ₁ e))
      (≈Refl C (nrec C c₀ c₊ x' (a ₀ x')))))






-- ----------------------------------------------------------------------
-- -- Chain reasoning for setoids
-- ----------------------------------------------------------------------
-- data ~Rel (A : Setd)(x y : ∣ A ∣) : Set where
--   ~rel : (p : A ∋ x ~ y) → ~Rel A x y

-- -- Beginning of a proof
-- infix  1 ~begin_∋_
-- ~begin_∋_ :
--   (A : Setd)
--   {x y : ∣ A ∣}
--   → ---------------------
--   ~Rel A x y → A ∋ x ~ y
-- ~begin_∋_ A (~rel p) = p

-- module _ {A : Setd} where
--   -- Step with a non-trivial equality
--   infixr 2 step~
--   step~ : ∀ x {y z} → ~Rel A y z → (A ∋ x ~ y) → ~Rel A x z
--   step~ _ (~rel p) q = ~rel (~Trans A q p)
--   syntax step~ x p q = x ~⟨ q ⟩ p

--   -- Step with a flipped non-trivial equality
--   infixr 2 step~°
--   step~° : ∀ x {y z} → ~Rel A y z → (A ∋ y ~ x)  → ~Rel A x z
--   step~° _ (~rel p) q = ~rel (~Trans A (~Symm A q) p)
--   syntax step~° x p q = x ~°⟨ q ⟩ p

--   -- Step with a trivial equality
--   infixr 2 _~⟨⟩_
--   _~⟨⟩_ : ∀ x {y} → ~Rel A x y → ~Rel A x y
--   _ ~⟨⟩ p = p

--   -- Termination
--   infix  3 _~∎
--   _~∎ : ∀ x → ~Rel A x x
--   x ~∎ = ~rel (~Refl A x)

-- -- Test
-- module test
--   (A : Setd)
--   (x y z w : ∣ A ∣)
--   (p : A ∋ x ~ y)
--   (q : A ∋ y ~ z)
--   (r : A ∋ w ~ z)
--   where
--   e : A ∋ x ~ w
--   e =
--     ~begin A ∋
--       x
--     ~⟨⟩
--       x
--     ~⟨ p ⟩
--       y
--     ~⟨ q ⟩
--       z
--     ~°⟨ r ⟩
--       w
--     ~∎

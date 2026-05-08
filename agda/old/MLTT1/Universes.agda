module MLTTomega.Universes where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Level
open import Nat
open import Notation
open import Product
open import Unit

open import WSLN

open import MLTTomega.Syntax
open import MLTTomega.Judgement
open import MLTTomega.TypeSystem
open import MLTTomega.ContextConversion
open import MLTTomega.Ok
open import MLTTomega.WellScoped
open import MLTTomega.Renaming
open import MLTTomega.Substitution
open import MLTTomega.ReflexivityInversion
open import MLTTomega.AdmissibleRules
open import MLTTomega.UniqueTypes

----------------------------------------------------------------------
-- The structure for an Agda-style countable family of universes
----------------------------------------------------------------------
record AgdaUnivStruc : Set₁ where
  constructor mkAgdaUnivStruc
  field
    U : ℕ → Set

    E : (n : ℕ) → U n → Set

    univ :
      (n : ℕ)
      → ------
      U (1+ n)

    pi0 :
      (X : U 0)
      (Y : E 0 X → U 0)
      → ---------------
      U 0

    pi+ :
      {n : ℕ}
      (X : U (1+ n))
      (Y : E (1+ n) X → U (1+ n))
      → -------------------------
      U (1+ n)

    pi< :
      {n m : ℕ}
      (p : n ≥ m)
      (X : U m)
      (Y : E m X → U (1+ n))
      → --------------------
      U (1+ n)

    pi> :
      {n m : ℕ}
      (p : n ≥ m)
      (X : U (1+ n))
      (Y : E (1+ n) X → U m)
      → --------------------
      U (1+ n)

    eq :
      {n : ℕ}
      (X : U n)
      (x x' : E n X)
      → ------------
      U n

    nat : U 0

    Euniv :
      {n : ℕ}
      → ---------------------
      E (1+ n) (univ n) ≡ U n

    Epi0 :
      (X : U 0)
      (Y : E 0 X → U 0)
      → ---------------------------------------
      E 0 (pi0 X Y) ≡ ((x : E 0 X) → E 0 (Y x))

    Epi+ :
      {n : ℕ}
      (X : U (1+ n))
      (Y : E (1+ n) X → U (1+ n))
      → ------------------------------------------------------
      E (1+ n) (pi+ X Y) ≡ ((x : E (1+ n) X) → E (1+ n) (Y x))

    Epi< :
      {n m : ℕ}
      (p : n ≥ m)
      (X : U m)
      (Y : E m X → U (1+ n))
      → ---------------------------------------------------
      E (1+ n) (pi< p X Y) ≡ ((x : E m X) → E (1+ n) (Y x))

    Epi> :
      {n m : ℕ}
      (p : n ≥ m)
      (X : U (1+ n))
      (Y : E (1+ n) X → U m)
      → ---------------------------------------------------
      E (1+ n) (pi> p X Y) ≡ ((x : E (1+ n) X) → E m (Y x))

    Eeq :
      {n : ℕ}
      (X : U n)
      (x x' : E n X)
      → ------------------------
      E n (eq X x x') ≡ (x ≡ x')

    Enat :
      E 0 nat ≡ ℕ

----------------------------------------------------------------------
-- The structure for a single universe
----------------------------------------------------------------------
record UnivStruc : Set₁ where
  constructor mkUnivStruc
  field
    Ｕ : Set
    Ｅ : Ｕ → Set

open UnivStruc public

----------------------------------------------------------------------
-- Zeroth universe
----------------------------------------------------------------------
data U₀ : Set
E₀ : U₀ → Set

data U₀ where
  Pi0 :
    (X : U₀)
    (Y : E₀ X → U₀)
    → ---------------
    U₀
  Id0 :
    (X : U₀)
    (x x' : E₀ X)
    → -------------
    U₀
  Nat : U₀

E₀ (Pi0 X Y) = (x : E₀ X) → E₀ (Y x)
E₀ (Id0 X x x') = x ≡ x'
E₀ Nat = ℕ

０ : UnivStruc
Ｕ ０ = U₀
Ｅ ０ = E₀

----------------------------------------------------------------------
-- Successor universe
----------------------------------------------------------------------
data U₊
  (n : ℕ)
  (u : ∀{m} → n ≥ m → UnivStruc)
  : ----------------------------
  Set
E₊ :
  (n : ℕ)
  (u : ∀{m} → n ≥ m → UnivStruc)
  → ----------------------------
  U₊ n u → Set

data U₊ n u where
  Univ : U₊ n u
  Pi+ :
    (X : U₊ n u)
    (Y : E₊ n u X → U₊ n u)
    → ---------------------
    U₊ n u
  Pi< :
    {m : ℕ}
    (p : n ≥ m)
    (X : Ｕ(u p))
    (Y : Ｅ(u p) X → U₊ n u)
    → ----------------------
    U₊ n u
  Pi> :
    {m : ℕ}
    (p : n ≥ m)
    (X : U₊ n u)
    (Y : E₊ n u X → Ｕ(u p))
    → ---------------------
    U₊ n u
  Id+ :
    (X : U₊ n u)
    (x x' : E₊ n u X)
    → ---------------
    U₊ n u

E₊ n u Univ         = Ｕ(u ≥refl)
E₊ n u (Pi+ X Y)    = (x : E₊ n u X) → E₊ n u (Y x)
E₊ n u (Pi< p X Y)  = (x : Ｅ(u p) X) → E₊ n u (Y x)
E₊ n u (Pi> p X Y)  = (x : E₊ n u X) → Ｅ(u p) (Y x)
E₊ n u (Id+ _ x x') = x ≡ x'

Ｓ : (n : ℕ)(u : ∀{m} → n ≥ m → UnivStruc) → UnivStruc

Ｕ (Ｓ n f) = U₊ n f
Ｅ (Ｓ n f) = E₊ n f

----------------------------------------------------------------------
-- Construction of an Agda-style countable family of universes
----------------------------------------------------------------------
u≤ : ∀ n {m} → n ≥ m → UnivStruc

u≤ 0 _ = ０
u≤ (1+ n) ≥refl     = Ｓ n (u≤ n)
u≤ (1+ n) (≥step q) = u≤ n q

us : ℕ → UnivStruc

us n = u≤ n ≥refl

u≤=us :
  (n : ℕ)
  {m : ℕ}
  (p : n ≥ m)
  → -----------
  us m ≡ u≤ n p

u≤=us n  ≥refl    = refl
u≤=us n (≥step p) = u≤=us _ p

agdaUniv : AgdaUnivStruc

AgdaUnivStruc.U agdaUniv n = Ｕ (us n)
AgdaUnivStruc.E agdaUniv n = Ｅ(us n)
AgdaUnivStruc.univ agdaUniv _ = Univ
AgdaUnivStruc.pi0 agdaUniv = Pi0
AgdaUnivStruc.pi+ agdaUniv = Pi+
AgdaUnivStruc.pi< agdaUniv {n} p X Y rewrite u≤=us n p = Pi< p X Y
AgdaUnivStruc.pi> agdaUniv {n} p X Y rewrite u≤=us n p = Pi> p X Y
AgdaUnivStruc.eq agdaUniv {0} = Id0
AgdaUnivStruc.eq agdaUniv {1+ n} = Id+
AgdaUnivStruc.nat agdaUniv = Nat
AgdaUnivStruc.Euniv agdaUniv = refl
AgdaUnivStruc.Epi0 agdaUniv _ _ = refl
AgdaUnivStruc.Epi+ agdaUniv _ _ = refl
AgdaUnivStruc.Epi< agdaUniv {n} p _ _ rewrite u≤=us n p = refl
AgdaUnivStruc.Epi> agdaUniv {n} p _ _ rewrite u≤=us n p = refl
AgdaUnivStruc.Eeq agdaUniv {0} _ _ _ = refl
AgdaUnivStruc.Eeq agdaUniv {1+ n} _ _ _ = refl
AgdaUnivStruc.Enat agdaUniv = refl

-- ----------------------------------------------------------------------
-- -- Semantic universes
-- ----------------------------------------------------------------------
-- data 𝒰₀ : Set
-- ℰ₀ : 𝒰₀ → Set



-- data 𝒰₁ : Set
-- ∣𝒰₁∣ : 𝒰₁ → Set

-- data 𝒰₁ where
--   U₀ : 𝒰₁
--   Pi₀₁ :
--     (X : 𝒰₀)
--     (Y : ℰ₀ X → 𝒰₁)
--     → ---------------
--     𝒰₁
--   Pi₁₀ :
--     (X : 𝒰₁)
--     (Y : ∣𝒰₁∣ X → 𝒰₀)
--     → ---------------
--     𝒰₁
--   Pi₁₁ :
--     (X : 𝒰₁)
--     (Y : ∣𝒰₁∣ X → 𝒰₁)
--     → ---------------
--     𝒰₁
--   Id₁ :
--     (X : 𝒰₁)
--     (x x' : ∣𝒰₁∣ X)
--     → -------------
--     𝒰₁

-- ∣𝒰₁∣ U₀ = 𝒰₀
-- ∣𝒰₁∣ (Pi₀₁ X Y) = (x : ℰ₀ X) →  ∣𝒰₁∣ (Y x)
-- ∣𝒰₁∣ (Pi₁₀ X Y) = (x : ∣𝒰₁∣ X) →  ℰ₀ (Y x)
-- ∣𝒰₁∣ (Pi₁₁ X Y) = (x : ∣𝒰₁∣ X) →  ∣𝒰₁∣ (Y x)
-- ∣𝒰₁∣ (Id₁ X x x') = x ≡ x'

-- 𝒰 : Lvl → Set

-- 𝒰 𝟎 = 𝒰₀
-- 𝒰 𝟏 = 𝒰₁

-- ∣𝒰∣ : {l : Lvl} → 𝒰 l → Set

-- ∣𝒰∣ {𝟎} = ℰ₀
-- ∣𝒰∣ {𝟏} = ∣𝒰₁∣

-- Pi :
--   {l l' : Lvl}
--   (X : 𝒰 l)
--   (Y : ∣𝒰∣ X → 𝒰 l')
--   → ----------------
--   𝒰 (lmax l l')

-- Pi {𝟎} {𝟎} = Pi₀₀
-- Pi {𝟎} {𝟏} = Pi₀₁
-- Pi {𝟏} {𝟎} = Pi₁₀
-- Pi {𝟏} {𝟏} = Pi₁₁

-- Id :
--   {l : Lvl}
--   (X : 𝒰 l)
--   (x x' : ∣𝒰∣ X)
--   → ------------
--   𝒰 l

-- Id {𝟎} = Id₀
-- Id {𝟏} = Id₁

-- ----------------------------------------------------------------------
-- -- Semantic contexts, types and terms
-- ----------------------------------------------------------------------
-- ⟦Cx⟧ : Set₁
-- ⟦Cx⟧ = Set


-- ⟦Ty⟧ : (l : Lvl) → ⟦Cx⟧ → Set

-- ⟦Ty⟧ l C = C → 𝒰 l

-- ⟦Tm⟧ : {l : Lvl}(C : ⟦Cx⟧) → ⟦Ty⟧ l C → Set

-- ⟦Tm⟧ C T = (c : C) → ∣𝒰∣(T c)

-- ----------------------------------------------------------------------
-- -- Comprehension
-- ----------------------------------------------------------------------
-- infixl 6 _⋉_
-- _⋉_ : (C : ⟦Cx⟧) → {l : Lvl} → ⟦Ty⟧ l C → ⟦Cx⟧

-- C ⋉ T = ∑ C (∣𝒰∣ ∘ T)

-- 𝓅₁ :
--   {l : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   → ------------
--   C ⋉ T → C

-- 𝓅₁ = π₁

-- 𝓅₂ :
--   {l : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   → ----------------------
--   ⟦Tm⟧ (C ⋉ T) (T ○ 𝓅₁{l})

-- 𝓅₂ = π₂

-- 𝓅𝒶𝒾𝓇 :
--   {l : Lvl}
--   {C C' : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   (f : C' → C)
--   (t : ⟦Tm⟧ C' (T ○ f))
--   → ------------------
--   C' → C ⋉ T

-- 𝓅𝒶𝒾𝓇 f t = ⟨ f , t ⟩∑

-- 𝓅𝒶𝒾𝓇² :
--   {l l' : Lvl}
--   {C C' : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   {T' : ⟦Ty⟧ l' (C ⋉ T)}
--   (f : C' → C)
--   (t : ⟦Tm⟧ C' (T ○ f))
--   (t' : ⟦Tm⟧ C' (T' ○  𝓅𝒶𝒾𝓇{l} f t))
--   → --------------------------------
--   C' → C ⋉ T ⋉ T'

-- 𝓅𝒶𝒾𝓇²{l}{l'} f t t' = 𝓅𝒶𝒾𝓇{l'} (𝓅𝒶𝒾𝓇{l} f  t) t'

-- ----------------------------------------------------------------------
-- -- Universe
-- ----------------------------------------------------------------------
-- 𝒮ℯ𝓉 :
--   {C : ⟦Cx⟧}
--   → ------
--   ⟦Ty⟧ 𝟏 C

-- 𝒮ℯ𝓉 _ = U₀

-- ----------------------------------------------------------------------
-- -- Pi-types
-- ----------------------------------------------------------------------
-- 𝒫𝒾 :
--   {l l' : Lvl}
--   {C : ⟦Cx⟧}
--   (T : ⟦Ty⟧ l C)
--   (T' : ⟦Ty⟧ l' (C ⋉ T))
--   → ------------------
--   ⟦Ty⟧ (lmax l l') C

-- 𝒫𝒾 T T' c = Pi (T c) (λ t → T' (c , t))

-- 𝓁𝒶𝓂 :
--   {l l' : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   {T' : ⟦Ty⟧ l' (C ⋉ T)}
--   (t : ⟦Tm⟧ (C ⋉ T) T')
--   → --------------------
--   ⟦Tm⟧ C (𝒫𝒾 T T')

-- 𝓁𝒶𝓂 {𝟎} {𝟎} t c t' = t (c , t')
-- 𝓁𝒶𝓂 {𝟎} {𝟏} t c t' = t (c , t')
-- 𝓁𝒶𝓂 {𝟏} {𝟎} t c t' = t (c , t')
-- 𝓁𝒶𝓂 {𝟏} {𝟏} t c t' = t (c , t')

-- 𝒶𝓅𝓅 :
--   {l l' : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   {T' : ⟦Ty⟧ l' (C ⋉ T)}
--   (t' : ⟦Tm⟧ C (𝒫𝒾 T T'))
--   (t : ⟦Tm⟧ C T)
--   → ------------------------
--   ⟦Tm⟧ C (T' ○ 𝓅𝒶𝒾𝓇{l} id t)

-- 𝒶𝓅𝓅 {𝟎} {𝟎} t' t c = t' c (t c)
-- 𝒶𝓅𝓅 {𝟎} {𝟏} t' t c = t' c (t c)
-- 𝒶𝓅𝓅 {𝟏} {𝟎} t' t c = t' c (t c)
-- 𝒶𝓅𝓅 {𝟏} {𝟏} t' t c = t' c (t c)

-- ----------------------------------------------------------------------
-- -- Identity types
-- ----------------------------------------------------------------------
-- ℐ𝒹 :
--   {l : Lvl}
--   {C : ⟦Cx⟧}
--   (T : ⟦Ty⟧ l C)
--   (t t' : ⟦Tm⟧ C T)
--   → -------------
--   ⟦Ty⟧ l C

-- ℐ𝒹 T t t' c = Id (T c) (t c) (t' c)

-- 𝓇ℯ𝒻𝓁 :
--   {l : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   (t : ⟦Tm⟧ C T)
--   → ---------------
--   ⟦Tm⟧ C (ℐ𝒹 T t t)

-- 𝓇ℯ𝒻𝓁 {𝟎} _ _ = refl
-- 𝓇ℯ𝒻𝓁 {𝟏} _ _ = refl

-- 𝒥 :
--   {l l' : Lvl}
--   {C : ⟦Cx⟧}
--   {T : ⟦Ty⟧ l C}
--   {t₀ t₁ : ⟦Tm⟧ C T}
--   (T' : ⟦Ty⟧ l' (C ⋉ T ⋉ ℐ𝒹 (T ○ 𝓅₁{l} ) (t₀ ○ 𝓅₁{l}) (𝓅₂{l})))
--   (_ : ⟦Tm⟧ C (T' ○ 𝓅𝒶𝒾𝓇²{l}{l} id t₀ (𝓇ℯ𝒻𝓁{l} t₀)))
--   (t'' : ⟦Tm⟧ C (ℐ𝒹 T t₀ t₁))
--   → -----------------------------------------------------------
--   ⟦Tm⟧ C (T' ○ 𝓅𝒶𝒾𝓇² {l} {l} id t₁ t'')

-- 𝒥 {𝟎} {𝟎} T' t' t'' c =
--   ≡elim (λ y e → ℰ₀ (T' ((c , y) , e))) (t' c) (t'' c)
-- 𝒥 {𝟎} {𝟏} T' t' t'' c =
--   ≡elim (λ y e → ∣𝒰₁∣ (T' ((c , y) , e))) (t' c) (t'' c)
-- 𝒥 {𝟏} {𝟎} T' t' t'' c =
--   ≡elim (λ y e → ℰ₀ (T' ((c , y) , e))) (t' c) (t'' c)
-- 𝒥 {𝟏} {𝟏} T' t' t'' c =
--   ≡elim (λ y e → ∣𝒰₁∣ (T' ((c , y) , e))) (t' c) (t'' c)

-- ----------------------------------------------------------------------
-- -- Natural numbers
-- ----------------------------------------------------------------------
-- 𝒩𝒶𝓉 :
--   {C : ⟦Cx⟧}
--   → ------
--   ⟦Ty⟧ 𝟎 C

-- 𝒩𝒶𝓉 _ = Nat

-- 𝓏ℯ𝓇ℴ :
--   {C : ⟦Cx⟧}
--   → --------
--   ⟦Tm⟧ C 𝒩𝒶𝓉

-- 𝓏ℯ𝓇ℴ _ = 0

-- 𝓈𝓊𝒸𝒸 :
--   {C : ⟦Cx⟧}
--   (t : ⟦Tm⟧ C 𝒩𝒶𝓉)
--   → -----------------
--   ⟦Tm⟧ C 𝒩𝒶𝓉

-- 𝓈𝓊𝒸𝒸 t c =  1+ (t c)

-- 𝓃𝓇ℯ𝒸 :
--   {l : Lvl}
--   {C : ⟦Cx⟧}
--   (T : ⟦Ty⟧ l (C ⋉ 𝒩𝒶𝓉))
--   (t₀ : ⟦Tm⟧ C (T ○ 𝓅𝒶𝒾𝓇{𝟎} id 𝓏ℯ𝓇ℴ))
--   (t₊ : ⟦Tm⟧ (C ⋉ 𝒩𝒶𝓉 ⋉ T)
--     (T ○ ((𝓅𝒶𝒾𝓇 {𝟎} (𝓅₁{𝟎}) (𝓈𝓊𝒸𝒸 (𝓅₂{𝟎}))) ∘ 𝓅₁{l})))
--   (t : ⟦Tm⟧ C 𝒩𝒶𝓉)
--   → --------------------------------------------------
--   ⟦Tm⟧ C (T ○ 𝓅𝒶𝒾𝓇{𝟎} id t)

-- 𝓃𝓇ℯ𝒸{l} T t₀ t₊ t c = ℕelim
--   (λ x → ∣𝒰∣ (T (c , x)))
--   (t₀ c)
--   (λ x y → t₊ ((c , x) , y))
--   (t c)

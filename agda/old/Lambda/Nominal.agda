module Lambda.Nominal where

open import Prelude
open import WSLN

----------------------------------------------------------------------
-- Nominal lambda terms
----------------------------------------------------------------------
data Nom : Set where
  𝐯   : 𝔸 → Nom
  app : Nom → Nom → Nom
  lam : 𝔸 → Nom → Nom

----------------------------------------------------------------------
-- Freshness
----------------------------------------------------------------------
suppNom : Nom → Fset𝔸
suppNom (𝐯 x)     = ｛ x ｝
suppNom (app M N) = suppNom M ∪ suppNom N
suppNom (lam x M) = ｛ x ｝ ∪ suppNom M

instance
  FiniteSupportNom : FiniteSupport Nom
  supp ⦃ FiniteSupportNom ⦄ = suppNom

----------------------------------------------------------------------
-- Renaming
----------------------------------------------------------------------
rnNom : (𝔸 → 𝔸) → Nom → Nom

-- we rename all variables, be they free, bound or binding
rnNom ρ (𝐯 x)     = 𝐯 (ρ x)
rnNom ρ (app M N) = app (rnNom ρ M) (rnNom ρ N)
rnNom ρ (lam x M) = lam (ρ x) (rnNom ρ M)

instance
  ApplyRnNom : Apply (𝔸 → 𝔸) Nom Nom
  _*_ ⦃ ApplyRnNom ⦄ = rnNom

----------------------------------------------------------------------
-- Alpha equivalence of nominal lambda terms
----------------------------------------------------------------------
infix 4 _~_
data _~_ : Nom → Nom → Set where
  ~var :
    (x : 𝔸)
    → -------
    𝐯 x ~ 𝐯 x

  ~app :
    {M M' N N' : Nom}
    (_ : M ~ M')
    (_ : N ~ N')
    → ---------------
    app M N ~ app M' N'

  ~lam :
    {y x x' : 𝔸}
    {M M' : Nom}
    (_ : (x ↦ y) * M ~ (x' ↦ y)* M')
    (_ : y # (M , M'))
    → ------------------------------
    lam x M  ~ lam x' M'

----------------------------------------------------------------------
-- Size
----------------------------------------------------------------------
sizeNom : Nom → ℕ

sizeNom (𝐯 x) = 0
sizeNom (app M N) = 1+ (max (sizeNom M) (sizeNom N))
sizeNom (lam x M) = 1+ (sizeNom M)

instance
  hasSizeNom : hasSize Nom
  size ⦃ hasSizeNom ⦄ = sizeNom

-- Renaming preserves size
sizeRen :
  (M : Nom)
  (ρ : 𝔸 → 𝔸)
  → -------------------
  size (ρ * M) ≡ size M

sizeRen (𝐯 _) _ = refl
sizeRen (app M N) ρ
  rewrite sizeRen M ρ
  | sizeRen N ρ = refl
sizeRen (lam x M) ρ
  rewrite sizeRen M ρ = refl

sizeRen≤ :
  {h : ℕ}
  (M : Nom)
  (ρ : 𝔸 → 𝔸)
  (_ : size M ≤ h)
  → --------------
  size (ρ * M) ≤ h

sizeRen≤ M ρ q rewrite sizeRen M ρ = q

----------------------------------------------------------------------
-- Capture-avoiding substitution
----------------------------------------------------------------------
infixr 6 [_/_] [_/_]≤

[_/_] : Nom → 𝔸 → Nom → Nom

-- We proceed by induction on the size of nominal lambda terms:
[_/_]≤ :
  (M : Nom)
  (x : 𝔸)
  {h : ℕ}
  (N : Nom)
  (_ : size N ≤ h)
  → --------------
  Nom

[ M / x ]≤ (𝐯 y) _ with  x ≐ y
... | no  _ = 𝐯 y
... | yes _ = M

[ M / x ]≤ {1+ _} (app N₁ N₂) 1+≤ = app
  ([ M / x ]≤ N₁ (it ∘ ≤max₁ _ _))
  ([ M / x ]≤ N₂ (it ∘ ≤max₂ (size N₁) _))

[ M / x ]≤ {1+ _} (lam y N) 1+≤ =
  let z = new (supp (M , x , N)) in
  lam z ([ M / x ]≤ ((y ↦ z) * N) (sizeRen≤ N (id ∘ y := z) it))

[ M / x ] N = [ M / x ]≤ N ≤refl

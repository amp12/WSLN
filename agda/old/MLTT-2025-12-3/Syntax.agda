module MLTT.Syntax where

open import Identity
open import List
open import Nat
open import Notation
open import Product

open import WSLN

----------------------------------------------------------------------
-- Universe levels
----------------------------------------------------------------------
{- We consider the case where there are a countalbe infinity of nested
non-cumulative universes. -}

Lvl : Set
Lvl = ℕ

----------------------------------------------------------------------
-- Signature for types and terms
----------------------------------------------------------------------
-- Operators
data OpMLTT : Set where
  -- Universe type
  ′Set′ : Lvl → OpMLTT
  -- Dependent function type
  ′Pi′ :  OpMLTT
  -- Function abstraction
  ′lam′ :  OpMLTT
  -- Function application
  ′app′ :  OpMLTT
  -- Identity type
  ′Id′ : OpMLTT
  -- Reflexivity proof
  ′refl′ : OpMLTT
  -- Identity elimination
  ′J′ : OpMLTT
  -- Natural number type
  ′Nat′ : OpMLTT
  -- Zero
  ′zero′ : OpMLTT
  -- Successor
  ′succ′ : OpMLTT
  -- Natural number elimination
  ′natrec′ : OpMLTT

-- Arities
arMLTT : OpMLTT → List ℕ
arMLTT (′Set′ ℓ) = []
arMLTT ′Pi′ = 0 ∷ 1 ∷ []
arMLTT ′lam′ = 0 ∷ 1 ∷ []
arMLTT ′app′ = 0 ∷ 0 ∷ 1 ∷ 0 ∷ []
arMLTT ′Id′ = 0 ∷ 0 ∷ 0 ∷ []
arMLTT ′refl′ = 0 ∷ []
arMLTT ′J′ = 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
arMLTT ′Nat′ = []
arMLTT ′zero′ = []
arMLTT ′succ′ = 0 ∷ []
arMLTT ′natrec′ = 1 ∷ 0 ∷ 2 ∷ 0 ∷ []

instance
  MLTT : Sig

  Op MLTT = OpMLTT
  ar MLTT = arMLTT

----------------------------------------------------------------------
-- Terms of Martin-Löf Type Theory
----------------------------------------------------------------------
infix 6 Tm[_]
Tm[_] : ℕ → Set

Tm[ n ] = Exp[_] ⦃ MLTT ⦄ n

Tm : Set

Tm = Exp[_] ⦃ MLTT ⦄ 0

-- Types are particular kinds of term
infix 6 Ty[_]
Ty[_] : ℕ → Set

Ty[ n ] = Tm[ n ]

Ty : Set

Ty = Tm

----------------------------------------------------------------------
-- Notation
----------------------------------------------------------------------
infix 7 _∙[_,_]_
pattern 𝐒𝐞𝐭 ℓ = 𝐜 (′Set′ ℓ) []
pattern 𝐒𝐞𝐭₀ = 𝐜 (′Set′ 0) []
pattern 𝚷 A B = 𝐜 ′Pi′ (A ∷ B ∷ [])
pattern 𝛌 A f = 𝐜 ′lam′ (A ∷ f ∷ [])
pattern _∙[_,_]_ b A B a = 𝐜 ′app′ (b ∷ A ∷ B ∷ a ∷ [])
pattern 𝐈𝐝 A a a' = 𝐜 ′Id′ (A ∷ a ∷ a' ∷ [] )
pattern 𝐫𝐞𝐟𝐥 a = 𝐜 ′refl′ (a ∷ [])
pattern 𝐉 C a b c e = 𝐜 ′J′ (C ∷ a ∷ b ∷ c ∷ e ∷ [])
pattern 𝐍𝐚𝐭 = 𝐜 ′Nat′ []
pattern 𝐳𝐞𝐫𝐨 = 𝐜 ′zero′ []
pattern 𝐬𝐮𝐜𝐜 a = 𝐜 ′succ′ (a ∷ [])
pattern 𝐧𝐫𝐞𝐜 C c₀ c₊ a = 𝐜 ′natrec′ (C ∷ c₀ ∷ c₊ ∷ a ∷ [])

----------------------------------------------------------------------
-- Contexts
----------------------------------------------------------------------
infixl 5 _⸴_∶[_]_

-- A small inductive-recursive definition
-- which is convenient, but avoidable
data Cx : Set
dom : Cx → Fset𝔸

data Cx where
  ◇     : Cx
  _⸴_∶[_]_ :
    (Γ : Cx)
    (x : 𝔸)
    (ℓ : Lvl)
    (A : Ty)
    ⦃ _ : x ∉ dom Γ ⦄
    → ---------------
    Cx

dom ◇ = ∅
dom (Γ ⸴ x ∶[ _ ] _) = dom Γ ∪ ｛ x ｝

-- Freshness for contexts
instance
  FiniteSupportCx : FiniteSupport Cx
  supp ⦃ FiniteSupportCx ⦄ Γ = dom Γ

-- Inversion
cx⁻¹ :
  {Γ Γ' : Cx}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  {ℓ ℓ' : Lvl}
  {A A' : Ty}
  (_ : (Γ ⸴ x ∶[ ℓ ] A) ≡ (Γ' ⸴ x' ∶[ ℓ' ] A'))
  → -------------------------------------------
  (Γ ≡ Γ') ∧ (x ≡ x') ∧ (ℓ ≡ ℓ') ∧ (A ≡ A')

cx⁻¹ refl = (refl , refl , refl , refl)

----------------------------------------------------------------------
-- Membership of contexts
----------------------------------------------------------------------
infix 4 _isIn_
data _isIn_  (xℓA : 𝔸 × Lvl × Ty) : Cx → Set where
  isInNew :
    {Γ : Cx}
    {x' : 𝔸}
    ⦃ _ : x' # Γ ⦄
    {ℓ' : Lvl}
    {A' : Ty}
    (p : xℓA ≡ (x' , ℓ' , A'))
    → --------------------------
    xℓA isIn (Γ ⸴ x' ∶[ ℓ' ] A')
  isInOld :
    {Γ : Cx}
    {x' : 𝔸}
    ⦃ _ : x' # Γ ⦄
    {ℓ' : Lvl}
    {A' : Ty}
    (p : xℓA isIn Γ)
    → -------------------------
    xℓA isIn (Γ ⸴ x' ∶[ ℓ' ] A')

isIn→dom :
  {Γ : Cx}
  {x : 𝔸}
  {ℓ : Lvl}
  {A : Ty}
  (_ : (x , ℓ , A) isIn Γ)
  → ----------------------
  x ∈ dom Γ
isIn→dom (isInNew refl) = ∈∪₂ ∈｛｝
isIn→dom (isInOld p) = ∈∪₁ (isIn→dom p)

dom→isIn :
  {Γ : Cx}
  {x : 𝔸}
  (_ : x ∈ dom Γ)
  → ------------------------------
  ∃[ ℓ ] ∃[ A ] (x , ℓ , A) isIn Γ
dom→isIn {_ ⸴ _ ∶[ _ ] _} (∈∪₁ p)
  with (ℓ , A , p') ← dom→isIn p = (ℓ , A , isInOld p')
dom→isIn {_ ⸴ _ ∶[ ℓ ] A} (∈∪₂ ∈｛｝) = (ℓ , A , isInNew refl)

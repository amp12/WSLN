# WSLN

`adgda/WSLN` is an Agda library for the well-scoped version of the locally nameless method of representing syntax. The library is parameterised by a Plotkin-style binding signature and makes use of some  (more or less) standard library definitions in `agda/Prelude`. 
  
`agda/Adequacy` gives a proof of the adequacy of this style of representation with respect to naïve nameful syntax modulo α-conversion 
 
Examples of WSLN in use:
 
*  `agda/MLTT` Martin-Löf Type Theory with countably many Agda-style non-cumulative universes closed under Pi-types, natural number type and intensional identity types.
*  `agda/GST` Decidability of βη-conversion for Gödel's System T using well-scoped locally nameless syntax, proved via a normalization by evaluation argument, in safe Agda.
* Further examples of binding signatures: untyped λ-calculus (`agda/Lambda.agda`), π-calculus (`agda/PiCalc.agda`).

### Browsable code: [README](https://amp12.github.io/WSLN/html/README.html)

Checked with Agda version 2.8.0 using flags
  `--safe`
  `--without-K`
  
### Accompanying paper:

### Example of using the WSLN library (`agda/Lambda.agda`)

```agda
{- Well-scoped locally nameless representation of untyped λ-calculus. -}

-- Some standard definitions and notations
open import Prelude

-- Import the WSLN library
open import WSLN public

-- Declare a suitable binding signature for untyped λ-calculus.
instance
  WSLN : Sig
  WSLN = mkSig OpWSLN arWSLN
    module _ where
    -- Operators
    data OpWSLN : Set where
      -- function abstraction
      ′lm′ : OpWSLN
      -- function application
      ′ap′ :  OpWSLN

    -- Arities
    arWSLN : OpWSLN → List ℕ
    -- function abstraction take one argument, binding one name
    arWSLN ′lm′ = 1 :: []
    -- function application takes two aruments, each binding no names
    arWSLN ′ap′ = 0 :: 0 :: []

{- WSLN provides an ℕ-indexed type Trm[ n ] of n-terms over the
signature with constructors 𝐢 for scoped deBruijn indices (Fin n), 𝐚
for atomic names (𝔸) and 𝐨 for compound terms built using operators.

λ-terms modulo α-equivalence are in bijection with the locally
closed (n = 0) terms. Trm[ 0 ] is abbreviated to Trm. -}

-- Some concrete syntax for terms over the sinature
infixl 7 _∙_
-- variable named by atom x
pattern 𝐯 x = 𝐚 x
-- function abstraction
pattern 𝛌 a = 𝐨 ′lm′ (a :: [])
 -- function application
pattern _∙_ b a = 𝐨 ′ap′ (b :: a :: [])

-- Example term, corresponding to λ x . λ y . x (y  z)
module _
  (z : 𝔸)
  where
  ex : Trm
  ex =
    𝐨 ′lm′ (
      𝐨 ′lm′ (
        𝐨 ′ap′ (
          𝐢 (suc zero) ::
          𝐨 ′ap′ (
            𝐢 zero ::
            𝐯 z :: [])
          :: [])
        :: [])
      :: [])

  -- using the concrete syntax
  ex' : Trm
  ex' = 𝛌 (𝛌 (i1 ∙ (i0 ∙ 𝐯 z)))

  ex≡ex' : ex ≡ ex'
  ex≡ex' = refl

-- Example relation: one-step β-reduction
infix 4 _⟶β_
data _⟶β_ : Trm → Trm → Set where
  beta :
    (t : Trm[ 1 ])
    (u : Trm)
    → ----------------
    𝛌 t ∙ u ⟶β t [ u ]
    -- t [ u ] is the concretion of
    -- the 1-term t at the 0-term u

  lam :
    {x : 𝔸}
    {t t' : Trm[ 1 ]}
    -- Fset𝔸 is a type representing
    -- finite sets of atoms
    (S : Fset𝔸)
    -- Cofinite quantification
    (_ : ∀ x → x # S →
      t [ x ] ⟶β t' [ x ])
    → --------------------
    𝛌 t ⟶β 𝛌 t'

  app₁ :
    {u u' : Trm}
    (t : Trm)
    (_ : u ⟶β u')
    → -------------
    t ∙ u ⟶β t ∙ u'

  app₂ :
    {t t' : Trm}
    (u : Trm)
    (_ : t ⟶β t')
    → -------------
    t ∙ u ⟶β t' ∙ u
```
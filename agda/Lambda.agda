module Lambda where

{- Well-scoped locally nameless representation of untyped lambda
calculus. -}

open import Prelude
open import WSLN public

----------------------------------------------------------------------
-- Well scoped, locally nameless lambda terms
----------------------------------------------------------------------
instance
  WSLN : Sig
  WSLN = mkSig OpWSLN arWSLN
    module _ where
    -- Operators
    data OpWSLN : Set where
      -- Function abstraction
      ′lm′ : OpWSLN
      -- Function application
      ′ap′ :  OpWSLN

    -- Arities
    arWSLN : OpWSLN → List ℕ
    arWSLN ′lm′ = 1 :: []
    arWSLN ′ap′ = 0 :: 0 :: []

-- Notation
infixl 7 _∙_
pattern 𝐯 x = 𝐚 x
pattern _∙_ b a = 𝐨 ′ap′ (b :: a :: [])
pattern 𝛌 a = 𝐨 ′lm′ (a :: [])

-- Lambda terms are the locally closed expressions
Lam : Set
Lam = Trm[_] 0

----------------------------------------------------------------------
-- Example term: λ x . λ y . x (y  z)
----------------------------------------------------------------------
module _ (z : 𝔸) where
  ex : Lam
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

  ex' : Lam
  ex' = 𝛌 (𝛌 (i1 ∙ (i0 ∙ 𝐯 z)))

  ex≡ex' : ex ≡ ex'
  ex≡ex' = refl

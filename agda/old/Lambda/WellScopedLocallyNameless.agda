module Lambda.WellScopedLocallyNameless where

open import Prelude
open import WSLN

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
    arWSLN ′lm′ = 1 ∷ []
    arWSLN ′ap′ = 0 ∷ 0 ∷ []

-- Notation
infixl 7 _∙_
pattern _∙_ b a = 𝐜 ′ap′ (b ∷ a ∷ [])
pattern 𝛌 a = 𝐜 ′lm′ (a ∷ [])

-- Lambda terms are the locally closed expressions
Lam : Set
Lam = Exp[_] 0

-- Injectivity properties
∙inj :
  {a a' b b' : Lam}
  (_ : a ∙ b ≡ a' ∙ b')
  → -------------------
  (a ≡ a') ∧ (b ≡ b')

∙inj refl = (refl , refl)

𝛌inj :
  {a a' : Exp[ 1 ]}
  (_ : 𝛌 a ≡ 𝛌 a')
  → ---------------
  a ≡ a'

𝛌inj refl = refl

𝛌α :
  {x x' y : 𝔸}
  {a a' : Lam}
  (_ : 𝛌(x ． a) ≡ 𝛌(x' ． a'))
  (_ : y # (a , a'))
  → --------------------------------------
  (id ∘ x := y) * a ≡ (id  ∘ x' := y) * a'

𝛌α{x}{x'}{y}{a}{a'} e (q ∉∪ q') =
  begin
    (id  ∘ x := y) * a
  ≡˘⟨ updateRn id x y a ⟩
    (x ≔ 𝐯 y) * a
  ≡˘⟨ concAbs x a (𝐯 y) ⟩
    (x ． a)❪ y ❫
  ≡⟨ cong (λ b → b ❪ y ❫) (𝛌inj e) ⟩
    (x' ． a')❪ y ❫
  ≡⟨ concAbs x' a' (𝐯 y) ⟩
    (x' ≔ 𝐯 y) * a'
  ≡⟨ updateRn id x' y a' ⟩
    (id  ∘ x' := y) * a'
  ∎

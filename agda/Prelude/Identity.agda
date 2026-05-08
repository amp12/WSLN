module Prelude.Identity where

open import Prelude.Level

----------------------------------------------------------------------
-- Homogeneous identity types
----------------------------------------------------------------------
infix 4 _≡_
data _≡_ {l : Level}{A : Set l}(x : A) : A → Set l where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

----------------------------------------------------------------------
-- ≡ is an equivalence relation
----------------------------------------------------------------------
symm :
  {l : Level}
  {A : Set l}
  {x y : A}
  (_ : x ≡ y)
  → ---------
  y ≡ x
symm refl = refl

trans :
  {l : Level}
  {A : Set l}
  {x y z : A}
  (_ : x ≡ y)
  (_ : y ≡ z)
  → ---------
  x ≡ z
trans p refl = p

----------------------------------------------------------------------
-- Transport
----------------------------------------------------------------------
cong :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  {x x' : A}
  (_ : x ≡ x')
  → ----------
  f x ≡ f x'
cong _ refl = refl

cong₂ :
  {l m n : Level}
  {A : Set l}
  {B : Set m}
  {C : Set n}
  (f : A → B → C)
  {x x' : A}
  {y y' : B}
  (_ : x ≡ x')
  (_ : y ≡ y')
  → -------------
  f x y ≡ f x' y'
cong₂ _ refl refl = refl

cong₃ :
  {l m n o : Level}
  {A : Set l}
  {B : Set m}
  {C : Set n}
  {D : Set o}
  (f : A → B → C → D)
  {x x' : A}
  {y y' : B}
  {z z' : C}
  (_ : x ≡ x')
  (_ : y ≡ y')
  (_ : z ≡ z')
  → ------------------
  f x y z ≡ f x' y' z'
cong₃ _ refl refl refl = refl

cong₄ :
  {l m n o p : Level}
  {A : Set l}
  {B : Set m}
  {C : Set n}
  {D : Set o}
  {E : Set p}
  (f : A → B → C → D → E)
  {x x' : A}
  {y y' : B}
  {z z' : C}
  {w w' : D}
  (_ : x ≡ x')
  (_ : y ≡ y')
  (_ : z ≡ z')
  (_ : w ≡ w')
  → -----------------------
  f x y z w ≡ f x' y' z' w'
cong₄ _ refl refl refl refl = refl

----------------------------------------------------------------------
-- Congruence
----------------------------------------------------------------------
subst :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  {x x' : A}
  (_ : x ≡ x')
  → -------------
  B x → B x'
subst _ refl b = b

subst₂ :
  {l m : Level}
  {A B : Set l}
  (C : A → B → Set m)
  {x x' : A}
  {y y' : B}
  (_ : x ≡ x')
  (_ : y ≡ y')
  → -----------------
  C x y → C x' y'
subst₂ _ refl refl c = c

subst₃ :
  {l m : Level}
  {A B C : Set l}
  (D : A → B → C → Set m)
  {x x' : A}
  {y y' : B}
  {z z' : C}
  (_ : x ≡ x')
  (_ : y ≡ y')
  (_ : z ≡ z')
  → --------------------
  D x y z → D x' y' z'
subst₃ _ refl refl refl d = d

subst₄ :
  {l m : Level}
  {A B C D : Set l}
  (E : A → B → C → D → Set m)
  {x x' : A}
  {y y' : B}
  {z z' : C}
  {w w' : D}
  (_ : x ≡ x')
  (_ : y ≡ y')
  (_ : z ≡ z')
  (_ : w ≡ w')
  → -----------------------
  E x y z w → E x' y' z' w'
subst₄ _ refl refl refl refl d = d

tpt :
  {l m n : Level}
  {A : Set l}
  (B : A → Set m)
  (C : (x : A) → B x → Set n)
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (e : x ≡ x')
  (_ : subst B e y ≡ y')
  → -------------------------
  C x y → C x' y'
tpt _ _ refl refl c = c

≡elim :
  {l m : Level}
  {A : Set l}
  {x x' : A}
  (B : (y : A) → x ≡ y → Set m)
  (_ : B x refl)
  (e : x ≡ x')
  → ---------------------------
  B x' e

≡elim _ b refl = b

substInj :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  {x x' : A}
  {y y' : B x}
  (e : x ≡ x')
  (_ : subst B e y ≡ subst B e y')
  → ------------------------------
  y ≡ y'
substInj _ refl e = e

substInv :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (e : x ≡ x')
  (_ : y' ≡ subst B e y)
  → ---------------------
  subst B (symm e) y' ≡ y

substInv B refl refl = refl

-- subst-nat :
--  {l m : Level}
--  {A A' : Set l}
--  {x x' : A}
--  (B : A → Set m)
--  (B' : A' → Set m)
--  (f : A → A')
--  (g : ∀{x} → B x → B' (f x))
--  (e : x ≡ x')
--  (e' : f x ≡ f x')
--  (y : B x)
--  → --------------------------------
--  subst B' e' (g y) ≡ g (subst B e y)

-- subst-nat _ _ _ _ refl e _ = {!!}

----------------------------------------------------------------------
-- Chain reasoning
----------------------------------------------------------------------

{- Lifted from
  <agda-stdlib/src/Relation/Binary/Reasoning/Base/Single.agda> -}

module _ {l : Level}{A : Set l} where
  infix  4 _IsRelatedTo_
  data _IsRelatedTo_ (x y : A) : Set l where
    relTo : (x≡y : x ≡ y) → x IsRelatedTo y

  -- Beginning of a proof
  infix  1 begin_
  begin_ : ∀ {x y} → x IsRelatedTo y → x ≡ y
  begin relTo x≡y = x≡y

  -- Step with a non-trivial propositional equality
  infixr 2 step-≡
  step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
  step-≡ _ x≡z refl = x≡z
  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

  -- Step with a flipped non-trivial propositional equality
  infixr 2 step-≡˘
  step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
  step-≡˘ _ x≡z refl = x≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

  -- Step with a trivial propositional equality
  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x≡y = x≡y

  -- Note that the arguments to the `step`s are not provided in their
  -- "natural" order and syntax declarations are later used to re-order
  -- them. This is because the `step` ordering allows the type-checker to
  -- better infer the middle argument `y` from the `_IsRelatedTo_`
  -- argument (see issue 622).
  --
  -- This has two practical benefits. First it speeds up type-checking by
  -- approximately a factor of 5. Secondly it allows the combinators to be
  -- used with macros that use reflection

  -- Termination
  infix  3 _∎
  _∎ : ∀ x → x IsRelatedTo x
  x ∎ = relTo refl

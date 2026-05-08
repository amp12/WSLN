module Prelude.Function where

open import Prelude.Level
open import Prelude.Notation

----------------------------------------------------------------------
-- Identity function
----------------------------------------------------------------------
instance
  FuncIdentity : {l : Level}{A : Set l} → Identity (A → A)
  id ⦃ FuncIdentity ⦄ x = x

----------------------------------------------------------------------
-- Non-dependent function composition
----------------------------------------------------------------------
instance
  FuncComp :
    {l m n : Level}
    {A : Set l}
    {B : Set m}
    {C : Set n}
    → ---------------------------------
    Composition (B → C) (A → B) (A → C)
  _∘_ ⦃ FuncComp ⦄ g f x = g (f x)

----------------------------------------------------------------------
-- Dependent function composition
----------------------------------------------------------------------
infixr 5 _○_
_○_ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (x : A) → B x → Set n}
  (g : {x : A}(y : B x) → C x y)
  (f : (x : A) → B x)
  → ----------------------------
  (x : A) → C x (f x)

(g ○ f) x = g (f x)

----------------------------------------------------------------------
-- Case expressions
----------------------------------------------------------------------
infix 1 case_of_
case_of_ :
  {l m : Level}
  {A : Set l}
  (x : A)
  {B : A → Set m}
  → -------------------
  ((x : A) → B x) → B x

case x of f  = f x

infix 1 case_returning_of_
case_returning_of_ :
  {l m : Level}
  {A : Set l}
  (x : A)
  (B : A → Set m)
  → -------------------
  ((x : A) → B x) → B x

case x returning _ of f = f x

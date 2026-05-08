module Prelude.List where

open import Prelude.Identity
open import Prelude.Level
open import Agda.Builtin.List renaming (_∷_ to _::_) public
open import Prelude.Product

-- List cons injectivity
::inj :
  {l : Level}
  {A : Set l}
  {x x' : A}
  {xs xs' : List A}
  (_ : x :: xs ≡ x' :: xs')
  → -----------------------
  x ≡ x' ∧ xs ≡ xs'

::inj refl = (refl , refl)

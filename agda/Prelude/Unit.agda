module Prelude.Unit where

open import Prelude.Level

----------------------------------------------------------------------
-- Unit type
----------------------------------------------------------------------
record 𝟙 {l : Level} : Set l where
  instance constructor tt

{-# BUILTIN UNIT 𝟙 #-}

⊤ : Set
⊤ = 𝟙

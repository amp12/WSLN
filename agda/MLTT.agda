module MLTT where

{- Martin-Löf Type Theory with countably many Agda-style
non-cumulative universes closed under Pi-types, natural number type
and intensional identity types. -}

open import MLTT.Syntax public
open import MLTT.Judgement public
open import MLTT.Cofinite public
open import MLTT.Ok public
open import MLTT.WellScoped public
open import MLTT.Weakening public
open import MLTT.Substitution public
open import MLTT.Admissible public
open import MLTT.ExistsFresh public
open import MLTT.Uniqueness public

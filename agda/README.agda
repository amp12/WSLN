module README where

{- WSLN is a library for the well-scoped version of the locally
  nameless method of representing syntax. The library is parameterised
  by a Plotkin-style binding signature. We give a proof of the
  adequacy of this style of representation with respect to naïve
  nameful syntax modulo α-conversion and some examples of its use.

Checked with Agda version 2.8.0 using flags
  --safe
  --without-K

© Andrew Pitts 2026 -}

-- Some (more or less) standard library definitions
open import Prelude

-- The Well-Scoped Locally Nameless library
open import WSLN

-- Adequacy of the well scoped locally nameless representation with
-- repect to nameful terms modulo α-equivalence (including
-- correctness for capture-avoiding substitution)
open import Adequacy

-- Example: well-scoped locally nameless representation of untyped
-- lambda calculus
open import Lambda

-- Example : well-scoped locally nameless representation of
-- π-calculus processes, structural congruence and reduction
open import PiCalc

-- Example: basic meta-theory for intensional Martin-Löf Type Theory
-- with countably many Agda-style non-cumulative universes closed
-- under Pi-types, natural number type and intensional identity types.
open import MLTT

-- Example: decidability of βη-conversion for Gödel's System T proved
-- in safe Agda
open import GST

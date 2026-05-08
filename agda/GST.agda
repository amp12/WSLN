module GST where

{- An illustration of using the WSLN library:

Decidability of βη-conversion for Gödel's System T using well-scoped
locally nameless syntax, proved via a normalization by evaluation
argument, in safe Agda

(flags: --without-K --safe)

© Andrew Pitts 2025 -}

open import WSLN public

open import GST.Syntax public
open import GST.Context public
open import GST.TypeSystem public
open import GST.WellScoped public
open import GST.Setoid public
open import GST.Renaming public
open import GST.Substitution public
open import GST.Admissible public
open import GST.UniqueTypes public
open import GST.NormalForm public
open import GST.Presheaf public
open import GST.TypeSemantics public
open import GST.ReifyReflect public
open import GST.TermSemantics public
open import GST.LogicalRelation public
open import GST.Sound public
open import GST.Normalization public
open import GST.DecidableConv public

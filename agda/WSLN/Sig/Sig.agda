module WSLN.Sig.Sig where

open import Prelude

open import WSLN.Index
open import WSLN.Atom
open import WSLN.Fresh

----------------------------------------------------------------------
-- Plotkin's binding signatures
----------------------------------------------------------------------
record Sig : Set₁ where
  constructor mkSig
  field
    Op : Set
    ar : Op → List ℕ

open Sig public

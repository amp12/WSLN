module Lambda where

-- A library for syntax using the well-scoped locally nameless
-- representation of expressions over any Plotkin binding signature
open import WSLN public

-- Nominal versus well-scoped locally nameless representation for
-- untyped lambda calculus
open import Lambda.Nominal public
open import Lambda.WellScopedLocallyNameless public
open import Lambda.Adequacy public

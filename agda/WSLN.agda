module WSLN where

{- A library for syntax using the well-scoped locally nameless
representation of expressions over any Plotkin binding signature. -}

-- Well scoped deBruijn indices
open import WSLN.Index public

-- Atomic names
open import WSLN.Atom public

-- Support and freshness
open import WSLN.Fresh public

-- Plotkin binding signatures
open import WSLN.Sig.Sig public

{- The rest of the library is parameterised by a Plotkin binding
signature -}

-- Scoped set of terms over a Plotkin binding signature
open import WSLN.Sig.Term public

-- Term-for-name substitution
open import WSLN.Sig.Substitution public

-- Concreting abstracted terms
open import WSLN.Sig.Concretion public

-- Abstracting names in terms
open import WSLN.Sig.Abstraction public

-- Size of terms
open import WSLN.Sig.Size public

open import Prelude

open import WSLN.Index
open import WSLN.Atom
open import WSLN.Fresh
open import WSLN.Sig.Sig
open import WSLN.Sig.Term
open import WSLN.Sig.Substitution

module WSLN.Sig.Concretion ⦃ Σ : Sig ⦄ where

----------------------------------------------------------------------
-- Opening
----------------------------------------------------------------------
infix 6 _~>_ _~>'_
_~>_ :
  {n : ℕ}
  -- index to be replaced
  (_ : Fin (1+ n))
  -- locally closed term with which to replace it
  (_ : Trm)
  -- term to be opened
  (_ : Trm[ 1+ n ])
  → ---------------
  Trm[ n ]

_~>'_ :
  {ns : List ℕ}
  {n : ℕ}
  (_ : Fin (1+ n))
  (_ : Trm)
  (_ : Arg[ 1+ n ] ns)
  → ------------------
  Arg[ n ] ns

-- Helper functions
opn :
  {m n : ℕ}
  (_ : Fin m)
  (_ : Trm)
  (_ : Trm[ m ])
  (_ : m ≡ 1+ n)
  → ------------
  Trm[ n ]
opn' :
  {ns : List ℕ}
  {m n : ℕ}
  (_ : Fin m)
  (_ : Trm)
  (_ : Arg[ m ] ns)
  (_ : m ≡ 1+ n)
  → ---------------
  Arg[ n ] ns

(i ~>  u) t  = opn i u t refl
(i ~>' u) ts = opn' i u ts refl

opn i u (𝐢 j) refl with i ≐ j
... | no ¬p =
  -- use the operation for removing an index while maintaining order
  𝐢 (remove i j ⦃ ≢→≠i ¬p ⦄)
... | yes _ =
  -- use the inclusion of Trm[ 0 ] into Trm[ n ]
  u ‿ _
opn _ _ (𝐚 x) _ = 𝐚 x
opn i u (𝐨 op ts) e = 𝐨 op (opn' i u ts e)
opn' _ _ [] _ = []
opn' i u (t :: ts) refl =
  -- here is where the helper function opn is used with
  -- its last argument not just equal to refl
  opn (suc^ i) u t 1++
  ::
  (opn' i u ts refl)

----------------------------------------------------------------------
-- Concretion
----------------------------------------------------------------------
record ConcretionSyntax (A : Set) : Set where
  constructor mkConcretionSyntax
  infixl 10 _[_] _[_][_] _[_][_][_]
  field
    _[_] : ∀{n} → Trm[ 1+ n ] → A → Trm[ n ]

  _[_][_] : ∀{n} → Trm[ 2+ n ] → A → A → Trm[ n ]
  e [ a ][ b ] = e [ a ] [ b ]

  _[_][_][_] : ∀{n} → Trm[ 3+ n ] → A → A → A → Trm[ n ]
  e [ a ][ b ][ c ] = e [ a ] [ b ] [ c ]

open ConcretionSyntax ⦃ ... ⦄ public

instance
  ConcretionSyntaxTrm : ConcretionSyntax Trm
  _[_] ⦃ ConcretionSyntaxTrm ⦄ t u = (zero ~> u) t
  -- The following allows us to write "t [ x ]" instead of "t [ 𝐚 x ]"
  ConcretionSyntax𝔸 : ConcretionSyntax 𝔸
  _[_] ⦃ ConcretionSyntax𝔸 ⦄ t x = t [ 𝐚 x ]

{-# DISPLAY opn Fin.zero u t refl  = t [ u ] #-}
{-# DISPLAY _~>_ Fin.zero u t refl = t [ u ] #-}

----------------------------------------------------------------------
-- Finite support properties of opening and concretion
----------------------------------------------------------------------
opnSupp :
  {m n : ℕ}
  (i : Fin m)
  (u : Trm)
  (t : Trm[ m ])
  (e : m ≡ 1+ n)
  → -------------------------
  supp t ⊆ supp (opn i u t e)
opnSupp' :
  {m n : ℕ}
  {ns : List ℕ}
  (i : Fin m)
  (u : Trm)
  (ts : Arg[ m ] ns)
  (e : m ≡ 1+ n)
  → ----------------------------
  supp ts ⊆ supp (opn' i u ts e)

opnSupp _ _ (𝐢 _) refl ()
opnSupp _ _ (𝐚 _) refl p = p
opnSupp i u (𝐨 op ts) refl = opnSupp' i u ts refl
opnSupp' _ _ [] refl ()
opnSupp' i u (t :: _ ) refl (∈∪₁ p) = ∈∪₁ (opnSupp (suc^ i) u t 1++ p)
opnSupp' i u (_ :: ts) refl (∈∪₂ p) = ∈∪₂ (opnSupp' i u ts refl p)

[]supp :
  {n : ℕ}
  (t : Trm[ 1+ n ])
  (u : Trm)
  → ---------------------
  supp t ⊆ supp (t [ u ])

[]supp t u = opnSupp zero u t refl

[]²supp :
  {n : ℕ}
  (t : Trm[ 2+ n ])
  (u v : Trm)
  → -------------------------
  supp t ⊆ supp (t [ u ][ v ])

[]²supp t u v = []supp (t [ u ]) v ∘ []supp t u

suppOpn :
  {m n : ℕ}
  (i : Fin m)
  (u : Trm)
  (t : Trm[ m ])
  (e : m ≡ 1+ n)
  → -----------------------------------
  supp (opn i u t e) ⊆ supp t ∪ supp u
suppOpn' :
  {m n : ℕ}
  {ns : List ℕ}
  (i : Fin m)
  (u : Trm)
  (ts : Arg[ m ] ns)
  (e : m ≡ 1+ n)
  → -------------------------------------
  supp (opn' i u ts e) ⊆ supp ts ∪ supp u

suppOpn{n = n} i u (𝐢 j) refl p with i ≐ j
... | equ rewrite supp‿ u n ⦃ 0≤ ⦄ = ∈∪₂ p
suppOpn _ _ (𝐚 _) refl p = ∈∪₁ p
suppOpn i u (𝐨 op ts) refl p = suppOpn' i u ts refl p
suppOpn' _ _ [] _ ()
suppOpn' i u (t :: ts) refl (∈∪₁ p)
    with suppOpn (suc^ i) u t 1++ p
... | ∈∪₁ p₁ = ∈∪₁ (∈∪₁ p₁)
... | ∈∪₂ p₂ = ∈∪₂ p₂
suppOpn' i u (t :: ts) refl (∈∪₂ p)
    with suppOpn' i u ts refl p
... | ∈∪₁ p₁ = ∈∪₁ (∈∪₂ p₁)
... | ∈∪₂ p₂ = ∈∪₂ p₂

supp[] :
  {n : ℕ}
  (t : Trm[ 1+ n ])
  (u : Trm)
  → ------------------------------
  supp (t [ u ]) ⊆ supp t ∪ supp u

supp[] t u = suppOpn zero u t refl

supp[]² :
  {n : ℕ}
  (t : Trm[ 2+ n ])
  (u v : Trm)
  → -----------------------------------------------
  supp (t [ u ][ v ]) ⊆ (supp t ∪ supp u) ∪ supp v

supp[]² t u v = ∪⊆ (supp[] t u) ⊆refl ∘ supp[] (t [ u ]) v

----------------------------------------------------------------------
-- Opening at an index greater than those in the term
----------------------------------------------------------------------
opnFin< :
  {n m : ℕ}
  (i : Fin m)
  (j : Fin n)
  (_ : m ≤ toℕ j) -- hence m < n
  ⦃ _ : m ≤ n ⦄   -- helper
  → -------------
  i ‿ n ≠ j

opnFin< zero (suc j) _ = z≠s j
opnFin< {1+ _} {1+ _} (suc i) (suc j) 1+≤ ⦃ 1+≤ ⦄ =
  s≠s ⦃ opnFin< i j it ⦄

opn< :
  {k m n : ℕ}
  (i : Fin n)
  (u : Trm)
  (e : n ≡ 1+ m)
  (_ : k ≤ toℕ i) -- hence k ≤ m
  ⦃ _ : k ≤ m ⦄   -- helper
  ⦃ _ : k ≤ n ⦄   -- helper
  (t : Trm[ k ])
  → -----------------------
  opn i u (t ‿ n) e ≡ t ‿ m
opn<' :
  {k m n : ℕ}
  {ns : List ℕ}
  (i : Fin n)
  (u : Trm)
  (e : n ≡ 1+ m)
  (_ : k ≤ toℕ i)
  ⦃ _ : k ≤ m ⦄
  ⦃ _ : k ≤ n ⦄
  (ts : Arg[ k ] ns)
  → --------------------------
  opn' i u (ts ‿ n) e ≡ ts ‿ m

opn<{m = m} i u refl q (𝐢 j) with i ≐ j ‿ (1+ m)
opn<{m = m} i u refl q (𝐢 j) | equ = Øelim (≠iirrefl (opnFin< j i q))
opn<{m = m} i u refl q (𝐢 j) | no ¬p = cong 𝐢 (trans
  (removeIrrel i (j ‿ 1+ m) ((j ‿ m ‿ 1+ m)⦃ ≤step ⦄)
    ⦃ ≢→≠i ¬p ⦄ ⦃ p' ⦄ (symm (‿assoc j m (1+ m) ⦃ ≤step ⦄)))
  (remove< i (j ‿ m) ⦃ ≤step ⦄ ⦃ p' ⦄ j<i))
  where
  p' : i ≠ (j ‿ m ‿ 1+ m)⦃ ≤step ⦄
  p' rewrite ‿assoc j m (1+ m) ⦃ ≤step ⦄ ⦃ it ⦄ = ≢→≠i ¬p

  j<i : toℕ (j ‿ m) < toℕ i
  j<i rewrite toℕ‿ j m ⦃ it ⦄ = ≤trans (toℕ< j) q
opn< _ _ _ _ (𝐚 _) = refl
opn< i u e q (𝐨 op ts) = cong (𝐨 op) (opn<' i u e q ts)
opn<' _ _ _ _ [] = refl
opn<'{k}{m} i u refl q (_::_{m = m'} t ts) = cong₂ _::_
  (opn< (suc^ i) u 1++ q' ⦃ +≤{m'} ⦄ ⦃ +≤ ⦄ t)
  (opn<' i u refl q ts)
  where
  q' : m' + k ≤ toℕ (suc^{m'} i)
  q' rewrite toℕ∘suc^ i m' = +≤ ⦃ q ⦄

----------------------------------------------------------------------
-- Substitution and renaming commutes with opening and concretion
----------------------------------------------------------------------
sbOpn :
  {m n : ℕ}
  (σ : Sb)
  (i : Fin m)
  (u : Trm)
  (t : Trm[ m ])
  (e : m ≡ 1+ n)
  → ------------------------------------------
  σ * (opn i u t e) ≡ opn i (σ * u) (σ * t) e
sbOpn' :
  {m n : ℕ}
  {ns : List ℕ}
  (σ : Sb)
  (i : Fin m)
  (u : Trm)
  (ts : Arg[ m ] ns)
  (e : m ≡ 1+ n)
    → -------------------------------------------
  σ * (opn' i u ts e) ≡ opn' i (σ * u) (σ * ts) e

sbOpn σ i u (𝐢 j) refl with i ≐ j
... | no _ = refl
... | equ = sb‿ u _ σ
sbOpn σ i u (𝐚 x) refl = symm (opn< i (σ * u) refl 0≤ (σ x))
sbOpn σ i u (𝐨 op ts) e = cong (𝐨 op) (sbOpn' σ i u ts e)
sbOpn' _ _ _ [] _ = refl
sbOpn' σ i u (t :: ts) refl = cong₂ _::_
  (sbOpn σ (suc^ i) u t 1++)
  (sbOpn' σ i u ts refl)

sb[] :
  {n : ℕ}
  (σ : Sb)
  (t : Trm[ 1+ n ])
  (u : Trm)
  → -------------------------------
  σ * (t [ u ]) ≡ (σ * t) [ σ * u ]

sb[] σ t u = sbOpn σ zero u t refl

rn[] :
  {n : ℕ}
  (ρ : Rn)
  (t : Trm[ 1+ n ])
  (u : Trm)
  → -------------------------------
  ρ * (t [ u ]) ≡ (ρ * t) [ ρ * u ]

rn[] ρ = sb[] (𝐚∘ ρ)

sb[]² :
  {n : ℕ}
  (σ : Sb)
  (t : Trm[ 2+ n ])
  (u u' : Trm)
  → -----------------------------------------------
  σ * (t [ u ][ u' ]) ≡ (σ * t) [ σ * u ][ σ * u' ]

sb[]² σ t u u'
  rewrite sb[] σ (t [ u ]) u'
  | sb[] σ t u = refl

rn[]² :
  {n : ℕ}
  (ρ : Rn)
  (t : Trm[ 2+ n ])
  (u u' : Trm)
  → --------------------------------------------
  ρ * (t [ u ][ u' ]) ≡ (ρ * t) [ ρ * u ][ ρ * u' ]

rn[]² ρ = sb[]² (𝐚∘ ρ)

sbUpdate[] :
  {n : ℕ}
  (σ : Sb)
  (x : 𝔸)
  (u : Trm)
  (t : Trm[ 1+ n ])
  (_ : x # t)
  → ---------------------------------------
  (σ ∘/ x := u) * (t [ x ]) ≡ (σ * t) [ u ]

sbUpdate[] σ x u t x#
  rewrite sb[] (σ ∘/ x := u) t (𝐚 x)
  | updateFresh σ x u t x#
  | updateEq{σ}{u} x = refl

sbUpdate[]² :
  {n : ℕ}
  (σ : Sb)
  (x y : 𝔸)
  (u v : Trm)
  (t : Trm[ 2+ n ])
  (_ : x # t)
  (_ : y # (t , x))
  → ---------------------------------------------------------
  ((σ ∘/ x := u) ∘/ y := v)* t [ x ][ y ] ≡ (σ * t)[ u ][ v ]

sbUpdate[]² σ x y u v t x#t (y#t ∉∪ (∉｛｝ y≠x))
  rewrite sb[]² ((σ ∘/ x := u) ∘/ y := v) t (𝐚 x) (𝐚 y)
  | updateFresh (σ ∘/ x := u) y v t y#t
  | updateFresh σ x u t x#t
  | :=Neq{f = (σ ∘/ x := u)}{v} y x (λ{refl → ≠𝔸irrefl y≠x})
  | :=Eq{f = σ}{u} x
  | :=Eq{f = (σ ∘/ x := u)}{v} y
  | ‿unit u ⦃ it ⦄
  | ‿unit v ⦃ it ⦄ = refl

rnUpdate[] :
  {n : ℕ}
  (ρ : Rn)
  (x x' : 𝔸)
  (t : Trm[ 1+ n ])
  (_ : x # t)
  → -----------------------------------------
  (ρ ∘/ x := x') * (t [ x ]) ≡ (ρ * t) [ x' ]

rnUpdate[] ρ x x' t x#
  rewrite sb[] (𝐚∘ (ρ ∘/ x := x')) t (𝐚 x)
  | :=Eq {f = ρ}{x'} x
  | updateFreshRn ρ x x' t x# = refl

ssb[] :
  {n : ℕ}
  (x : 𝔸)
  (u : Trm)
  (t : Trm[ 1+ n ])
  (_ : x # t)
  → --------------------------
  (x := u) * t [ x ] ≡ t [ u ]

ssb[] x u t x#
  rewrite sbUpdate[] idˢ x u t x#
  | sbUnit t = refl

ssb[]² :
  {n : ℕ}
  (x y : 𝔸)
  (u v : Trm)
  (t : Trm[ 2+ n ])
  (_ : x # t)
  (_ : y # (t , x))
  → ----------------------------------------------
  (x := u ∘/ y := v) * t [ x ][ y ] ≡ t [ u ][ v ]

ssb[]² x y u v t x#t y#tx
  rewrite sbUpdate[]² idˢ x y u v t x#t y#tx
  | sbUnit t = refl

srn[] :
  {n : ℕ}
  (x x' : 𝔸)
  (t : Trm[ 1+ n ])
  (_ : x # t)
  → -------------------------------
  (x := x') * (t [ x ]) ≡ t [ x' ]

srn[] x x' t x#
  rewrite  rnUpdate[] id x x' t x#
  | rnUnit t = refl

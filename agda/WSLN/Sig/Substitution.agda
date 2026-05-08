open import Prelude

open import WSLN.Index
open import WSLN.Atom
open import WSLN.Fresh

open import WSLN.Sig.Sig
open import WSLN.Sig.Term

module WSLN.Sig.Substitution ⦃ Σ : Sig ⦄ where

--------------------------------------------------------------------
-- Substitution of locally closed terms for names
--------------------------------------------------------------------
Sb :  Set
Sb = 𝔸 → Trm

-- Identity substitution
idˢ : Sb
idˢ = 𝐚
instance
  IdentitySb : Identity Sb
  id ⦃ IdentitySb ⦄ = idˢ

----------------------------------------------------------------------
-- Renaming functions
----------------------------------------------------------------------
Rn :  Set
Rn = 𝔸 → 𝔸

-- Identity renaming
idʳ : Rn
idʳ = id

-- Renamings as substitutions
𝐚∘ : Rn → Sb
𝐚∘ ρ = 𝐚 ∘ ρ

--------------------------------------------------------------------
-- Action of substitutions and renamings on terms
--------------------------------------------------------------------
actSb : ∀{n} → Sb → Trm[ n ] → Trm[ n ]
actSb' : ∀{n ns} → Sb → Arg[ n ] ns → Arg[ n ] ns

actSb  σ (𝐢 i)     = 𝐢 i
actSb  σ (𝐚 x)     = (σ x ‿ _)
actSb  σ (𝐨 op ts) = 𝐨 op (actSb' σ ts)
actSb' σ []        = []
actSb' σ (t :: ts)  = actSb σ t :: actSb' σ ts

-- Notation for substitution and renaming actions
instance
  ApplySb : ∀{n} → Apply Sb Trm[ n ] Trm[ n ]
  _*_ ⦃ ApplySb ⦄ = actSb
  ApplySb' : ∀{n ns } → Apply Sb (Arg[ n ] ns) (Arg[ n ] ns)
  _*_ ⦃ ApplySb' ⦄ = actSb'
  -- We treat the action of renaming as a special case of substitution
  ApplyRn : ∀{n} → Apply Rn Trm[ n ] Trm[ n ]
  _*_ ⦃ ApplyRn ⦄ ρ t = 𝐚∘ ρ * t
  ApplyRn' : ∀{n ns} → Apply Rn (Arg[ n ] ns) (Arg[ n ] ns)
  _*_ ⦃ ApplyRn' ⦄ ρ t = 𝐚∘ ρ * t

{-# DISPLAY actSb  σ t  = σ * t  #-}
{-# DISPLAY actSb' σ ts = σ * ts #-}

-- Substitution is support respecting
sbRespSupp :
  {n : ℕ}
  (σ σ' : Sb)
  (t : Trm[ n ])
  (_ : ∀ x → x ∈ supp t → σ x ≡ σ' x)
  → ---------------------------------
  σ * t ≡ σ' * t
sbRespSupp' :
  {n : ℕ}
  {ns : List ℕ}
  (σ σ' : Sb)
  (ts : Arg[ n ] ns)
  (_ : ∀ x → x ∈ supp ts → σ x ≡ σ' x)
  → ----------------------------------
  σ * ts ≡ σ' * ts

sbRespSupp _ _ (𝐢 _) _ = refl
sbRespSupp _ _ (𝐚 x) e
  rewrite e x ∈｛｝ = refl
sbRespSupp σ σ' (𝐨 op ts) e
  rewrite sbRespSupp' σ σ' ts e = refl
sbRespSupp' _ _ [] _ = refl
sbRespSupp' σ σ' (t :: ts) e
  rewrite sbRespSupp σ σ' t (λ x x∈t → e x (∈∪₁ x∈t))
  | sbRespSupp' σ σ' ts (λ x x∈ts → e x (∈∪₂ x∈ts)) = refl

rnRespSupp :
  {n : ℕ}
  (ρ ρ' : Rn)
  (t : Trm[ n ])
  (_ : ∀ x → x ∈ supp t → ρ x ≡ ρ' x)
  → ---------------------------------
  ρ * t ≡ ρ' * t

rnRespSupp ρ ρ' t e =
  sbRespSupp (𝐚∘ ρ) (𝐚∘ ρ') t (λ x x∈t → cong 𝐚 (e x x∈t))

--------------------------------------------------------------------
-- Composition of substitutions
--------------------------------------------------------------------
infixr 5 _∘ˢ_
_∘ˢ_ : Sb → Sb → Sb
(σ' ∘ˢ σ) x = σ' * (σ x)
instance
  CompositionSb : Composition Sb Sb Sb
  _∘_ ⦃ CompositionSb ⦄ = _∘ˢ_

--------------------------------------------------------------------
-- Substitution and renaming respect scope extension
--------------------------------------------------------------------
sb‿ :
  {m : ℕ}
  (t : Trm[ m ])
  (n : ℕ)
  ⦃ _ : m ≤ n ⦄
  (σ : Sb)
  → -----------------------
  σ * (t ‿ n) ≡ (σ * t) ‿ n
sb‿' :
  {ns : List ℕ}
  {m : ℕ}
  (ts : Arg[ m ] ns)
  (n : ℕ)
  ⦃ _ : m ≤ n ⦄
  (σ : Sb)
  → -------------------------
  σ * (ts ‿ n) ≡ (σ * ts) ‿ n

sb‿ (𝐢 _) _ _ = refl
sb‿ (𝐚 x) _ σ = symm (‿assoc (σ x) _ _)
sb‿ (𝐨 op ts) n σ = cong (𝐨 op) (sb‿' ts n σ )
sb‿' [] _ _ = refl
sb‿' (t :: ts) n σ = cong₂ _::_
  (sb‿  t (_ + n) ⦃ +≤ ⦄ σ)
  (sb‿' ts n σ)

rn‿ :
  {m : ℕ}
  (t : Trm[ m ])
  (n : ℕ)
  ⦃ _ : m ≤ n ⦄
  (ρ : Rn)
  → -----------------------
  ρ * (t ‿ n) ≡ (ρ * t) ‿ n

rn‿  t n ρ = sb‿ t n (𝐚∘ ρ)

--------------------------------------------------------------------
-- Unitary and associative laws
--------------------------------------------------------------------
sbUnit :
  {n : ℕ}
  (t : Trm[ n ])
  → ------------
  idˢ * t ≡ t
sbUnit' :
  {ns : List ℕ}
  {n : ℕ}
  (ts : Arg[ n ] ns)
  → ----------------
  idˢ * ts ≡ ts

sbUnit (𝐢 _) = refl
sbUnit (𝐚 _) = refl
sbUnit (𝐨 op ts)
  rewrite sbUnit' ts = refl
sbUnit' [] = refl
sbUnit' (t :: ts)
  rewrite sbUnit t
  | sbUnit' ts = refl

sbAssoc :
  {n : ℕ}
  (σ σ' : Sb)
  (t : Trm[ n ])
  → -------------------------
  (σ' ∘ σ) * t ≡ σ' * (σ * t)
sbAssoc' :
  {ns : List ℕ}
  {n : ℕ}
  (σ σ' : Sb)
  (ts : Arg[ n ] ns)
  → ---------------------------
  (σ' ∘ σ) * ts ≡ σ' * (σ * ts)

sbAssoc _ _ (𝐢 _) = refl
sbAssoc{n} σ σ' (𝐚 x)
  rewrite  sb‿ (σ x) n σ' = refl
sbAssoc σ σ' (𝐨 op ts)
  rewrite sbAssoc' σ σ' ts = refl
sbAssoc' _ _ [] = refl
sbAssoc' σ σ' (t :: ts)
  rewrite sbAssoc σ σ' t
  | sbAssoc' σ σ' ts = refl

rnUnit :
  {n : ℕ}
  (t : Trm[ n ])
  → ------------
  idʳ * t ≡ t

rnUnit = sbUnit

rnAssoc :
  {n : ℕ}
  (ρ ρ' : Rn)
  (t : Trm[ n ])
  → --------------------------
  (ρ' ∘ ρ) * t ≡ ρ' * (ρ * t)

rnAssoc ρ ρ' = sbAssoc (𝐚∘ ρ) (𝐚∘ ρ')

--------------------------------------------------------------------
-- Properties of updating substitutions and renamings
--------------------------------------------------------------------
updateEq :
  {σ : Sb}
  {t : Trm}
  (x : 𝔸)
  → ---------------------
  (σ ∘/ x := t) * 𝐚 x ≡ t

updateEq{σ}{t} x
  rewrite :=Eq {f = σ} {t} x
  | ‿unit t ⦃ it ⦄ = refl

updateFresh :
  {n : ℕ}
  (σ : Sb)
  (x : 𝔸)
  (u : Trm)
  (t : Trm[ n ])
  (_ : x # t)
  → -----------------------
  (σ ∘/ x := u) * t ≡ σ * t

updateFresh σ x u t x#t = sbRespSupp (σ ∘/ x := u) σ t
  (λ y y∈t → :=Neq x _ λ{refl → ∉→¬∈ x#t y∈t})

updateIdSb :
  {n : ℕ}
  (x : 𝔸)
  (t : Trm[ n ])
  → ----------------
  (x := 𝐚 x) * t ≡ t

updateIdSb x t
  rewrite sbRespSupp (x := 𝐚 x) idˢ t (λ x' _ → :=Id x x')
  | sbUnit t = refl

ssbFresh :
  {n : ℕ}
  (x : 𝔸)
  (u : Trm)
  (t : Trm[ n ])
  (_ : x # t)
  → --------------
  (x := u) * t ≡ t

ssbFresh x u t x#t
  rewrite updateFresh idˢ x u t x#t
  | sbUnit t = refl

updateRn :
  {n : ℕ}
  (ρ : Rn)
  (x x' : 𝔸)
  (t : Trm[ n ])
  → --------------------------------------------
  (𝐚∘ ρ ∘/ x := 𝐚 x') * t ≡ 𝐚∘(ρ ∘/ x := x') * t
updateRn ρ x x' t =
  sbRespSupp (𝐚∘ ρ ∘/ x := 𝐚 x') (𝐚∘ (ρ ∘/ x := x')) t f
  where
  f : ∀ y → y ∈ supp t → (𝐚∘ ρ ∘/ x := 𝐚 x') y ≡ 𝐚∘ (ρ ∘/ x := x') y
  f y _ with x ≐ y
  ... | no _  = refl
  ... | yes _ = refl

updateId :
  {n : ℕ}
  (x : 𝔸)
  (t : Trm[ n ])
  → --------------
  (x := x) * t ≡ t

updateId x t
  rewrite rnRespSupp (x := x) id t (λ x' _ → :=Id x x') = rnUnit t

updateFreshRn :
  {n : ℕ}
  (ρ : Rn)
  (x y : 𝔸)
  (t : Trm[ n ])
  (_ : x # t)
  → -----------------------
  (ρ ∘/ x := y) * t ≡ ρ * t

updateFreshRn ρ x y t x#t
  rewrite symm (updateRn ρ x y t) = updateFresh (𝐚∘ ρ) x (𝐚 y) t x#t

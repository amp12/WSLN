module Lambda.Adequacy where

open import Prelude
open import WSLN
open import Lambda.Nominal
open import Lambda.WellScopedLocallyNameless

----------------------------------------------------------------------
-- Translation of nominal terms to locally nameless terms
----------------------------------------------------------------------
infix 1 ⟦_⟧
⟦_⟧ : Nom → Lam
⟦ 𝐯 x     ⟧ = 𝐯 x
⟦ app M N ⟧ = ⟦ M ⟧ ∙ ⟦ N ⟧
⟦ lam x M ⟧ = 𝛌 (x ． ⟦ M ⟧)

----------------------------------------------------------------------
-- Support property
----------------------------------------------------------------------
⟦supp⟧ :
  (M : Nom)
  → ------------------
  supp ⟦ M ⟧ ⊆ supp M

⟦supp⟧ (𝐯 x) = id
⟦supp⟧ (app M N) = ⊆ub
  (∈∪₁ ∘ ⟦supp⟧ M)
  (⊆ub (∈∪₂ ∘ ⟦supp⟧ N) λ())
⟦supp⟧ (lam x M) = ⊆ub
  (∈∪₂ ∘ ⟦supp⟧ M ∘ suppAbs x ⟦ M ⟧)
  λ()

----------------------------------------------------------------------
-- Renaming
----------------------------------------------------------------------
-- The property that a renaming is injective on the names occurring in
-- a term
Inj : (𝔸 → 𝔸) → Nom → Set
Inj ρ M = ∀{x x'} → x ∈ supp M → x' ∈ supp M → ρ x ≡ ρ x' → x ≡ x'

-- A renaming preserves the translation of a term if it
-- acts injectively on the names occurring in the term
⟦rn⟧ :
  (ρ : 𝔸 → 𝔸)
  (M : Nom)
  (_ : Inj ρ M)
  → -------------------
  ⟦ ρ * M ⟧ ≡ ρ * ⟦ M ⟧

⟦rn⟧ ρ (𝐯 x) e = refl
⟦rn⟧ ρ (app M N) e = cong₂ _∙_
  (⟦rn⟧ ρ M λ p p' → e (∈∪₁ p) (∈∪₁ p'))
  (⟦rn⟧ ρ N λ p p' → e (∈∪₂ p) (∈∪₂ p'))
⟦rn⟧ ρ (lam x M) e =
  begin
    𝛌 (ρ x ． ⟦ ρ * M ⟧)
  ≡⟨ cong (λ a → 𝛌 (ρ x ． a))
     (⟦rn⟧ ρ M λ p p' → e (∈∪₂ p) (∈∪₂ p')) ⟩
    𝛌 (ρ x ． ρ * ⟦ M ⟧)
  ≡˘⟨ cong (λ a → 𝛌 (ρ x ． a))
      (rnRespSupp (ρ ∘ x := ρ x) ρ ⟦ M ⟧ λ y q →
        :=Id {f = ρ} x y) ⟩
    𝛌 ( ρ x ． (ρ ∘ x := ρ x) * ⟦ M ⟧)
  ≡˘⟨ cong 𝛌 (rnAbs ρ x (ρ x) ⟦ M ⟧ λ y p q r →
      q (e (∈∪₁ ∈｛｝) (∈∪₂ (⟦supp⟧ M p)) r)) ⟩
    𝛌 (ρ * (x ． ⟦ M ⟧))
  ∎

-- Fresh renaming is injective
InjUpdate :
  (x y : 𝔸)
  (M : Nom)
  (_ : y # M)
  → -----------------
  Inj (id ∘ x := y) M

InjUpdate x _ _ _ {z}{z'} _ _ _    with x ≐ z | x ≐ z'
InjUpdate x y M y#        _ _ e    | no _     | no _ = e
InjUpdate x y M y#        p _ refl | no _     | equ
  with () ← ∉→¬∈ y# p
InjUpdate x y M y#        _ p refl | equ      | no _
  with () ← ∉→¬∈ y# p
InjUpdate _ _ _ _         _ _ _    | equ      | equ = refl

----------------------------------------------------------------------
-- Soundness
----------------------------------------------------------------------
sound :
  {M N : Nom}
  (_ : M ~ N)
  → -----------
  ⟦ M ⟧ ≡ ⟦ N ⟧

sound (~var x) = refl

sound (~app q₀ q₁) = cong₂ _∙_ (sound q₀) (sound q₁)

sound (~lam{y}{x}{x'}{M}{M'} q₀ (q₁ ∉∪ q₁')) =
  begin
    𝛌 (x ． ⟦ M ⟧)
  ≡⟨ cong 𝛌 (alphaEquiv x y ⟦ M ⟧ (⊆∉ (⟦supp⟧ M) q₁)) ⟩
    𝛌 (y ． (id ∘ x := y) * ⟦ M ⟧)
  ≡˘⟨ cong (λ a → 𝛌 (y ． a))
      (⟦rn⟧ (x ↦ y) M (InjUpdate x y M q₁)) ⟩
    𝛌 (y ． ⟦ (x ↦ y) * M ⟧)
  ≡⟨ cong (λ a → 𝛌 (y ． a)) (sound q₀) ⟩
    𝛌 (y ． ⟦ (x' ↦ y) * M' ⟧)
  ≡⟨ cong (λ a → 𝛌 (y ． a))
     (⟦rn⟧ (x' ↦ y) M' (InjUpdate x' y M' q₁')) ⟩
    𝛌 (y ． (x' ↦ y) * ⟦ M' ⟧)
  ≡˘⟨ cong 𝛌 (alphaEquiv x' y ⟦ M' ⟧ (⊆∉ (⟦supp⟧ M') q₁')) ⟩
    𝛌 (x' ． ⟦ M' ⟧)
  ∎

----------------------------------------------------------------------
-- Injectivity
----------------------------------------------------------------------
⟦⟧injective :
  (M N : Nom)
  (_ : ⟦ M ⟧ ≡ ⟦ N ⟧)
  → -----------------
  M ~ N

-- We proceed by induction on the size of nominal lambda terms:
⟦⟧injective≤ :
  {h : ℕ}
  (M N : Nom)
  (_ : size M ≤ h)
  (_ : size N ≤ h)
  (_ : ⟦ M ⟧ ≡ ⟦ N ⟧)
  → -----------------
  M ~ N

⟦⟧injective≤ (𝐯 x) (𝐯 _) _ _ refl = ~var x

⟦⟧injective≤ {1+ _} (app M N) (app M' N') 1+≤ 1+≤ e
  with (e₁ , e₂) ← ∙inj e = ~app
  (⟦⟧injective≤ M M' (it ∘ ≤max₁ _ _) (it ∘ ≤max₁ _ _) e₁)
  (⟦⟧injective≤ N N' (it ∘ ≤max₂ (size M) _) (it ∘ ≤max₂ (size M') _) e₂)

⟦⟧injective≤ {1+ h} (lam x M) (lam x' M') 1+≤ 1+≤ e
  with (y , y#) ← fresh (M , M') = ~lam
  (⟦⟧injective≤ ((x ↦ y) * M) ((x' ↦ y) * M') q q' e')
  y#
  where
  q : size ((x ↦ y) * M) ≤ h
  q rewrite sizeRen M (x ↦ y) = it

  q' : size ((x' ↦ y) * M') ≤ h
  q' rewrite sizeRen M' (x' ↦ y) = it

  e' : ⟦ (x ↦ y) * M ⟧ ≡ ⟦ (x' ↦ y) * M' ⟧
  e' =
    begin
      ⟦ (x ↦ y) * M ⟧
    ≡⟨ ⟦rn⟧ (x ↦ y) M (InjUpdate x y M (∉∪₁ y#)) ⟩
      (x ↦ y) * ⟦ M ⟧
    ≡⟨ 𝛌α{x}{x'}{y}{⟦ M ⟧}{⟦ M' ⟧} e
       ((⊆∉ (⟦supp⟧ M) (∉∪₁ y#)) ∉∪ (⊆∉ (⟦supp⟧ M') (∉∪₂ y#))) ⟩
      (x' ↦ y) * ⟦ M' ⟧
    ≡˘⟨ ⟦rn⟧ (x' ↦ y) M' (InjUpdate x' y M' (∉∪₂ y#)) ⟩
      ⟦ (x' ↦ y) * M' ⟧
    ∎

⟦⟧injective M N =
  ⟦⟧injective≤{max (size M) (size N)} M N (≤max₁ _ _) (≤max₂ _ _)

----------------------------------------------------------------------
-- Surjectivity
----------------------------------------------------------------------
⟦⟧surjective : (a : Lam) → ∃[ M ] ⟦ M ⟧ ≡ a

-- We proceed by induction on the size of well-scoped locally nameless
-- lambda terms:
⟦⟧surjective≤ :
  {h : ℕ}
  (a : Lam)
  (_ : size a ≤ h)
  → --------------
  ∃[ M ] ⟦ M ⟧ ≡ a

⟦⟧surjective≤ (𝐯 x) _ = (𝐯 x , refl)

⟦⟧surjective≤ {1+ _} (a ∙ b) 1+≤
   with (M , refl) ← ⟦⟧surjective≤ a (it ∘ ≤max₂ (size b) _)
   | (N , refl) ← ⟦⟧surjective≤ b (it ∘ ≤max₁ _ _) =
   (app M N , refl)

⟦⟧surjective≤ {1+ _} (𝛌 a) 1+≤
  with (x , x#) ← fresh a
  with (M , e) ← ⟦⟧surjective≤ (a ❪ x ❫) (size❪❫≤ a x it) =
  (lam x M , cong 𝛌 e')
  where
  e' : x ． ⟦ M ⟧ ≡ a
  e' rewrite e | absConc x a x# = refl

⟦⟧surjective a = ⟦⟧surjective≤ a ≤refl

----------------------------------------------------------------------
-- Bijection
----------------------------------------------------------------------
infix 6 ⟦_⟧⁻¹
⟦_⟧⁻¹ : Lam → Nom

⟦_⟧⁻¹ a = π₁ (⟦⟧surjective a)

⟦⟧∘⟦⟧⁻¹ :
  (a : Lam)
  → -------------
  ⟦ ⟦ a ⟧⁻¹ ⟧ ≡ a

⟦⟧∘⟦⟧⁻¹ a = π₂ (⟦⟧surjective a)


⟦⟧⁻¹∘⟦⟧ :
  (M : Nom)
  → -------------
  ⟦ ⟦ M ⟧ ⟧⁻¹ ~ M

⟦⟧⁻¹∘⟦⟧ M = ⟦⟧injective ⟦ ⟦ M ⟧ ⟧⁻¹ M (⟦⟧∘⟦⟧⁻¹ ⟦ M ⟧)

----------------------------------------------------------------------
-- Substitution correctness
----------------------------------------------------------------------
correct :
  (M : Nom)
  (x : 𝔸)
  (N : Nom)
  → -----------------------------------
  ⟦ [ M / x ] N ⟧ ≡ (x ≔ ⟦ M ⟧) * ⟦ N ⟧

-- We proceed by induction on the size of nominal lambda terms:
correct≤ :
  {h : ℕ}
  (M : Nom)
  (x : 𝔸)
  (N : Nom)
  (q : size N ≤ h)
  → --------------------------------------
  ⟦ [ M / x ]≤ N q ⟧ ≡ (x ≔ ⟦ M ⟧) * ⟦ N ⟧

correct≤ M x (𝐯 y) _
    with x ≐ y
... | no ¬p = refl
... | yes p rewrite ‿unit ⟦ M ⟧ ⦃ ≤refl ⦄ = refl

correct≤ {1+ _} M x (app N₁ N₂) 1+≤ = cong₂ _∙_
  (correct≤ M x N₁ (it ∘ ≤max₁ _ _))
  (correct≤ M x N₂ (it ∘ ≤max₂ (size N₁) _))

correct≤ {1+ _} M x (lam y N) 1+≤ = cong 𝛌 q
  where
  z = new (supp(M , x , N))
  z#M = ∉∪₁ (new∉ (supp(M , x , N)))
  z#x = ∉∪₁ (∉∪₂ (new∉ (supp(M , x , N))))
  z#N = ∉∪₂ (∉∪₂ (new∉ (supp(M , x , N))))

  q : z ． ⟦ [ M / x ]≤ ((y ↦ z) * N) (sizeRen≤ N (y ↦ z) it) ⟧
    ≡ (x ≔ ⟦ M ⟧) * (y ． ⟦ N ⟧)
  q =
    begin
      z ． ⟦ [ M / x ]≤ ((y ↦ z) * N) (sizeRen≤ N (y ↦ z) it) ⟧
    ≡⟨ cong (z ．_) (correct≤ M x ((y ↦ z) * N)
       (sizeRen≤ N (y ↦ z) it)) ⟩
      z ． (x ≔ ⟦ M ⟧) * ⟦ (y ↦ z) * N ⟧
    ≡⟨ cong (λ a → z ． (x ≔ ⟦ M ⟧) * a) (⟦rn⟧ (y ↦ z) N
       (InjUpdate y z N z#N)) ⟩
      z ． (x ≔ ⟦ M ⟧) * 𝐬(y ↦ z) * ⟦ N ⟧
    ≡˘⟨ cong (λ a → z ． (x ≔ ⟦ M ⟧) * a) (updateRn id y z ⟦ N ⟧) ⟩
      z ． (x ≔ ⟦ M ⟧) * (y ≔ 𝐯 z) * ⟦ N ⟧
    ≡˘⟨ cong (z ．_) (sbAssoc (y ≔ 𝐯 z) (x ≔ ⟦ M ⟧) ⟦ N ⟧) ⟩
      z ． (x ≔ ⟦ M ⟧ ∘ y ≔ 𝐯 z) * ⟦ N ⟧
    ≡⟨ cong (z ．_) (sbRespSupp (x ≔ ⟦ M ⟧ ∘ y ≔ 𝐯 z)
      (x ≔ ⟦ M ⟧ ∘ y := 𝐯 z) ⟦ N ⟧ g) ⟩
      z ． (x ≔ ⟦ M ⟧ ∘ y := 𝐯 z) * ⟦ N ⟧
    ≡˘⟨ sbAbs (x ≔ ⟦ M ⟧) y z ⟦ N ⟧ f ⟩
      (x ≔ ⟦ M ⟧) * (y ． ⟦ N ⟧)
    ∎
    where
    f :
      (y' : ℕ)
      (_ : y' ∈ supp ⟦ N ⟧)
      (_ : ¬ (y ≡ y'))
      → -------------------
      z # (x ≔ ⟦ M ⟧) y'
    f y' r s
        with x ≐ y'
    ... | no _ = ∉｛｝ (≢→≠𝔸 λ{refl → ∉→¬∈ z#N (⟦supp⟧ N r) })
    ... | yes _ = ⊆∉ (⟦supp⟧ M) z#M

    g :
      (y' : 𝔸) →
      (_ : y' ∈ supp ⟦ N ⟧)
      → ----------------------------
      (x ≔ ⟦ M ⟧) * ((y ≔ 𝐯 z) y') ≡
      (x ≔ ⟦ M ⟧ ∘ y := 𝐯 z) y'
    g y' r
        with  y ≐ y'
    ... | no ¬p = ‿unit _
    ... | equ = ssbFresh x ⟦ M ⟧ (𝐯 z) (#symm z#x)

correct M x N = correct≤ M x N ≤refl

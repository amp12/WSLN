module MLTT1.Renaming where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTT1.Syntax
open import MLTT1.Judgement
open import MLTT1.TypeSystem
open import MLTT1.ContextConversion
open import MLTT1.Ok
open import MLTT1.WellScoped

----------------------------------------------------------------------
-- Well-typed renamings
----------------------------------------------------------------------
infix 4 _⊢ʳ_∶_
data _⊢ʳ_∶_ (Γ' : Cx) : Rn → Cx → Set where
  ◇ :
    {ρ : Rn}
    (q : Ok Γ')
    → ----------
    Γ' ⊢ʳ ρ ∶ ◇
  ∷ :
    {l : Lvl}
    {Γ : Cx}
    {ρ : Rn}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ʳ ρ ∶ Γ)
    (q₁ : Γ ⊢ A ∶𝐔 l)
    (q₂ : (ρ x , ρ * A , l) isIn Γ')
    → ------------------------------
    Γ' ⊢ʳ ρ ∶ (Γ ⸴ x ∶ A ∶ l)

----------------------------------------------------------------------
-- Well-formedness
----------------------------------------------------------------------
rnOk :
  {Γ' Γ : Cx}
  {ρ : Rn}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ---------------
  Ok Γ

rnOk (◇ _) = ◇
rnOk (∷ q q' _) = ∷⁻ q'

okRn :
  {Γ' Γ : Cx}
  {ρ : Rn}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → ---------------
  Ok Γ'

okRn (◇ q) = q
okRn (∷ q _ _) = okRn q

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wkRn :
  {l : Lvl}
  {Γ Γ' : Cx}
  {ρ : Rn}
  {A : Ty}
  (x : 𝔸)
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ A ∶𝐔 l)
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  → -----------------------
  (Γ' ⸴ x ∶ A ∶ l) ⊢ʳ ρ ∶ Γ

wkRn x q (◇ q') = ◇ (∷ q q')
wkRn x q (∷ q₀ q₁ q₂) = ∷ (wkRn x q q₀) q₁ (isInOld q₂)

----------------------------------------------------------------------
-- Identity renaming is well-typed
----------------------------------------------------------------------
⊢id :
  {Γ : Cx}
  (_ : Ok Γ)
  → ---------
  Γ ⊢ʳ id ∶ Γ

⊢id ◇ = ◇ ◇
⊢id (∷{l}{x = x} q q') = ∷
  (wkRn _ q (⊢id q'))
  q
  (isInNew (cong (λ A' → (x , A' , l)) (rnUnit _)))

----------------------------------------------------------------------
-- Extensionality property of well-typed renamings
----------------------------------------------------------------------
rnExt :
  {ρ ρ' : Rn}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : ∀ x → x ∈ dom Γ → ρ x ≡ ρ' x)
  → --------------------------------
  Γ' ⊢ʳ ρ' ∶ Γ

rnExt (◇ q) _ = ◇ q
rnExt{ρ}{ρ'} (∷{A = A}{x} q q₁ q₂) e
  rewrite rnRespSupp ρ ρ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ (∈∪₁ p'))))
  | e x (∈∪₂ ∈｛｝) = ∷ (rnExt q (λ y r → e y (∈∪₁ r))) q₁ q₂

----------------------------------------------------------------------
-- Lifting renamings
----------------------------------------------------------------------
liftRn :
  {l : Lvl}
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ A ∶𝐔 l)
  -- helper hypothesis
  (_ : Γ' ⊢ ρ * A ∶𝐔 l)
  → ---------------------------------------------------
  (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ʳ (x := x')ρ ∶ (Γ ⸴ x ∶ A ∶ l)

liftRn{l}{ρ}{Γ}{Γ'}{A}{x}{x'} ⊢ρ ⊢A ⊢ρA = ∷ (wkRn x' ⊢ρA ⊢ρ') ⊢A q
  where
  e : ∀ y → y ∈ dom Γ → ρ y ≡ (x := x')ρ y
  e y  y∈Γ with x ≐ y
  ... | no _ = refl
  ... | equ = Øelim (∉→¬∈ it y∈Γ)

  ⊢ρ' : Γ' ⊢ʳ (x := x')ρ ∶ Γ
  ⊢ρ' = rnExt ⊢ρ e

  q : ((x := x')ρ x , (x := x')ρ * A , l) isIn (Γ' ⸴ x' ∶ ρ * A ∶ l)
  q rewrite updateFreshRn ρ x x' A (∉∪₁ (⊢# ⊢A it))
    | :=Eq{f = ρ}{x'} x = isInNew refl

-- Iterated lifting
liftRn² :
  {l l' : Lvl}
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  {x y x' y' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  ⦃ _ : y # (Γ , x) ⦄
  ⦃ _ : y' # (Γ' , x') ⦄
  (p : Γ' ⊢ʳ ρ ∶ Γ)
  (p₁ : Γ ⊢ A ∶𝐔 l)
  (p₂ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ∶𝐔 l')
  (p₃ : ρ * A ≡ A')
  (p₄ : (x := x')ρ * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ A' ∶𝐔 l)
  (h' : (Γ' ⸴ x' ∶ A' ∶ l) ⊢ B' ∶𝐔 l')
  → ----------------------------------------------------
  (Γ' ⸴ x' ∶ A' ∶ l ⸴ y' ∶ B' ∶ l') ⊢ʳ
    (y := y')((x := x')ρ) ∶ (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ B ∶ l')

liftRn² p p₁ p₂ refl refl h h' = liftRn (liftRn p p₁ h) p₂ h'

----------------------------------------------------------------------
-- Types of variables under renaming
----------------------------------------------------------------------
rnVar :
  {l : Lvl}
  {ρ : Rn}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : (x , A , l) isIn Γ)
  → -----------------------
  (ρ x , ρ * A , l) isIn Γ'

rnVar (∷ _ _ q)  (isInNew refl) = q
rnVar (∷ q' _ _) (isInOld q)    = rnVar q' q

rnDom :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {x : 𝔸}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : x ∈ dom Γ)
  → ---------------
  ρ x ∈ dom Γ'

rnDom p q =
  let (_ , _ , q') = dom→isIn q
  in isIn→dom (rnVar p q')

----------------------------------------------------------------------
-- Renaming preserves provable judgements
----------------------------------------------------------------------
rnJg :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {J : Jg}
  (_ : Γ' ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ J)
  → ---------------
  Γ' ⊢ ρ * J

rnJg p (⊢conv q₀ q₁) = ⊢conv
  (rnJg p q₀)
  (rnJg p q₁)

rnJg p (⊢𝐯 _ q) = ⊢𝐯 (okRn p) (rnVar p q)

rnJg p (⊢𝐔 _) = ⊢𝐔 (okRn p)

rnJg{ρ}{Γ' = Γ'} p (⊢𝚷{l}{l'}{A = A}{B}{x} q₀ q₁ q₂) =
  ⊢𝚷{x = x'}
    (rnJg p q₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ B' ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnJg (liftRn p q₀ (rnJg p q₀)) q₁))
    x'#
  where
  S = supp (ρ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg{ρ}{Γ' = Γ'} p (⊢𝛌{l}{l'}{A}{B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) =
  ⊢𝛌{x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ b' ∶ B' ∶ l')
      (rnUpdate⟨⟩ ρ x x' b q₁')
      (rnUpdate⟨⟩ ρ x x' B q₁)
      (rnJg (liftRn p h₀ (rnJg p h₀)) q₀))
    x'#
    (rnJg p h₀)
    (subst (λ C → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ C ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₁)
      (rnJg (liftRn p h₀ (rnJg p h₀)) h₁))
  where
  S = supp ((ρ * B , ρ * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg{ρ}{Γ' = Γ'} p (⊢∙{l}{l'}{A}{B}{a}{b}{x} q₀ q₁ q₂ q₃ h)
  rewrite rn⟨⟩ ρ B a =
  -- helper hypothesis used
  ⊢∙
    (rnJg p q₀)
    (rnJg p q₁)
    (subst (λ C → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ C ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₃)
      (rnJg (liftRn p h (rnJg p h)) q₂))
    x'#
    (rnJg p h)
  where
  S = supp (ρ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg p (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
  (rnJg p q₀)
  (rnJg p q₁)
  (rnJg p q₂)

rnJg p (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐫𝐞𝐟𝐥
  (rnJg p q)
  (rnJg p h)

rnJg{ρ}{Γ' = Γ'} p (⊢𝐉{l}{l'}{A}{C}{a}{b}{c}{e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁)
  rewrite rn⟨⟩² ρ C b e =
  -- helper hypotheses used
  ⊢𝐉{x = x'}{y'}
    q₀'
    (rnJg p q₁)
    (rnJg p q₂)
    q₃'
    (rnJg p q₄)
    x'#
    y'#
    (rnJg p h₀)
    h₁'
  where
  S = supp (ρ * C , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (ρ * C , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  q₃' : Γ' ⊢ ρ * c ∶ (ρ * C) ⟨ ρ * a ⸴ 𝐫𝐞𝐟𝐥 (ρ * a)⟩ ∶ l'
  q₃' = subst (λ C' → Γ' ⊢ ρ * c ∶ C' ∶ l')
    (rn⟨⟩² ρ C a (𝐫𝐞𝐟𝐥 a))
    (rnJg p q₃)

  eq : (x := x')ρ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x')
  eq rewrite  updateFreshRn ρ x x' A (∉∪₂ (⊢# q₁ it))
     | updateFreshRn ρ x x' a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = ρ}{x'} x = refl

  h₁' : (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ I ∶𝐔 l)
    eq
    (rnJg (liftRn p h₀ (rnJg p h₀)) h₁)

  eq' : (y := y')((x := x')ρ) * C ⟨ x ⸴ y ⟩ ≡ (ρ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) C (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' C q₆
      | updateFreshRn ρ x x' C q₅
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  q₀' : (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢
    (ρ * C) ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst (λ C →
    (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢ C ∶𝐔 l')
    eq'
    (rnJg (liftRn² p h₀ h₁ refl eq (rnJg p h₀) h₁') q₀)

rnJg p (⊢𝐍𝐚𝐭 _) = ⊢𝐍𝐚𝐭 (okRn p)

rnJg p (⊢𝐳𝐞𝐫𝐨 _) = ⊢𝐳𝐞𝐫𝐨 (okRn p)

rnJg p (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (rnJg p q)

rnJg{ρ}{Γ' = Γ'} p (⊢𝐧𝐫𝐞𝐜{l}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
  rewrite rn⟨⟩ ρ C a =
  -- helper hypotheses used
  ⊢𝐧𝐫𝐞𝐜{x = x'}{y'}
    q₀'
    q₁'
    (rnJg p q₂)
    x'#
    y'#
    h'
  where
  S = supp ((ρ * C , ρ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (ρ * c₊ , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ (⟨⟩supp C 𝐳𝐞𝐫𝐨)) (∉∪₁ it)

  q₀' :  Γ' ⊢ ρ * c₀ ∶ (ρ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ ρ * c₀ ∶ C' ∶ l)
    (rn⟨⟩ ρ C 𝐳𝐞𝐫𝐨)
    (rnJg p q₀)

  eq : (x := x')ρ * C ⟨ x ⟩ ≡ (ρ * C)⟨ x' ⟩
  eq rewrite rn⟨⟩ ((x := x')ρ) C (𝐯 x)
     | updateFreshRn ρ x x' C q₃
     | :=Eq{f = ρ}{x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (ρ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (rnJg (liftRn p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okRn p))) h)

  eq' : (y := y')((x := x')ρ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (ρ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) c₊ (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' c₊ q₄
      | updateFreshRn ρ x x' c₊ q₃'
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq'' : (y := y')((x := x')ρ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (ρ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite rn⟨⟩ ((y := y')((x := x')ρ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFreshRn ((x := x')ρ) y y' C y#C
       | updateFreshRn ρ x x' C q₃
       | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = ρ}{x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C)⟨ x' ⟩ ∶ l) ⊢
      (ρ * c₊)⟨ x' ⸴ y' ⟩ ∶ (ρ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (rnJg
        (liftRn² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okRn p)) h')
        q₁)

rnJg p (Refl q) = Refl (rnJg p q)

rnJg p (Symm q) = Symm (rnJg p q)

rnJg p (Trans q₀ q₁) = Trans
  (rnJg p q₀)
  (rnJg p q₁)

rnJg p (＝conv q₀ q₁) = ＝conv
  (rnJg p q₀)
  (rnJg p q₁)

rnJg{ρ}{Γ' = Γ'} p (𝚷Cong{l}{l'}{A = A}{B = B}{B'}{x}
  q₀ q₁ (q₂ ∉∪ q₂') h) =
  𝚷Cong{x = x'}
    (rnJg p q₀)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnUpdate⟨⟩ ρ x x' B' q₂')
      (rnJg (liftRn p h (rnJg p h)) q₁))
  x'#
  (rnJg p h)
  where
  S = supp ((ρ * B , ρ * B') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg{ρ}{Γ' = Γ'} p (𝛌Cong{l}{l'}{A}{B = B}{b}{b'}{x}
  q₀ q₁ (q₂ ∉∪ q₂' ∉∪ q₂'') h₀ h₁) =
  𝛌Cong{x = x'}
    (rnJg p q₀)
    (subst₃ (λ c c' C → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ c ＝ c' ∶ C ∶ l')
      (rnUpdate⟨⟩ ρ x x' b q₂')
      (rnUpdate⟨⟩ ρ x x' b' q₂'')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnJg (liftRn p h₀ (rnJg p h₀)) q₁))
    x'#
    (rnJg p h₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ B' ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnJg (liftRn p h₀ (rnJg p h₀)) h₁))
  where
  S = supp ((ρ * B , ρ * b , ρ * b') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg{ρ}{Γ' = Γ'} p (∙Cong{l}{l'}{A}{A'}{B}{B'}{a}{a'}{b}{b'}{x}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') h₀ h₁)
  rewrite rn⟨⟩ ρ B a =
  -- helper hypotheses used
  ∙Cong{x = x'}
    (rnJg p q₀)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₄)
      (rnUpdate⟨⟩ ρ x x' B' q₄')
      (rnJg (liftRn p h₀ (rnJg p h₀)) q₁))
    (rnJg p q₂)
    (rnJg p q₃)
    x'#
    (rnJg p h₀)
    (subst (λ C → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ C ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₄)
      (rnJg (liftRn p h₀ (rnJg p h₀)) h₁))
  where
  S = supp ((ρ * B , ρ * B') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg p (𝐈𝐝Cong q₀ q₁ q₂) = 𝐈𝐝Cong
  (rnJg p q₀)
  (rnJg p q₁)
  (rnJg p q₂)

rnJg p (𝐫𝐞𝐟𝐥Cong q₀ q₁) = 𝐫𝐞𝐟𝐥Cong
  (rnJg p q₀)
  (rnJg p q₁)

rnJg{ρ}{Γ' = Γ'} p (𝐉Cong{l}{l'}{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}{x}{y}
  q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') h₀ h₁)
  rewrite rn⟨⟩² ρ C b e =
  -- helper hypotheses used
  𝐉Cong{x = x'}{y'}
    q₀'
    (rnJg p q₁)
    (rnJg p q₂)
    q₃'
    (rnJg p q₄)
    x'#
    y'#
    (rnJg p h₀)
    h₁'
  where
  S = supp ((ρ * C , ρ * C') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((ρ * C , ρ * C') , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  q₃' : Γ' ⊢ ρ * c ＝ ρ * c' ∶ (ρ * C) ⟨ ρ * a ⸴ 𝐫𝐞𝐟𝐥 (ρ * a) ⟩ ∶ l'
  q₃' = subst (λ C' → Γ' ⊢ ρ * c ＝ ρ * c' ∶ C' ∶ l')
    (rn⟨⟩² ρ C a (𝐫𝐞𝐟𝐥 a))
    (rnJg p q₃)

  eq : (x := x')ρ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x')
  eq rewrite  updateFreshRn ρ x x' A (∉∪₂ (∉∪₂ (⊢# q₁ it)))
     | updateFreshRn ρ x x' a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = ρ}{x'} x = refl

  h₁' : (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ I ∶𝐔 l)
    eq
    (rnJg (liftRn p h₀ (rnJg p h₀)) h₁)

  eq' : (y := y')((x := x')ρ) * C ⟨ x ⸴ y ⟩ ≡
        (ρ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) C (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' C q₆
      | updateFreshRn ρ x x' C q₅
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq'' : (y := y')((x := x')ρ) * C' ⟨ x ⸴ y ⟩ ≡
        (ρ * C')⟨ x' ⸴ y' ⟩
  eq'' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) C' (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' C' q₆'
      | updateFreshRn ρ x x' C' q₅'
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  q₀' : (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢
    (ρ * C) ⟨ x' ⸴ y' ⟩ ＝ (ρ * C') ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst₂ (λ D D' →
    (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢ D ＝ D' ∶𝐔 l')
    eq'
    eq''
    (rnJg (liftRn² p h₀ h₁ refl eq (rnJg p h₀) h₁') q₀)

rnJg p (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (rnJg p q)

rnJg{ρ}{Γ' = Γ'} p (𝐧𝐫𝐞𝐜Cong{l}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') h)
  rewrite rn⟨⟩ ρ C a =
  -- helper hypotheses used
  𝐧𝐫𝐞𝐜Cong{x = x'}{y'}
    q₀'
    q₁'
    q₂'
    (rnJg p q₃)
    x'#
    y'#
    h'
  where
  S = supp ((ρ * C , ρ * C' , ρ * c₊ , ρ * c₊') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((ρ * c₊ , ρ * c₊') , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  y#C : y # C
  y#C = ⊆∉ (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨) (∉∪₁ it)

  eq : (x := x')ρ * C ⟨ x ⟩ ≡ (ρ * C)⟨ x' ⟩
  eq rewrite rn⟨⟩ ((x := x')ρ) C (𝐯 x)
     | updateFreshRn ρ x x' C q₄
     | :=Eq{f = ρ}{x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (ρ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (rnJg (liftRn p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (⊢𝐍𝐚𝐭 (okRn p))) h)

  eq' : (x := x')ρ * C' ⟨ x ⟩ ≡ (ρ * C')⟨ x' ⟩
  eq' rewrite rn⟨⟩ ((x := x')ρ) C' (𝐯 x)
     | updateFreshRn ρ x x' C' q₄'
     | :=Eq{f = ρ}{x'} x = refl

  q₀' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (ρ * C) ⟨ x' ⟩ ＝ (ρ * C') ⟨ x' ⟩ ∶𝐔 l
  q₀' = subst₂ (λ D D' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ D ＝ D' ∶𝐔 l)
    eq
    eq'
    (rnJg (liftRn p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (⊢𝐍𝐚𝐭 (okRn p))) q₀)

  q₁' :  Γ' ⊢ ρ * c₀ ＝ ρ * c₀' ∶ (ρ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₁' = subst (λ D → Γ' ⊢ ρ * c₀ ＝ ρ * c₀' ∶ D ∶ l)
    (rn⟨⟩ ρ C 𝐳𝐞𝐫𝐨)
    (rnJg p q₁)

  eq₊ : (y := y')((x := x')ρ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (ρ * c₊)⟨ x' ⸴ y' ⟩
  eq₊ rewrite rn⟨⟩² ((y := y')((x := x')ρ)) c₊ (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' c₊ q₅
      | updateFreshRn ρ x x' c₊ q₄''
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq₊' : (y := y')((x := x')ρ) * c₊' ⟨ x ⸴ y ⟩ ≡
        (ρ * c₊')⟨ x' ⸴ y' ⟩
  eq₊' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) c₊' (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' c₊' q₅'
      | updateFreshRn ρ x x' c₊' q₄'''
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq'' : (y := y')((x := x')ρ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (ρ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite rn⟨⟩ ((y := y')((x := x')ρ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFreshRn ((x := x')ρ) y y' C y#C
       | updateFreshRn ρ x x' C q₄
       | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = ρ}{x'} x = refl

  q₂' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C)⟨ x' ⟩ ∶ l) ⊢
      (ρ * c₊)⟨ x' ⸴ y' ⟩ ＝ (ρ * c₊')⟨ x' ⸴ y' ⟩ ∶ (ρ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₂' = subst₃ (λ d d' D →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C) ⟨ x' ⟩ ∶ l) ⊢ d ＝ d' ∶ D ∶ l)
      eq₊
      eq₊'
      eq''
      (rnJg
        (liftRn² p (⊢𝐍𝐚𝐭 (⊢ok q₃)) h refl eq
          (⊢𝐍𝐚𝐭(okRn p)) h')
        q₂)

rnJg{ρ}{Γ' = Γ'} p (𝚷Beta{l}{l'}{A}{a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁)
  rewrite rn⟨⟩ ρ b a
  | rn⟨⟩ ρ B a =
  -- helper hypotheses used
  𝚷Beta{x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ b' ∶ B' ∶ l')
      (rnUpdate⟨⟩ ρ x x' b q₂')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnJg (liftRn p h₀ (rnJg p h₀)) q₀))
    (rnJg p q₁)
    x'#
    (rnJg p h₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ B' ∶𝐔 l')
      (rnUpdate⟨⟩ ρ x x' B q₂)
      (rnJg (liftRn p h₀ (rnJg p h₀)) h₁))
  where
  S = supp ((ρ * B , ρ * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

rnJg{ρ}{Γ' = Γ'} p (𝐈𝐝Beta{l}{l'}{A}{C}{a}{c}{x}{y}
  q₀ q₁ q₂ q₃ q₄ h₀ h₁)
  rewrite rn⟨⟩² ρ C a (𝐫𝐞𝐟𝐥 a) =
     -- helper hypotheses used
  𝐈𝐝Beta{x = x'} {y'}
    q₀'
    (rnJg p q₁)
    q₂'
    x'#
    y'#
    (rnJg p h₀)
    h₁'
  where
  S = supp (ρ * C , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (ρ * C , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  eq : (x := x')ρ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x')
  eq rewrite  updateFreshRn ρ x x' A (∉∪₂ (⊢# q₁ it))
     | updateFreshRn ρ x x' a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = ρ}{x'} x = refl

  h₁' : (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ I ∶𝐔 l)
    eq
    (rnJg (liftRn p h₀ (rnJg p h₀)) h₁)

  eq' : (y := y')((x := x')ρ) * C ⟨ x ⸴ y ⟩ ≡
        (ρ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) C (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' C q₄
      | updateFreshRn ρ x x' C q₃
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  q₀' : (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢
    (ρ * C) ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst (λ D →
    (Γ' ⸴ x' ∶ ρ * A ∶ l ⸴ y' ∶ 𝐈𝐝(ρ * A)(ρ * a)(𝐯 x') ∶ l) ⊢ D ∶𝐔 l')
    eq'
    (rnJg (liftRn² p h₀ h₁ refl eq (rnJg p h₀) h₁') q₀)

  q₂' : Γ' ⊢ ρ * c ∶ (ρ * C) ⟨ ρ * a ⸴ 𝐫𝐞𝐟𝐥 (ρ * a) ⟩ ∶ l'
  q₂' = subst (λ D → Γ' ⊢ ρ * c ∶ D ∶ l')
    (rn⟨⟩² ρ C a (𝐫𝐞𝐟𝐥 a))
    (rnJg p q₂)

rnJg{ρ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₀{l}{C}{c₀}{c₊}{x}{y} q₀ q₁ (q₂ ∉∪ q₂') q₃ h)
  rewrite rn⟨⟩ ρ C 𝐳𝐞𝐫𝐨 =
  -- helper hypotheses used
  𝐍𝐚𝐭Beta₀{x = x'}{y'} q₀' q₁' x'# y'# h'
  where
  S = supp ((ρ * C , ρ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (ρ * c₊ , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ (⟨⟩supp C 𝐳𝐞𝐫𝐨)) (∉∪₁ it)

  q₀' :  Γ' ⊢ ρ * c₀ ∶ (ρ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ ρ * c₀ ∶ C' ∶ l)
    (rn⟨⟩ ρ C 𝐳𝐞𝐫𝐨)
    (rnJg p q₀)

  eq : (x := x')ρ * C ⟨ x ⟩ ≡ (ρ * C)⟨ x' ⟩
  eq rewrite rn⟨⟩ ((x := x')ρ) C (𝐯 x)
     | updateFreshRn ρ x x' C q₂
     | :=Eq{f = ρ}{x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (ρ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (rnJg (liftRn p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okRn p))) h)

  eq' : (y := y')((x := x')ρ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (ρ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) c₊ (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' c₊ q₃
      | updateFreshRn ρ x x' c₊ q₂'
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq'' : (y := y')((x := x')ρ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (ρ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite rn⟨⟩ ((y := y')((x := x')ρ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFreshRn ((x := x')ρ) y y' C y#C
       | updateFreshRn ρ x x' C q₂
       | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = ρ}{x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C)⟨ x' ⟩ ∶ l) ⊢
      (ρ * c₊)⟨ x' ⸴ y' ⟩ ∶ (ρ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (rnJg
        (liftRn² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okRn p)) h')
        q₁)

rnJg{ρ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₊{l}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
  rewrite rn⟨⟩² ρ c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a)
  | rn⟨⟩ ρ C (𝐬𝐮𝐜𝐜 a) =
  -- helper hypotheses used
  𝐍𝐚𝐭Beta₊{x = x'}{y'} q₀' q₁' (rnJg p q₂) x'# y'# h'
  where
  S = supp ((ρ * C , ρ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (ρ * c₊ , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  y#C : y # C
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ (⟨⟩supp C 𝐳𝐞𝐫𝐨)) (∉∪₁ it)

  q₀' :  Γ' ⊢ ρ * c₀ ∶ (ρ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ ρ * c₀ ∶ C' ∶ l)
    (rn⟨⟩ ρ C 𝐳𝐞𝐫𝐨)
    (rnJg p q₀)

  eq : (x := x')ρ * C ⟨ x ⟩ ≡ (ρ * C)⟨ x' ⟩
  eq rewrite rn⟨⟩ ((x := x')ρ) C (𝐯 x)
     | updateFreshRn ρ x x' C q₃
     | :=Eq{f = ρ}{x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ) ⊢ (ρ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (rnJg (liftRn p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okRn p))) h)

  eq' : (y := y')((x := x')ρ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (ρ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite rn⟨⟩² ((y := y')((x := x')ρ)) c₊ (𝐯 x) (𝐯 y)
      | updateFreshRn ((x := x')ρ) y y' c₊ q₄
      | updateFreshRn ρ x x' c₊ q₃'
      | :=Eq{f = (x := x')ρ}{y'} y
      | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = ρ}{x'} x = refl

  eq'' : (y := y')((x := x')ρ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (ρ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite rn⟨⟩ ((y := y')((x := x')ρ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFreshRn ((x := x')ρ) y y' C y#C
       | updateFreshRn ρ x x' C q₃
       | :=Neq{f = (x := x')ρ}{y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = ρ}{x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C)⟨ x' ⟩ ∶ l) ⊢
      (ρ * c₊)⟨ x' ⸴ y' ⟩ ∶ (ρ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (ρ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (rnJg
        (liftRn² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okRn p)) h')
        q₁)

rnJg{ρ}{Γ' = Γ'} p (𝚷Eta{l}{l'}{A}{B}{b}{x} q₀ q₁ h) =
  -- helper hypothesis used
  subst (λ b' → Γ' ⊢ ρ * b ＝ b' ∶ 𝚷 (ρ * A) (ρ * B) ∶ max l l')
    eq
    (𝚷Eta{x = x'}
      (rnJg p q₀)
      (subst (λ B' → (Γ' ⸴ x' ∶ ρ * A ∶ l) ⊢ B' ∶𝐔 l')
        (rnUpdate⟨⟩ ρ x x' B (⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) it))
        (rnJg (liftRn p h (rnJg p h)) q₁))
      (rnJg p h))
  where
  S = supp ((ρ * B , ρ * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

  x#b : x # b
  x#b = ∉∪₁ (⊢# q₀ it)

  x#A : x # A
  x#A = ∉∪₁ (∉∪₂ (⊢# q₀ it))

  x#B : x # B
  x#B = ∉∪₁ (∉∪₂ (∉∪₂ (⊢# q₀ it)))

  f :
    (y : ℕ)
    (_ : y ∈ supp (b ∙[ A , B ] 𝐯 x))
    (_ : ¬ (x ≡ y))
    → -------------------------------
    ¬ (x' ≡ ρ y)
  f y (∈∪₁ y∈b) _ xx = ∉→¬∈ x'#Γ'
    (subst (_∈ dom Γ') (symm xx) (rnDom p (⊢supp q₀ (∈∪₁ y∈b))))
  f y (∈∪₂ (∈∪₁ y∈A)) _ xx = ∉→¬∈ x'#Γ'
    (subst (_∈ dom Γ') (symm xx) (rnDom p (⊢supp q₀ (∈∪₂ (∈∪₁ y∈A)))))
  f y (∈∪₂ (∈∪₂ (∈∪₁ y∈B))) _ xx = ∉→¬∈ x'#Γ'
    (subst (_∈ dom Γ') (symm xx) (rnDom p (⊢supp q₀ (∈∪₂ (∈∪₂ (∈∪₁ y∈B))))))
  f y (∈∪₂ (∈∪₂ (∈∪₂ (∈∪₁ ∈｛｝)))) ¬xy _ = ¬xy refl

  eq : 𝛌 (ρ * A)(x' ． (ρ * b) ∙[ ρ * A , ρ * B ] 𝐯 x') ≡
    ρ * 𝛌 A (x ． b ∙[ A , B ] 𝐯 x)
  eq rewrite rnAbs ρ x x' (b ∙[ A , B ] 𝐯 x) f
     | updateFreshRn ρ x x' b x#b
     | updateFreshRn ρ x x' A x#A
     | updateFreshRn ρ x x' B x#B
     | :=Eq{f = ρ}{x'} x = refl

----------------------------------------------------------------------
-- Renaming type abstractions
----------------------------------------------------------------------
rnTm¹ :
  {x x' : 𝔸}
  {Γ : Cx}
  {l l' : Lvl}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
  (_ : x # (B , b))
  → --------------------------------------------
  (Γ ⸴ x' ∶ A ∶ l) ⊢ b ⟨ x' ⟩ ∶ B ⟨ x' ⟩ ∶ l'

rnTm¹{x}{x'}{Γ}{l}{l'}{A}{B}{b}  q (x#B ∉∪ x#b) =
  subst₂ (λ b' B' → (Γ ⸴ x' ∶ A ∶ l) ⊢ b' ∶ B' ∶ l')
    (srn⟨⟩ x x' b x#b)
    (srn⟨⟩ x x' B x#B)
    (rnJg p q)
  where
  Γok : Ok Γ
  Γok = π₂ (∷⁻¹ q)

  ⊢A : Γ ⊢ A ∶𝐔 l
  ⊢A = π₁ (∷⁻¹ q)

  e : ((x := x')id x , (x := x')id * A , l) isIn (Γ ⸴ x' ∶ A ∶ l)
  e rewrite  :=Eq{f = id}{x'} x
    | updateFreshRn id x x' A (∉∪₁ (⊆∉ (⊢supp ⊢A) it))
    | rnUnit A = isInNew refl

  p : (Γ ⸴ x' ∶ A ∶ l) ⊢ʳ (x := x')id ∶ (Γ ⸴ x ∶ A ∶ l)
  p = ∷ (rnExt (wkRn x' ⊢A (⊢id Γok)) λ y r →
     symm (:=Neq{f = id} x y λ{refl → ∉→¬∈ it r})) ⊢A e

rnTy¹ :
  {l l' : Lvl}
  {x x' : 𝔸}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ⟨ x ⟩ ∶𝐔 l')
  (_ : x # B)
  → ---------------------------------
  (Γ ⸴ x' ∶ A ∶ l) ⊢ B ⟨ x' ⟩ ∶𝐔 l'

rnTy¹{l' = l'}{B = B} q q' = rnTm¹{B = 𝐔 l'}{B} q (∉∅ ∉∪ q')

----------------------------------------------------------------------
-- Weakening provable judgements
----------------------------------------------------------------------
wkJg :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {J : Jg}
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ∶𝐔 l)
  (_ : Γ ⊢ J)
  → ---------------
  Γ ⸴ x ∶ A ∶ l ⊢ J

wkJg{l}{Γ}{A}{J} x q q' = subst (λ J' → Γ ⸴ x ∶ A ∶ l ⊢ J')
  (rnUnitJg J)
  (rnJg (wkRn x q (⊢id (⊢ok q))) q')

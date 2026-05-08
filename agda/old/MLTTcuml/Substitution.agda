module MLTTcuml.Substitution where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTTcuml.Syntax
open import MLTTcuml.Judgement
open import MLTTcuml.TypeSystem
open import MLTTcuml.ContextConversion
open import MLTTcuml.Ok
open import MLTTcuml.WellScoped
open import MLTTcuml.Renaming

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Well-typed substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢ_∶_
data _⊢ˢ_∶_ (Γ' : Cx) : Sb → Cx → Set where
  ◇ :
    {σ : Sb}
    (q : Ok Γ')
    → ---------
    Γ' ⊢ˢ σ ∶ ◇
  ∷ :
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ∶ Γ)
    (q₁ : Γ ⊢ A ty)
    (q₂ : Γ' ⊢ σ x ∶ σ * A)
    → ---------------------
    Γ' ⊢ˢ σ ∶ (Γ ⸴ x ∶ A)

----------------------------------------------------------------------
-- Convertible well-typed substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢ_＝_∶_
data _⊢ˢ_＝_∶_ (Γ' : Cx) : Sb → Sb → Cx → Set where
  ◇ :
    {σ σ' : Sb}
    (q : Ok Γ')
    → ---------------
    Γ' ⊢ˢ σ ＝ σ' ∶ ◇
  ∷ :
    {Γ : Cx}
    {σ σ' : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
    (q₁ : Γ ⊢ A ty)
    (q₂ : Γ' ⊢ σ x ＝ σ' x ∶ σ * A)
    → -----------------------------
    Γ' ⊢ˢ σ ＝ σ' ∶ (Γ ⸴ x ∶ A)

----------------------------------------------------------------------
-- Well-formedness
----------------------------------------------------------------------
sbOk :
  {Γ' Γ : Cx}
  {σ : Sb}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  Ok Γ

sbOk (◇ _) = ◇
sbOk (∷ q q' _) = ∷ q' (sbOk q)

okSb :
  {Γ' Γ : Cx}
  {σ : Sb}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  Ok Γ'

okSb (◇ q) = q
okSb (∷ q _ _) = okSb q

sb＝Ok :
  {Γ' Γ : Cx}
  {σ σ' : Sb}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → --------------------
  Ok Γ

sb＝Ok (◇ _) = ◇
sb＝Ok (∷ q q' _) = ∷ q' (sb＝Ok q)

okSb＝ :
  {Γ' Γ : Cx}
  {σ σ' : Sb}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → --------------------
  Ok Γ'

okSb＝ (◇ q) = q
okSb＝ (∷ q _ _) = okSb＝ q

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wkSb :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  (x : 𝔸)
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ A ty)
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -----------------
  Γ' ⸴ x ∶ A ⊢ˢ σ ∶ Γ

wkSb x q (◇ q') = ◇ (∷ q q')
wkSb x q (∷ q₀ q₁ q₂) = ∷ (wkSb x q q₀) q₁ (wkJg x q q₂)

wk＝Sb :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  (x : 𝔸)
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ A ty)
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → -----------------------
  Γ' ⸴ x ∶ A ⊢ˢ σ ＝ σ' ∶ Γ

wk＝Sb x q (◇ q') = ◇ (∷ q q')
wk＝Sb x q (∷ q₀ q₁ q₂) = ∷ (wk＝Sb x q q₀) q₁ (wkJg x q q₂)

----------------------------------------------------------------------
-- Identity substitution is well-typed
----------------------------------------------------------------------
⊢ι :
  {Γ : Cx}
  (_ : Ok Γ)
  → ---------
  Γ ⊢ˢ ι ∶ Γ

⊢ι ◇ = ◇ ◇
⊢ι (∷ q q') = ∷
  (wkSb _ q (⊢ι q'))
  q
  (⊢𝐯 (∷ q q') (isInNew (cong (_ ,_) (symm (sbUnit _)))))

----------------------------------------------------------------------
-- Extensionality properties of well-typed substitutions
----------------------------------------------------------------------
sbExt :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : ∀ x → x ∈ dom Γ → σ x ≡ σ' x)
  → --------------------------------
  Γ' ⊢ˢ σ' ∶ Γ

sbExt (◇ q) _ = ◇ q
sbExt{σ}{σ'} (∷{A = A}{x} q q₁ q₂) e
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ p')))
  | e x (∈∪₂ ∈｛｝) = ∷ (sbExt q (λ y r → e y (∈∪₁ r))) q₁ q₂

sb＝Ext :
  {σ' τ' σ τ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ＝ τ ∶ Γ)
  (_ : ∀ x → x ∈ dom Γ → σ x ≡ σ' x)
  (_ : ∀ x → x ∈ dom Γ → τ x ≡ τ' x)
  → --------------------------------
  Γ' ⊢ˢ σ' ＝ τ' ∶ Γ

sb＝Ext (◇ q) _ _ = ◇ q
sb＝Ext{σ'}{τ'} (∷{σ = σ}{τ}{A = A}{x} q q₁ q₂) e e'
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ p')))
  | e x (∈∪₂ ∈｛｝)
  | e' x (∈∪₂ ∈｛｝)= ∷
    (sb＝Ext q (λ y r → e y (∈∪₁ r)) (λ y' r' → e' y' (∈∪₁ r')))
    q₁
    q₂

----------------------------------------------------------------------
-- Lifting substitutions
----------------------------------------------------------------------
liftSb :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ty)
  -- helper hypothesis
  (_ : Γ' ⊢ σ * A ty)
  → -------------------------------------------
  Γ' ⸴ x' ∶ σ * A ⊢ˢ (x := 𝐯 x')σ ∶ (Γ ⸴ x ∶ A)

liftSb{σ}{Γ}{Γ'}{A}{x}{x'} ⊢σ ⊢A ⊢σA = ∷ (wkSb x' ⊢σA ⊢σ') ⊢A ⊢A'
  where
  ⊢σ' : Γ' ⊢ˢ (x := 𝐯 x')σ ∶ Γ
  ⊢σ' = sbExt ⊢σ (λ y r → symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))

  ⊢A' : (Γ' ⸴ x' ∶ σ * A) ⊢ (x := 𝐯 x')σ x ∶ (x := 𝐯 x')σ * A
  ⊢A' rewrite updateFresh σ x (𝐯 x') A (⊢# ⊢A it)
      | :=Eq{f = σ}{𝐯 x'} x = ⊢𝐯 (∷ ⊢σA (⊢ok ⊢σA)) (isInNew refl)

-- Iterated lifting
liftSb² :
  {x y x' y' : 𝔸}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  ⦃ _ : y # (Γ , x) ⦄
  ⦃ _ : y' # (Γ' , x') ⦄
  (p : Γ' ⊢ˢ σ ∶ Γ)
  (p₁ : Γ ⊢ A ty)
  (p₂ : Γ ⸴ x ∶ A ⊢ B ty)
  (p₃ : σ * A ≡ A')
  (p₄ : (x := 𝐯 x')σ * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ A' ty)
  (h' : Γ' ⸴ x' ∶ A' ⊢ B' ty)
  → -----------------------------------------------
  (Γ' ⸴ x' ∶ A' ⸴ y' ∶ B') ⊢ˢ
    (y := 𝐯 y')((x := 𝐯 x')σ) ∶ (Γ ⸴ x ∶ A ⸴ y ∶ B)

liftSb² p p₁ p₂ refl refl h h' = liftSb (liftSb p p₁ h) p₂ h'

----------------------------------------------------------------------
-- Types of variables under substitution
----------------------------------------------------------------------
sbVar :
  {σ : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : (x , A) isIn Γ)
  → ------------------
  Γ' ⊢ σ x ∶ σ * A

sbVar (∷ _ _ q)  (isInNew refl)  = q
sbVar (∷ q' _ _) (isInOld q)  = sbVar q' q

sbVar＝ :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_  : (x , A) isIn Γ)
  → -----------------------
  Γ' ⊢ σ x ＝ σ' x ∶ σ * A

sbVar＝ (∷ _ _ q) (isInNew refl) = q
sbVar＝ (∷ q' _ _) (isInOld q) = sbVar＝ q' q

sbDom :
  {σ : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : x ∈ dom Γ)
  → ----------------
  supp (σ x) ⊆ dom Γ'

sbDom p q =
  let (_ , q') = dom→isIn q
  in ⊢supp (sbVar p q') ∘ ∈∪₁

----------------------------------------------------------------------
-- Substitution preserves provable judgements
----------------------------------------------------------------------
sbJg :
  {σ : Sb}
  {Γ Γ' : Cx}
  {J : Jg}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ J)
  → ---------------
  Γ' ⊢ σ * J

sbJg{σ}{Γ' = Γ'} p (⊢𝚷ty{A}{B}{x} q₀ q₁ h) =
  -- helper hypothesis used
  ⊢𝚷ty{x = x'}
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb p h (sbJg p h)) q₀))
  x'#
  (sbJg p h)
  where
  S = supp (σ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg p (⊢𝐈𝐝ty q₀ q₁ q₂) =  ⊢𝐈𝐝ty
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (⊢𝐔 q) = ⊢𝐔 (okSb p)

sbJg p (⊢𝐄𝐥 q) =  ⊢𝐄𝐥 (sbJg p q)

sbJg p (TyRefl q) = TyRefl (sbJg p q)

sbJg p (TySymm q) = TySymm (sbJg p q)

sbJg p (TyTrans q₀ q₁) = TyTrans
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (𝚷TyCong{A}{B = B}{B'}{x} q₀ q₁ (q₂ ∉∪ q₂') h) =
  -- helper hypothesis used
  𝚷TyCong{x = x'}
    (sbJg p q₀)
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbUpdate⟨⟩ σ x (𝐯 x') B' q₂')
      (sbJg (liftSb p h (sbJg p h)) q₁))
  x'#
  (sbJg p h)
  where
  S = supp ((σ * B , σ * B') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg p (𝐈𝐝TyCong q₀ q₁ q₂) = 𝐈𝐝TyCong
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (＝𝐄𝐥 q) = ＝𝐄𝐥 (sbJg p q)

sbJg{σ} p (⊢𝐯{x = x} _ q) rewrite ‿unit (σ x) ⦃ it ⦄ = sbVar p q

sbJg p (⊢conv q₀ q₁) = ⊢conv
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (⊢𝚷{A}{B}{x} q₀ q₁ q₂) =
  ⊢𝚷 {x = x'}
    (sbJg p q₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A) ⊢ B' ∶ 𝐔)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p (⊢𝐄𝐥 q₀) (⊢𝐄𝐥 (sbJg p q₀))) q₁))
    x'#
  where
  S = supp (σ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (⊢𝛌{A}{B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) =
  -- helper hypothesis used
  ⊢𝛌 {x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ σ * A) ⊢ b' ∶ B')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₀))
    x'#
    (sbJg p h₀)
    (subst (λ C → Γ' ⸴ x' ∶ σ * A ⊢ C ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb p h₀ (sbJg p h₀)) h₁))
  where
  S = supp ((σ * B , σ * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (⊢∙{A}{B}{a}{b}{x} q₀ q₁ q₂ q₃ h)
  rewrite sb⟨⟩ σ B a =
  -- helper hypothesis used
  ⊢∙
    (sbJg p q₀)
    (sbJg p q₁)
    (subst (λ C → Γ' ⸴ x' ∶ σ * A ⊢ C ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₃)
      (sbJg (liftSb p h (sbJg p h)) q₂))
    x'#
    (sbJg p h)
  where
  S = supp (σ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg p (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢𝐈𝐝
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (⊢𝐫𝐞𝐟𝐥 q₀ q₁) = ⊢𝐫𝐞𝐟𝐥
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (⊢𝐉{A}{C}{a}{b}{c}{e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁)
  -- with (x' , x'# ∉∪ x'#Γ') ← fresh (σ * C , Γ')
  -- with (y' , y'# ∉∪ y'#Γ' ∉∪ y'#x') ← fresh (σ * C , Γ' , x')
  rewrite sb⟨⟩² σ C b e =
  -- helper hypotheses used
  ⊢𝐉{x = x'}{y'}
    q₀'
    (sbJg p q₁)
    (sbJg p q₂)
    q₃'
    (sbJg p q₄)
    x'#
    y'#
    (sbJg p h₀)
    h₁'
  where
  S = supp (σ * C , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (σ * C , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  q₃' : Γ' ⊢ σ * c ∶ (σ * C) ⟨ σ * a ⸴ 𝐫𝐞𝐟𝐥 (σ * a) ⟩
  q₃' = subst (λ C' → Γ' ⊢ σ * c ∶ C')
    (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₃)

  eq : (x := (𝐯 x'))σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (⊢# q₁ it))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h₁' : Γ' ⸴ x' ∶ σ * A ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ty
  h₁' = subst (λ C' → Γ' ⸴ x' ∶ σ * A ⊢ C' ty)
    eq
    (sbJg (liftSb p h₀ (sbJg p h₀)) h₁)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ x ⸴ y ⟩ ≡ (σ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C q₆
      | updateFresh σ x (𝐯 x') C q₅
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' : Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ty
  q₀' = subst (λ C →
    Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢ C ty)
    eq'
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

sbJg p (⊢𝐍𝐚𝐭 _) = ⊢𝐍𝐚𝐭 (okSb p)

sbJg p (⊢𝐳𝐞𝐫𝐨 _) = ⊢𝐳𝐞𝐫𝐨 (okSb p)

sbJg p (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (sbJg p q)

sbJg{σ}{Γ' = Γ'} p (⊢𝐧𝐫𝐞𝐜{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
  rewrite sb⟨⟩ σ C a =
  -- helper hypotheses used
  ⊢𝐧𝐫𝐞𝐜{x = x'}{y'}
    q₀'
    q₁'
    (sbJg p q₂)
    x'#
    y'#
    h'
  where
  S = supp ((σ * C , σ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (σ * c₊ , Γ' , x')
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C')
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := (𝐯 x'))σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₃
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ty
  h' = subst (λ C' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ C' ty)
    eq
    (sbJg (liftSb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb p)))) h)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (σ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') c₊ q₄
      | updateFresh σ x (𝐯 x') c₊ q₃'
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (σ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite sb⟨⟩ ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C y#C
       | updateFresh σ x (𝐯 x') C q₃
       | :=Neq{f = (x := (𝐯 x'))σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = σ}{𝐯 x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C)⟨ x' ⟩) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C) ⟨ x' ⟩) ⊢ c' ∶ C')
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) h refl eq
          (⊢𝐄𝐥 (⊢𝐍𝐚𝐭(okSb p))) h')
        q₁)

sbJg p (TmRefl q) = TmRefl (sbJg p q)

sbJg p (TmSymm q) = TmSymm (sbJg p q)

sbJg p (TmTrans q₀ q₁) = TmTrans
  (sbJg p q₀)
  (sbJg p q₁)

sbJg p (＝conv q₀ q₁) = ＝conv
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (𝚷TmCong{A}{A'}{B}{B'}{x} q₀ q₁ (q₂ ∉∪ q₂') h) =
  -- helper hypothesis used
  𝚷TmCong{x = x'}
    (sbJg p q₀)
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ∶ 𝐔)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbUpdate⟨⟩ σ x (𝐯 x') B' q₂')
      (sbJg (liftSb p (⊢𝐄𝐥 h) (⊢𝐄𝐥 (sbJg p h))) q₁))
    x'#
    (sbJg p h)
  where
  S = supp ((σ * B , σ * B') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (𝛌Cong{A}{B = B}{b}{b'}{x} q₀ q₁ (q₂ ∉∪ q₂' ∉∪ q₂'') h₀ h₁) =
  -- helper hypotheses used
  𝛌Cong{x = x'}
    (sbJg p q₀)
    (subst₃ (λ c c' C → (Γ' ⸴ x' ∶ σ * A) ⊢ c ＝ c' ∶ C)
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₂')
      (sbUpdate⟨⟩ σ x (𝐯 x') b' q₂'')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₁))
    x'#
    (sbJg p h₀)
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) h₁))
  where
  S = supp ((σ * B , σ * b , σ * b') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (∙Cong{A}{A'}{B}{B'}{a}{a'}{b}{b'}{x}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') h₀ h₁)
  rewrite sb⟨⟩ σ B a =
  -- helper hypotheses used
  ∙Cong{x = x'}
    (sbJg p q₀)
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₄)
      (sbUpdate⟨⟩ σ x (𝐯 x') B' q₄')
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₁))
    (sbJg p q₂)
    (sbJg p q₃)
    x'#
    (sbJg p h₀)
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₄)
      (sbJg (liftSb p h₀ (sbJg p h₀)) h₁))
  where
  S = supp ((σ * B , σ * B') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg p (𝐈𝐝TmCong q₀ q₁ q₂) = 𝐈𝐝TmCong
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (𝐫𝐞𝐟𝐥Cong q₀ q₁) = 𝐫𝐞𝐟𝐥Cong
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (𝐉Cong{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}{x}{y}
  q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') h₀ h₁)
  rewrite sb⟨⟩² σ C b e =
  -- helper hypotheses used
  𝐉Cong{x = x'}{y'}
    q₀'
    (sbJg p q₁)
    (sbJg p q₂)
    (subst (λ C' → Γ' ⊢ σ * c ＝ σ * c' ∶ C')
      (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
      (sbJg p q₃))
    (sbJg p q₄)
    x'#
    y'#
    (sbJg p h₀)
    h₁'
  where
  S = supp ((σ * C , σ * C') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((σ * C , σ * C') , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  eq : (x := (𝐯 x'))σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (∉∪₂ (⊢# q₁ it)))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{(𝐯 x')} x = refl

  h₁' : Γ' ⸴ x' ∶ σ * A ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ty
  h₁' = subst (λ C' → Γ' ⸴ x' ∶ σ * A ⊢ C' ty)
    eq
    (sbJg (liftSb p h₀ (sbJg p h₀)) h₁)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ x ⸴ y ⟩ ≡
        (σ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C q₆
      | updateFresh σ x (𝐯 x') C q₅
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C' ⟨ x ⸴ y ⟩ ≡
        (σ * C')⟨ x' ⸴ y' ⟩
  eq'' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) C' (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C' q₆'
      | updateFresh σ x (𝐯 x') C' q₅'
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯  y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' : Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ＝ (σ * C') ⟨ x' ⸴ y' ⟩ ty
  q₀' = subst₂ (λ D D' →
    Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢ D ＝ D' ty)
    eq'
    eq''
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

sbJg p (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (sbJg p q)

sbJg{σ}{Γ' = Γ'} p (𝐧𝐫𝐞𝐜Cong{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') h)
  rewrite sb⟨⟩ σ C a =
  -- helper hypotheses used
  𝐧𝐫𝐞𝐜Cong{x = x'}{y'}
    q₀'
    q₁'
    q₂'
    (sbJg p q₃)
    x'#
    y'#
    h'
  where
  S = supp ((σ * C , σ * C' , σ * c₊ , σ * c₊') , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((σ * c₊ , σ * c₊') , Γ' , x')
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

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₄
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ty
  h' = subst (λ C' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ C' ty)
    eq
    (sbJg (liftSb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₃))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb p)))) h)

  eq' : (x := (𝐯 x'))σ * C' ⟨ x ⟩ ≡ (σ * C')⟨ x' ⟩
  eq' rewrite sb⟨⟩ ((x := 𝐯 x')σ) C' (𝐯 x)
     | updateFresh σ x (𝐯 x') C' q₄'
     | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ＝ (σ * C') ⟨ x' ⟩ ty
  q₀' = subst₂ (λ D D' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ D ＝ D' ty)
    eq
    eq'
    (sbJg (liftSb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₃))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb p)))) q₀)

  q₁' :  Γ' ⊢ σ * c₀ ＝ σ * c₀' ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩
  q₁' = subst (λ D → Γ' ⊢ σ * c₀ ＝ σ * c₀' ∶ D)
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₁)

  eq₊ : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (σ * c₊)⟨ x' ⸴ y' ⟩
  eq₊ rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') c₊ q₅
      | updateFresh σ x (𝐯 x') c₊ q₄''
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq₊' : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊' ⟨ x ⸴ y ⟩ ≡
        (σ * c₊')⟨ x' ⸴ y' ⟩
  eq₊' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊' (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') c₊' q₅'
      | updateFresh σ x (𝐯 x') c₊' q₄'''
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (σ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite sb⟨⟩ ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C y#C
       | updateFresh σ x (𝐯 x') C q₄
       | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = σ}{𝐯 x'} x = refl

  q₂' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C)⟨ x' ⟩) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ＝ (σ * c₊')⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  q₂' = subst₃ (λ d d' D →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C) ⟨ x' ⟩) ⊢ d ＝ d' ∶ D)
      eq₊
      eq₊'
      eq''
      (sbJg
        (liftSb² p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₃))) h refl eq
          (⊢𝐄𝐥 (⊢𝐍𝐚𝐭(okSb p))) h')
        q₂)

sbJg{σ}{Γ' = Γ'} p (𝚷Beta{A}{a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁)
  with (x' , x'# ∉∪ x'#Γ') ← fresh ((σ * B , σ * b) , Γ')
  rewrite sb⟨⟩ σ b a
  | sb⟨⟩ σ B a =
  -- helper hypotheses used
    let
    instance
      _ : x' # Γ'
      _ = x'#Γ'
  in  𝚷Beta{x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ σ * A) ⊢ b' ∶ B')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₂')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₀))
    (sbJg p q₁)
    x'#
    (sbJg p h₀)
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) h₁))

sbJg{σ}{Γ' = Γ'} p (𝐈𝐝Beta{A}{C}{a}{c}{x}{y} q₀ q₁ q₂ q₃ q₄ h₀ h₁)
  rewrite sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a) =
  -- helper hypotheses used
  𝐈𝐝Beta{x = x'} {y'}
    q₀'
    (sbJg p q₁)
    q₂'
    x'#
    y'#
    (sbJg p h₀)
    h₁'
  where
  S = supp (σ * C , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (σ * C , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  eq : (x := 𝐯 x')σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (⊢# q₁ it))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h₁' : Γ' ⸴ x' ∶ σ * A ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ty
  h₁' = subst (λ C' → Γ' ⸴ x' ∶ σ * A ⊢ C' ty)
    eq
    (sbJg (liftSb p h₀ (sbJg p h₀)) h₁)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ x ⸴ y ⟩ ≡
        (σ * C)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C q₄
      | updateFresh σ x (𝐯 x') C q₃
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' : Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ty
  q₀' = subst (λ D →
    Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢ D ty)
    eq'
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

  q₂' : Γ' ⊢ σ * c ∶ (σ * C) ⟨ σ * a ⸴ 𝐫𝐞𝐟𝐥 (σ * a) ⟩
  q₂' = subst (λ D → Γ' ⊢ σ * c ∶ D)
    (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₂)

sbJg{σ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₀{C}{c₀}{c₊}{x}{y} q₀ q₁ (q₂ ∉∪ q₂') q₃ h)
  rewrite sb⟨⟩ σ C 𝐳𝐞𝐫𝐨 =
  -- helper hypotheses used
  𝐍𝐚𝐭Beta₀{x = x'}{y'} q₀' q₁' x'# y'# h'
  where
  S = supp ((σ * C , σ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (σ * c₊ , Γ' , x')
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C')
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₂
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ty
  h' = subst (λ C' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ C' ty)
    eq
    (sbJg (liftSb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb p)))) h)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (σ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') c₊ q₃
      | updateFresh σ x (𝐯 x') c₊ q₂'
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (σ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite sb⟨⟩ ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C y#C
       | updateFresh σ x (𝐯 x') C q₂
       | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = σ}{𝐯 x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C)⟨ x' ⟩) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C) ⟨ x' ⟩) ⊢ c' ∶ C')
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) h refl eq
          (⊢𝐄𝐥 (⊢𝐍𝐚𝐭(okSb p))) h')
        q₁)

sbJg{σ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₊{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
  rewrite sb⟨⟩² σ c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a)
  | sb⟨⟩ σ C (𝐬𝐮𝐜𝐜 a) =
  -- helper hypotheses used
  𝐍𝐚𝐭Beta₊{x = x'}{y'} q₀' q₁' (sbJg p q₂) x'# y'# h'
  where
  S = supp ((σ * C , σ * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp (σ * c₊ , Γ' , x')
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C')
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₃
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ty
  h' = subst (λ C' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ C' ty)
    eq
    (sbJg (liftSb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb p)))) h)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (σ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') c₊ q₄
      | updateFresh σ x (𝐯 x') c₊ q₃'
      | :=Eq{f = (x := 𝐯 x')σ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (σ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite sb⟨⟩ ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C y#C
       | updateFresh σ x (𝐯 x') C q₃
       | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = σ}{𝐯 x'} x = refl

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C)⟨ x' ⟩) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C) ⟨ x' ⟩) ⊢ c' ∶ C')
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) h refl eq
          (⊢𝐄𝐥 (⊢𝐍𝐚𝐭(okSb p))) h')
        q₁)

sbJg{σ}{Γ' = Γ'} p (𝚷Eta{A}{B}{b}{x} q₀ q₁ h) =
  -- helper hypothesis used
  subst (λ b' → Γ' ⊢ σ * b ＝ b' ∶ 𝚷 (σ * A) (σ * B))
    eq
    (𝚷Eta{x = x'}
      (sbJg p q₀)
      (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
        (sbUpdate⟨⟩ σ x (𝐯 x') B (⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) it))
        (sbJg (liftSb p h (sbJg p h)) q₁))
      (sbJg p h))
  where
  S = supp ((σ * B , σ * b) , Γ')
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
    x' # σ y
  f y (∈∪₁ y∈b) ¬xy =
    ⊆∉ (sbDom p (⊢supp q₀ (∈∪₁ y∈b))) x'#Γ'
  f y (∈∪₂ (∈∪₁ y∈A)) ¬xy =
    ⊆∉ (sbDom p (⊢supp q₀ (∈∪₂ (∈∪₁ y∈A)))) x'#Γ'
  f y (∈∪₂ (∈∪₂ (∈∪₁ y∈B))) ¬xy =
    ⊆∉ (sbDom p (⊢supp q₀ (∈∪₂ (∈∪₂ (∈∪₁ y∈B))))) x'#Γ'
  f y (∈∪₂ (∈∪₂ (∈∪₂ (∈∪₁ ∈｛｝)))) ¬xy =
    Øelim (¬xy refl)

  eq : 𝛌(σ * A) (x' ． (σ * b) ∙[ σ * A , σ * B ] 𝐯 x') ≡
    σ * 𝛌 A (x ． b ∙[ A , B ] 𝐯 x)
  eq rewrite sbAbs σ x x' (b ∙[ A , B ] 𝐯 x) f
     | updateFresh σ x (𝐯 x') b x#b
     | updateFresh σ x (𝐯 x') A x#A
     | updateFresh σ x (𝐯 x') B x#B
     | :=Eq{f = σ}{(𝐯 x')} x = refl

----------------------------------------------------------------------
-- Conversion for substitutions is reflexive
----------------------------------------------------------------------
sb＝Refl :
  {σ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  Γ' ⊢ˢ σ ＝ σ ∶ Γ

sb＝Refl (◇ q) = ◇ q
sb＝Refl (∷ q₀ q₁ q₂) = ∷ (sb＝Refl q₀) q₁ (TmRefl q₂)

----------------------------------------------------------------------
-- Properties of substitution update
----------------------------------------------------------------------
sbUpdate :
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ty)
  (_ : Γ' ⊢ a ∶ σ * A)
  → ----------------------------
  Γ' ⊢ˢ (x := a) σ ∶ (Γ ⸴ x ∶ A)

sbUpdate{Γ' = Γ'}{σ}{A}{a}{x} ⊢σ ⊢A ⊢a = ∷
  (sbExt ⊢σ (λ y r →
    symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r })))
  ⊢A
  (subst₂ (λ z Z → Γ' ⊢ z ∶ Z)
    (symm (:=Eq{f = σ}{a} x))
    (symm (updateFresh σ x a A (⊢# ⊢A it)))
    ⊢a)

sb＝Update :
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ty)
  (_ : Γ' ⊢ a ＝ a' ∶ σ * A)
  → --------------------------------------------
  Γ' ⊢ˢ (x := a) σ ＝ (x := a') σ' ∶ (Γ ⸴ x ∶ A)

sb＝Update{Γ' = Γ'}{σ}{σ'}{A}{a}{a'}{x} σ=σ' ⊢A a=a' = ∷
  (sb＝Ext σ=σ'
    (λ y r →
      symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))
    (λ y r →
      symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ it r })))
  ⊢A
  (subst₃ (λ z z' Z → Γ' ⊢ z ＝ z' ∶ Z)
    (symm (:=Eq{f = σ}{a} x))
    (symm (:=Eq{f = σ'}{a'} x))
    (symm (updateFresh σ x a A (⊢# ⊢A it)))
    a=a')

ssbUpdate :
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ a ∶ A)
  -- helper hypothesis
  (_ : Γ ⊢ A ty)
  → ------------------------
  Γ ⊢ˢ (x ≔ a) ∶ (Γ ⸴ x ∶ A)

ssbUpdate{Γ}{A}{a} q h = sbUpdate
  (⊢ι (⊢ok q))
  h
  (subst (λ A' → Γ ⊢ a ∶ A') (symm (sbUnit A)) q)

ssb＝Update :
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ a ＝ a' ∶ A)
  -- helper hypothesis
  (_ : Γ ⊢ A ty)
  → ------------------------------------
  Γ ⊢ˢ (x ≔ a) ＝ (x ≔ a') ∶ (Γ ⸴ x ∶ A)

ssb＝Update{Γ}{A}{a}{a'} q h = sb＝Update
  (sb＝Refl (⊢ι (⊢ok q)))
  h
  (subst (λ A' → Γ ⊢ a ＝ a' ∶ A') (symm (sbUnit A)) q)

ssbUpdate² :
  {Γ : Cx}
  {x y : 𝔸}
  {a b : Tm}
  {A B : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ a ∶ A)
  (_ : Γ ⸴ x ∶ A ⊢ B ty)
  (_ : Γ ⊢ b ∶ (x ≔ a) * B)
  → ----------------------------------------
  Γ ⊢ˢ (y := b)(x ≔ a) ∶ (Γ ⸴ x ∶ A ⸴ y ∶ B)

ssbUpdate² q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₁ = sbUpdate (ssbUpdate q₀ ⊢A) q₁ q₂

ssb＝Update² :
  {Γ : Cx}
  {x y : 𝔸}
  {a a' b b' : Tm}
  {A  B : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ a ＝ a' ∶ A)
  (_ : Γ ⸴ x ∶ A ⊢ B ty)
  (_ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B)
  → -------------------------------------------------------------
  Γ ⊢ˢ (y := b)(x ≔ a) ＝ (y := b')(x ≔ a') ∶ (Γ ⸴ x ∶ A ⸴ y ∶ B)

ssb＝Update² q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₁ = sb＝Update (ssb＝Update q₀ ⊢A) q₁ q₂

----------------------------------------------------------------------
-- Lifting substitutions, again
----------------------------------------------------------------------
liftSb⁻ :
  -- liftSb without the helper hypothesis
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ty)
  → -------------------------------------------
  Γ' ⸴ x' ∶ σ * A ⊢ˢ (x := 𝐯 x')σ ∶ (Γ ⸴ x ∶ A)

liftSb⁻ p q = liftSb p q (sbJg p q)

lift＝Sb :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ty)
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ------------------------------------------------------------
  Γ' ⸴ x' ∶ σ * A ⊢ˢ (x := 𝐯 x')σ ＝ (x := 𝐯 x')σ' ∶ (Γ ⸴ x ∶ A)

lift＝Sb{σ}{σ'}{Γ}{Γ'}{A}{x}{x'} p q h =
  ∷ (wk＝Sb x' (sbJg h q) p') q q''
  where
  p' : Γ' ⊢ˢ (x := 𝐯 x') σ ＝ (x := 𝐯 x') σ' ∶ Γ
  p' = sb＝Ext p
    (λ y r → symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))
    λ y r → symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ it r })

  q'' : Γ' ⸴ x' ∶ σ * A ⊢
      (x := 𝐯 x')σ x ＝ (x := 𝐯 x')σ' x ∶ (x := 𝐯 x')σ * A
  q'' rewrite updateFresh σ x (𝐯 x') A (⊢# q it)
      | :=Eq{f = σ}{𝐯 x'} x
      | :=Eq{f = σ'}{𝐯 x'} x =
    TmRefl (⊢𝐯 (∷ (sbJg h q) (okSb＝ p)) (isInNew refl))

lift＝Sb² :
  {x y x' y' : 𝔸}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  ⦃ _ : y # (Γ , x) ⦄
  ⦃ _ : y' # (Γ' , x') ⦄
  (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (p₁ : Γ ⊢ A ty)
  (p₂ : Γ ⸴ x ∶ A ⊢ B ty)
  (p₃ : σ * A ≡ A')
  (p₄ : (x := 𝐯 x')σ * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ˢ σ ∶ Γ)
  → -----------------------------------------------
  (Γ' ⸴ x' ∶ A' ⸴ y' ∶ B') ⊢ˢ
    (y := 𝐯 y')((x := 𝐯 x')σ)  ＝
    (y := 𝐯 y')((x := 𝐯 x')σ') ∶ (Γ ⸴ x ∶ A ⸴ y ∶ B)

lift＝Sb² p p₁ p₂ refl refl h =
  lift＝Sb (lift＝Sb p p₁ h) p₂ (liftSb⁻ h p₁)

----------------------------------------------------------------------
-- Action of convertible substitutions
----------------------------------------------------------------------
＝sbTy :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ty)
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ----------------------
  Γ' ⊢ σ * A ＝ σ' * A ty

＝sbTm :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ∶ A)
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → --------------------------
  Γ' ⊢ σ * a ＝ σ' * a ∶ σ * A

＝sbTy{σ}{σ'}{Γ' = Γ'} p (⊢𝚷ty{A}{B}{x} q₀ q₁ h) h' =
  -- helper hypotheses used
  𝚷TyCong {x = x'}
    (＝sbTy p h h')
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbUpdate⟨⟩ σ' x (𝐯 x') B q₁)
      (＝sbTy (lift＝Sb p h h') q₀ (liftSb⁻ h' h)))
    x'#
    (sbJg h' h)
  where
  S = supp ((σ * B , σ' * B) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

＝sbTy p (⊢𝐈𝐝ty q₀ q₁ h') h = 𝐈𝐝TyCong
  (＝sbTy p h' h)
  (＝sbTm p q₀ h)
  (＝sbTm p q₁ h)

＝sbTy p (⊢𝐔 q) h = TyRefl (⊢𝐔 (okSb＝ p))

＝sbTy p (⊢𝐄𝐥 q) h = ＝𝐄𝐥 (＝sbTm p q h)

＝sbTm{σ}{σ'} p (⊢𝐯{x = x} _ q) h
  rewrite ‿unit (σ x) ⦃ it ⦄
  | ‿unit (σ' x) ⦃ it ⦄ = sbVar＝ p q
＝sbTm p (⊢conv q₀ q₁) h = ＝conv (＝sbTm p q₀ h) (sbJg h q₁)
＝sbTm{σ}{σ'}{Γ' = Γ'} p (⊢𝚷{A}{B}{x} q₀ q₁ q₂) h =
  -- helper hypotheses used
  𝚷TmCong {x = x'}
    (＝sbTm p q₀ h)
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ∶ 𝐔)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbUpdate⟨⟩ σ' x (𝐯 x') B q₂)
      (＝sbTm (lift＝Sb p (⊢𝐄𝐥 q₀) h) q₁ (liftSb⁻ h (⊢𝐄𝐥 q₀))))
    x'#
    (sbJg h q₀)
  where
  S = supp ((σ * B , σ' * B) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

＝sbTm{σ}{σ'}{Γ' = Γ'} p (⊢𝛌{A}{B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) h =
  -- helper hypotheses used
  𝛌Cong {x = x'}
    (＝sbTy p h₀ h)
    (subst₃ (λ c c' C → Γ' ⸴ x' ∶ σ * A ⊢ c ＝ c' ∶ C)
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ' x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (＝sbTm (lift＝Sb p h₀ h) q₀ (liftSb⁻ h h₀)))
    x'#
    (sbJg h h₀)
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb h h₀ (sbJg h h₀)) h₁))
  where
  S = supp ((σ * B , σ * b , σ' * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

＝sbTm{σ}{σ'}{Γ' = Γ'} p (⊢∙{A}{B}{a}{b}{x} q₀ q₁ q₂ q₃ h') h
  rewrite sb⟨⟩ σ B a =
  -- helper hypotheses used
  ∙Cong {x = x'}
    (＝sbTy p h' h)
    (subst₂ (λ C C' → Γ' ⸴ x' ∶ σ * A ⊢ C ＝ C' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₃)
      (sbUpdate⟨⟩ σ' x (𝐯 x') B q₃)
      (＝sbTy (lift＝Sb p h' h) q₂ (liftSb⁻ h h')))
    (＝sbTm p q₀ h)
    (＝sbTm p q₁ h)
    x'#
    (sbJg h h')
    (subst (λ B' → Γ' ⸴ x' ∶ σ * A ⊢ B' ty)
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₃)
      (sbJg (liftSb h h' (sbJg h h')) q₂))
  where
  S = supp ((σ * B , σ' * B) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

＝sbTm p (⊢𝐈𝐝 q₀ q₁ q₂) h = 𝐈𝐝TmCong
  (＝sbTm p q₀ h)
  (＝sbTm p q₁ h)
  (＝sbTm p q₂ h)

＝sbTm p (⊢𝐫𝐞𝐟𝐥 q h') h = 𝐫𝐞𝐟𝐥Cong
  (＝sbTm p q h)
  (sbJg h h')

＝sbTm{σ}{σ'}{Γ' = Γ'} p (⊢𝐉{A}{C}{a}{b}{c}{e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁) h
  rewrite sb⟨⟩² σ C b e =
  -- helper hypotheses used
  𝐉Cong{x = x'}{y'}
    q₀'
    (＝sbTm p q₁ h)
    (＝sbTm p q₂ h)
    (subst (λ C' → Γ' ⊢ σ * c ＝ σ' * c ∶ C')
      (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
      (＝sbTm p q₃ h))
    (＝sbTm p q₄ h)
    x'#
    y'#
    (sbJg h h₀)
    h₁'
  where
  S = supp ((σ * C , σ' * C) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((σ * C , σ' * C) , Γ' , x')
  y' = new S'
  y'# = ∉∪₁ (new∉ S')
  y'#Γ' = ∉∪₁ (∉∪₂ (new∉ S'))
  y'#x' = ∉∪₂ (∉∪₂ (new∉ S'))
  instance
    _ : x' # Γ'
    _ = x'#Γ'
    _ : y' # (Γ' , x')
    _ = y'#Γ' ∉∪ y'#x'

  eq : (x := (𝐯 x'))σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (⊢# q₁ it))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{(𝐯 x')} x = refl

  h₁' : Γ' ⸴ x' ∶ σ * A ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ty
  h₁' = subst (λ C' → Γ' ⸴ x' ∶ σ * A ⊢ C' ty)
    eq
    (sbJg (liftSb h h₀ (sbJg h h₀)) h₁)

  eq' :
    (τ : Sb)
    → ----------------------------------------------------------
    (y := 𝐯 y')((x := 𝐯 x')τ) * C ⟨ x ⸴ y ⟩ ≡ (τ * C)⟨ x' ⸴ y' ⟩
  eq' τ rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')τ)) C (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')τ) y (𝐯 y') C q₆
      | updateFresh τ x (𝐯 x') C q₅
      | :=Eq{f = (x := 𝐯 x')τ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')τ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = τ}{𝐯 x'} x = refl

  q₀' : Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ＝ (σ' * C) ⟨ x' ⸴ y' ⟩ ty
  q₀' = subst₂ (λ D D' →
    Γ' ⸴ x' ∶ σ * A ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ⊢ D ＝ D' ty)
    (eq' σ)
    (eq' σ')
    (＝sbTy (lift＝Sb² p h₀ h₁ refl eq h) q₀
      (liftSb² h h₀ h₁ refl eq (sbJg h h₀) h₁'))

＝sbTm p (⊢𝐍𝐚𝐭 _) _ = TmRefl (⊢𝐍𝐚𝐭 (okSb＝ p))

＝sbTm p (⊢𝐳𝐞𝐫𝐨 _) _ = TmRefl (⊢𝐳𝐞𝐫𝐨 (okSb＝ p))

＝sbTm p (⊢𝐬𝐮𝐜𝐜 q) h = 𝐬𝐮𝐜𝐜Cong (＝sbTm p q h)

＝sbTm{σ}{σ'}{Γ' = Γ'} p (⊢𝐧𝐫𝐞𝐜{C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ q₅) h
  rewrite sb⟨⟩ σ C a =
  -- helper hypotheses used
  𝐧𝐫𝐞𝐜Cong {x = x'} {y'}
    (subst₂ (λ D D' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ D ＝ D' ty)
      (eq σ)
      (eq σ')
      (＝sbTy (lift＝Sb p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) h) q₅
      (liftSb h (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb＝ p))))))
    (subst (λ D → Γ' ⊢ σ * c₀ ＝ σ' * c₀ ∶ D)
      (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
      (＝sbTm p q₀ h))
    q₂'
    (＝sbTm p q₂ h)
    x'#
    y'#
    h'
  where
  S = supp ((σ * C , σ' * C , σ * c₊ , σ' * c₊) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  S' = supp ((σ * c₊ , σ' * c₊) , Γ' , x')
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
  y#C = ⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨) (∉∪₁ it)

  eq :
    (τ : Sb)
    → ------------------------------------
    (x := 𝐯 x')τ * C ⟨ x ⟩ ≡ (τ * C)⟨ x' ⟩
  eq τ rewrite sb⟨⟩ ((x := 𝐯 x')τ) C (𝐯 x)
     | updateFresh τ x (𝐯 x') C q₃
     | :=Eq{f = τ}{𝐯 x'} x = refl

  h' :  Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ (σ * C) ⟨ x' ⟩ ty
  h' = subst (λ C' → Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⊢ C' ty)
    (eq σ)
    (sbJg (liftSb h (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb h)))) q₅)

  eq₊ :
    (τ : Sb)
    → ------------------------------------------------------------
    (y := 𝐯 y')((x := 𝐯 x')τ) * c₊ ⟨ x ⸴ y ⟩ ≡ (τ * c₊)⟨ x' ⸴ y' ⟩
  eq₊ τ rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')τ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')τ) y (𝐯 y') c₊ q₄
      | updateFresh τ x (𝐯 x') c₊ q₃'
      | :=Eq{f = (x := 𝐯 x')τ}{𝐯 y'} y
      | :=Neq{f = (x := 𝐯 x')τ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = τ}{𝐯 x'} x = refl

  eq'' : (y := 𝐯 y')((x := 𝐯 x')σ) * C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ≡
        (σ * C)⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  eq'' rewrite sb⟨⟩ ((y := 𝐯 y')((x := 𝐯 x')σ)) C (𝐬𝐮𝐜𝐜 (𝐯 x))
       | updateFresh ((x := 𝐯 x')σ) y (𝐯 y') C y#C
       | updateFresh σ x (𝐯 x') C q₃
       | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
       | :=Eq{f = σ}{𝐯 x'} x = refl

  q₂' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C)⟨ x' ⟩) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ＝ (σ' * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩
  q₂' = subst₃ (λ d d' D →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ⸴ y' ∶ (σ * C) ⟨ x' ⟩) ⊢ d ＝ d' ∶ D)
      (eq₊ σ)
      (eq₊ σ')
      eq''
      (＝sbTm (lift＝Sb² p (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) q₅ refl (eq σ) h) q₁
        (liftSb² h (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (⊢ok q₀))) q₅ refl (eq σ)
          (⊢𝐄𝐥 (⊢𝐍𝐚𝐭 (okSb h))) h'))

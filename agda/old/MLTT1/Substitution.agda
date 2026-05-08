module MLTT1.Substitution where

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
open import MLTT1.Renaming

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
    {l : Lvl}
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ∶ Γ)
    (q₁ : Γ ⊢ A ∶𝐔 l)
    (q₂ : Γ' ⊢ σ x ∶ σ * A ∶ l)
    → -------------------------
    Γ' ⊢ˢ σ ∶ (Γ ⸴ x ∶ A ∶ l)

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
    {l : Lvl}
    {Γ : Cx}
    {σ σ' : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
    (q₁ : Γ ⊢ A ∶𝐔 l)
    (q₂ : Γ' ⊢ σ x ＝ σ' x ∶ σ * A ∶ l)
    → ---------------------------------
    Γ' ⊢ˢ σ ＝ σ' ∶ (Γ ⸴ x ∶ A ∶ l)

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
sbOk (∷ _ q _) = ∷⁻ q

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
sb＝Ok (∷ _ q _) = ∷⁻ q

okSb＝ :
  {Γ' Γ : Cx}
  {σ σ' : Sb}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → ---------------------
  Ok Γ'

okSb＝ (◇ q) = q
okSb＝ (∷ q _ _) = okSb＝ q

----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------
wkSb :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  (x : 𝔸)
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ A ∶𝐔 l)
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ----------------------
  Γ' ⸴ x ∶ A ∶ l ⊢ˢ σ ∶ Γ

wkSb x q (◇ q') = ◇ (∷ q q')
wkSb x q (∷ q₀ q₁ q₂) = ∷ (wkSb x q q₀) q₁ (wkJg x q q₂)

wk＝Sb :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  (x : 𝔸)
  ⦃ _ : x # Γ' ⦄
  (_ : Γ' ⊢ A ∶𝐔 l)
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  → ---------------------------
  Γ' ⸴ x ∶ A ∶ l ⊢ˢ σ ＝ σ' ∶ Γ

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
⊢ι (∷{l}{x = x} q q') = ∷
  (wkSb _ q (⊢ι q'))
  q
  (⊢𝐯 (∷⁻ q) (isInNew (cong (λ A' → (x , A' , l)) (sbUnit _))))

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
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ (∈∪₁ p'))))
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
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ (∈∪₁ p'))))
  | e x (∈∪₂ ∈｛｝)
  | e' x (∈∪₂ ∈｛｝)= ∷
    (sb＝Ext q (λ y r → e y (∈∪₁ r)) (λ y' r' → e' y' (∈∪₁ r')))
    q₁
    q₂

----------------------------------------------------------------------
-- Lifting substitutions
----------------------------------------------------------------------
liftSb :
  {l : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ∶𝐔 l)
  -- helper hypothesis
  (_ : Γ' ⊢ σ * A ∶𝐔 l)
  → ---------------------------------------------------
  Γ' ⸴ x' ∶ σ * A ∶ l ⊢ˢ (x := 𝐯 x')σ ∶ (Γ ⸴ x ∶ A ∶ l)

liftSb{l}{σ}{Γ}{Γ'}{A}{x}{x'} ⊢σ ⊢A ⊢σA = ∷ (wkSb x' ⊢σA ⊢σ') ⊢A ⊢A'
  where
  ⊢σ' : Γ' ⊢ˢ (x := 𝐯 x')σ ∶ Γ
  ⊢σ' = sbExt ⊢σ (λ y r → symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))

  ⊢A' : (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ (x := 𝐯 x')σ x ∶ (x := 𝐯 x')σ * A ∶ l
  ⊢A' rewrite updateFresh σ x (𝐯 x') A (∉∪₁ (⊢# ⊢A it))
      | :=Eq{f = σ}{𝐯 x'} x = ⊢𝐯 (∷⁻ ⊢σA) (isInNew refl)

-- Iterated lifting
liftSb² :
  {l l' : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  {x y x' y' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  ⦃ _ : y # (Γ , x) ⦄
  ⦃ _ : y' # (Γ' , x') ⦄
  (p : Γ' ⊢ˢ σ ∶ Γ)
  (p₁ : Γ ⊢ A ∶𝐔 l)
  (p₂ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ∶𝐔 l')
  (p₃ : σ * A ≡ A')
  (p₄ : (x := 𝐯 x')σ * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ A' ∶𝐔 l)
  (h' : (Γ' ⸴ x' ∶ A' ∶ l) ⊢ B' ∶𝐔 l')
  → --------------------------------------------------------
  (Γ' ⸴ x' ∶ A' ∶ l ⸴ y' ∶ B' ∶ l') ⊢ˢ
    (y := 𝐯 y')((x := 𝐯 x')σ) ∶ (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ B ∶ l')

liftSb² p p₁ p₂ refl refl h h' = liftSb (liftSb p p₁ h) p₂ h'

----------------------------------------------------------------------
-- Types of variables under substitution
----------------------------------------------------------------------
sbVar :
  {l : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  Γ' ⊢ σ x ∶ σ * A ∶ l

sbVar (∷ _ _ q)  (isInNew refl)  = q
sbVar (∷ q' _ _) (isInOld q)  = sbVar q' q

sbVar＝ :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_  : (x , A , l) isIn Γ)
  → --------------------------
  Γ' ⊢ σ x ＝ σ' x ∶ σ * A ∶ l

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
  let (_ , _ , q') = dom→isIn q
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

sbJg p (⊢conv q₀ q₁) = ⊢conv
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ} p (⊢𝐯{x = x} _ q) rewrite ‿unit (σ x) ⦃ it ⦄ = sbVar p q

sbJg p (⊢𝐔 _) = ⊢𝐔 (okSb p)

sbJg{σ}{Γ' = Γ'} p (⊢𝚷{l}{l'}{A = A}{B}{x} q₀ q₁ q₂) =
  ⊢𝚷{x = x'}
    (sbJg p q₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p q₀ (sbJg p q₀)) q₁))
    x'#
  where
  S = supp (σ * B , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (⊢𝛌{l}{l'}{A}{B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) =
  ⊢𝛌{x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ b' ∶ B' ∶ l')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₀))
    x'#
    (sbJg p h₀)
    (subst (λ C → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ∶𝐔 l')
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

sbJg{σ}{Γ' = Γ'} p (⊢∙{l}{l'}{A}{B}{a}{b}{x} q₀ q₁ q₂ q₃ h)
  rewrite sb⟨⟩ σ B a =
  -- helper hypothesis used
  ⊢∙
    (sbJg p q₀)
    (sbJg p q₁)
    (subst (λ C → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ∶𝐔 l')
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

sbJg p (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐫𝐞𝐟𝐥
  (sbJg p q)
  (sbJg p h)

sbJg{σ}{Γ' = Γ'} p (⊢𝐉{l}{l'}{A}{C}{a}{b}{c}{e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁)
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

  q₃' : Γ' ⊢ σ * c ∶ (σ * C) ⟨ σ * a ⸴ 𝐫𝐞𝐟𝐥 (σ * a)⟩ ∶ l'
  q₃' = subst (λ C' → Γ' ⊢ σ * c ∶ C' ∶ l')
    (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₃)

  eq : (x := 𝐯 x')σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (⊢# q₁ it))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h₁' : (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ I ∶𝐔 l)
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

  q₀' : (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst (λ C →
    (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢ C ∶𝐔 l')
    eq'
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

sbJg p (⊢𝐍𝐚𝐭 _) = ⊢𝐍𝐚𝐭 (okSb p)

sbJg p (⊢𝐳𝐞𝐫𝐨 _) = ⊢𝐳𝐞𝐫𝐨 (okSb p)

sbJg p (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (sbJg p q)

sbJg{σ}{Γ' = Γ'} p (⊢𝐧𝐫𝐞𝐜{l}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C' ∶ l)
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₃
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okSb p))) h)

  eq' : (y := 𝐯 y')((x := 𝐯 x')σ) * c₊ ⟨ x ⸴ y ⟩ ≡
        (σ * c₊)⟨ x' ⸴ y' ⟩
  eq' rewrite sb⟨⟩² ((y := 𝐯 y')((x := 𝐯 x')σ)) c₊ (𝐯 x) (𝐯 y)
      | updateFresh ((x := 𝐯 x')σ) y ( 𝐯 y') c₊ q₄
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

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C)⟨ x' ⟩ ∶ l) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okSb p)) h')
        q₁)

sbJg p (Refl q) = Refl (sbJg p q)

sbJg p (Symm q) = Symm (sbJg p q)

sbJg p (Trans q₀ q₁) = Trans
  (sbJg p q₀)
  (sbJg p q₁)

sbJg p (＝conv q₀ q₁) = ＝conv
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (𝚷Cong{l}{l'}{A = A}{B = B}{B'}{x}
  q₀ q₁ (q₂ ∉∪ q₂') h) =
  𝚷Cong{x = x'}
    (sbJg p q₀)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
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

sbJg{σ}{Γ' = Γ'} p (𝛌Cong{l}{l'}{A}{B = B}{b}{b'}{x}
  q₀ q₁ (q₂ ∉∪ q₂' ∉∪ q₂'') h₀ h₁) =
  𝛌Cong{x = x'}
    (sbJg p q₀)
    (subst₃ (λ c c' C → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ c ＝ c' ∶ C ∶ l')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₂')
      (sbUpdate⟨⟩ σ x (𝐯 x') b' q₂'')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₁))
    x'#
    (sbJg p h₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
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

sbJg{σ}{Γ' = Γ'} p (∙Cong{l}{l'}{A}{A'}{B}{B'}{a}{a'}{b}{b'}{x}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄') h₀ h₁)
  rewrite sb⟨⟩ σ B a =
  -- helper hypotheses used
  ∙Cong{x = x'}
    (sbJg p q₀)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₄)
      (sbUpdate⟨⟩ σ x (𝐯 x') B' q₄')
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₁))
    (sbJg p q₂)
    (sbJg p q₃)
    x'#
    (sbJg p h₀)
    (subst (λ C → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ∶𝐔 l')
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

sbJg p (𝐈𝐝Cong q₀ q₁ q₂) = 𝐈𝐝Cong
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (𝐫𝐞𝐟𝐥Cong q₀ q₁) = 𝐫𝐞𝐟𝐥Cong
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Γ' = Γ'} p (𝐉Cong{l}{l'}{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}{x}{y}
  q₀ q₁ q₂ q₃ q₄ (q₅ ∉∪ q₅') (q₆ ∉∪ q₆') h₀ h₁)
  rewrite sb⟨⟩² σ C b e =
  -- helper hypotheses used
  𝐉Cong{x = x'}{y'}
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

  q₃' : Γ' ⊢ σ * c ＝ σ * c' ∶ (σ * C) ⟨ σ * a ⸴ 𝐫𝐞𝐟𝐥 (σ * a) ⟩ ∶ l'
  q₃' = subst (λ C' → Γ' ⊢ σ * c ＝ σ * c' ∶ C' ∶ l')
    (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₃)

  eq : (x := 𝐯 x')σ * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x')
  eq rewrite  updateFresh σ x (𝐯 x') A (∉∪₂ (∉∪₂ (⊢# q₁ it)))
     | updateFresh σ x (𝐯 x') a (∉∪₁ (⊢# q₁ it))
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h₁' : (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ I ∶𝐔 l)
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
      | :=Neq{f = (x := 𝐯 x')σ}{𝐯 y'} y x
          (λ{refl → ∉→¬∈ it (∈∪₂ ∈｛｝)})
      | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' : (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ＝ (σ * C') ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst₂ (λ D D' →
    (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢ D ＝ D' ∶𝐔 l')
    eq'
    eq''
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

sbJg p (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (sbJg p q)

sbJg{σ}{Γ' = Γ'} p (𝐧𝐫𝐞𝐜Cong{l}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}{x}{y}
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

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (⊢𝐍𝐚𝐭 (okSb p))) h)

  eq' : (x := 𝐯 x')σ * C' ⟨ x ⟩ ≡ (σ * C')⟨ x' ⟩
  eq' rewrite sb⟨⟩ ((x := 𝐯 x')σ) C' (𝐯 x)
     | updateFresh σ x (𝐯 x') C' q₄'
     | :=Eq{f = σ}{𝐯 x'} x = refl

  q₀' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ＝ (σ * C') ⟨ x' ⟩ ∶𝐔 l
  q₀' = subst₂ (λ D D' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ D ＝ D' ∶𝐔 l)
    eq
    eq'
    (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (⊢𝐍𝐚𝐭 (okSb p))) q₀)

  q₁' :  Γ' ⊢ σ * c₀ ＝ σ * c₀' ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₁' = subst (λ D → Γ' ⊢ σ * c₀ ＝ σ * c₀' ∶ D ∶ l)
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

  q₂' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C)⟨ x' ⟩ ∶ l) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ＝ (σ * c₊')⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₂' = subst₃ (λ d d' D →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C) ⟨ x' ⟩ ∶ l) ⊢ d ＝ d' ∶ D ∶ l)
      eq₊
      eq₊'
      eq''
      (sbJg
        (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₃)) h refl eq
          (⊢𝐍𝐚𝐭(okSb p)) h')
        q₂)

sbJg{σ}{Γ' = Γ'} p (𝚷Beta{l}{l'}{A}{a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁)
  rewrite sb⟨⟩ σ b a
  | sb⟨⟩ σ B a =
  -- helper hypotheses used
  𝚷Beta{x = x'}
    (subst₂ (λ b' B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ b' ∶ B' ∶ l')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₂')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) q₀))
    (sbJg p q₁)
    x'#
    (sbJg p h₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbJg (liftSb p h₀ (sbJg p h₀)) h₁))
  where
  S = supp ((σ * B , σ * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

sbJg{σ}{Γ' = Γ'} p (𝐈𝐝Beta{l}{l'}{A}{C}{a}{c}{x}{y}
  q₀ q₁ q₂ q₃ q₄ h₀ h₁)
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

  h₁' : (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ I ∶𝐔 l)
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

  q₀' : (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst (λ D →
    (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l ) ⊢ D ∶𝐔 l')
    eq'
    (sbJg (liftSb² p h₀ h₁ refl eq (sbJg p h₀) h₁') q₀)

  q₂' : Γ' ⊢ σ * c ∶ (σ * C) ⟨ σ * a ⸴ 𝐫𝐞𝐟𝐥 (σ * a) ⟩ ∶ l'
  q₂' = subst (λ D → Γ' ⊢ σ * c ∶ D ∶ l')
    (sb⟨⟩² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₂)

sbJg{σ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₀{l}{C}{c₀}{c₊}{x}{y} q₀ q₁ (q₂ ∉∪ q₂') q₃ h)
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C' ∶ l)
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₂
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okSb p))) h)

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

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C)⟨ x' ⟩ ∶ l) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okSb p)) h')
        q₁)

sbJg{σ}{Γ' = Γ'} p (𝐍𝐚𝐭Beta₊{l}{C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h)
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

  q₀' :  Γ' ⊢ σ * c₀ ∶ (σ * C) ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l
  q₀' = subst (λ C' → Γ' ⊢ σ * c₀ ∶ C' ∶ l)
    (sb⟨⟩ σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀)

  eq : (x := 𝐯 x')σ * C ⟨ x ⟩ ≡ (σ * C)⟨ x' ⟩
  eq rewrite sb⟨⟩ ((x := 𝐯 x')σ) C (𝐯 x)
     | updateFresh σ x (𝐯 x') C q₃
     | :=Eq{f = σ}{𝐯 x'} x = refl

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    eq
    (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okSb p))) h)

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

  q₁' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C)⟨ x' ⟩ ∶ l) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₁' = subst₂ (λ c' C' →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C) ⟨ x' ⟩ ∶ l) ⊢ c' ∶ C' ∶ l)
      eq'
      eq''
      (sbJg
        (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h refl eq
          (⊢𝐍𝐚𝐭(okSb p)) h')
        q₁)

sbJg{σ}{Γ' = Γ'} p (𝚷Eta{l}{l'}{A}{B}{b}{x} q₀ q₁ h) =
  -- helper hypothesis used
  subst (λ b' → Γ' ⊢ σ * b ＝ b' ∶ 𝚷 (σ * A) (σ * B) ∶ max l l')
    eq
    (𝚷Eta{x = x'}
      (sbJg p q₀)
      (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
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

  eq : 𝛌 (σ * A)(x' ． (σ * b) ∙[ σ * A , σ * B ] 𝐯 x') ≡
    σ * 𝛌 A (x ． b ∙[ A , B ] 𝐯 x)
  eq rewrite sbAbs σ x x' (b ∙[ A , B ] 𝐯 x) f
     | updateFresh σ x (𝐯 x') b x#b
     | updateFresh σ x (𝐯 x') A x#A
     | updateFresh σ x (𝐯 x') B x#B
     | :=Eq{f = σ}{𝐯 x'} x = refl

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
sb＝Refl (∷ q₀ q₁ q₂) = ∷ (sb＝Refl q₀) q₁ (Refl q₂)

----------------------------------------------------------------------
-- Properties of substitution update
----------------------------------------------------------------------
sbUpdate :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ' ⊢ a ∶ σ * A ∶ l)
  -- helper hypothesis
  (_ : Γ ⊢ A ∶𝐔 l)
  → --------------------------------
  Γ' ⊢ˢ (x := a) σ ∶ (Γ ⸴ x ∶ A ∶ l)

sbUpdate{l}{Γ' = Γ'}{σ}{A}{a}{x} ⊢σ ⊢a ⊢A = ∷
  (sbExt ⊢σ (λ y r →
    symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r })))
  ⊢A
  (subst₂ (λ z Z → Γ' ⊢ z ∶ Z ∶ l)
    (symm (:=Eq{f = σ}{a} x))
    (symm (updateFresh σ x a A (∉∪₁ (⊢# ⊢A it))))
    ⊢a)

sb＝Update :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ' ⊢ a ＝ a' ∶ σ * A ∶ l)
  -- helper hypothesis
  (_ : Γ ⊢ A ∶𝐔 l)
  → -----------------------------------------------
  Γ' ⊢ˢ (x := a) σ ＝ (x := a') σ' ∶ (Γ ⸴ x ∶ A ∶ l)

sb＝Update{l}{Γ' = Γ'}{σ}{σ'}{A}{a}{a'}{x} σ=σ' a=a' ⊢A = ∷
  (sb＝Ext σ=σ'
    (λ y r →
      symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))
    (λ y r →
      symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ it r })))
  ⊢A
  (subst₃ (λ z z' Z → Γ' ⊢ z ＝ z' ∶ Z ∶ l)
    (symm (:=Eq{f = σ}{a} x))
    (symm (:=Eq{f = σ'}{a'} x))
    (symm (updateFresh σ x a A (∉∪₁ (⊢# ⊢A it))))
    a=a')

ssbUpdate :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ a ∶ A ∶ l)
  -- helper hypothesis
  (_ : Γ ⊢ A ∶𝐔 l)
  → ----------------------------
  Γ ⊢ˢ (x ≔ a) ∶ (Γ ⸴ x ∶ A ∶ l)

ssbUpdate{l}{Γ}{A}{a} q h = sbUpdate
  (⊢ι (⊢ok q))
  (subst (λ A' → Γ ⊢ a ∶ A' ∶ l) (symm (sbUnit A)) q)
  h

ssb＝Update :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ a ＝ a' ∶ A ∶ l)
  -- helper hypothesis
  (_ : Γ ⊢ A ∶𝐔 l)
  → ----------------------------------------
  Γ ⊢ˢ (x ≔ a) ＝ (x ≔ a') ∶ (Γ ⸴ x ∶ A ∶ l)

ssb＝Update{l}{Γ}{A}{a}{a'} q h = sb＝Update
  (sb＝Refl (⊢ι (⊢ok q)))
  (subst (λ A' → Γ ⊢ a ＝ a' ∶ A' ∶ l) (symm (sbUnit A)) q)
  h

ssbUpdate² :
  {l l' : Lvl}
  {Γ : Cx}
  {x y : 𝔸}
  {a b : Tm}
  {A B : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ∶𝐔 l')
  (_ : Γ ⊢ b ∶ (x ≔ a) * B ∶ l')
  → -------------------------------------------------
  Γ ⊢ˢ (y := b)(x ≔ a) ∶ (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ B ∶ l')

ssbUpdate² q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₁ = sbUpdate (ssbUpdate q₀ ⊢A) q₂ q₁

ssb＝Update² :
  {l l' : Lvl}
  {Γ : Cx}
  {x y : 𝔸}
  {a a' b b' : Tm}
  {A  B : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ a ＝ a' ∶ A ∶ l)
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ∶𝐔 l')
  (_ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B ∶ l')
  → ----------------------------------------------------------------------
  Γ ⊢ˢ (y := b)(x ≔ a) ＝ (y := b')(x ≔ a') ∶ (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ B ∶ l')

ssb＝Update² q₀ q₁ q₂
  with ∷ ⊢A _ ← ⊢ok q₁ = sb＝Update (ssb＝Update q₀ ⊢A) q₂ q₁

----------------------------------------------------------------------
-- Lifting substitutions, again
----------------------------------------------------------------------
liftSb⁻ :
  -- liftSb without the helper hypothesis
  {l : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ∶𝐔 l)
  → ---------------------------------------------------
  Γ' ⸴ x' ∶ σ * A ∶ l ⊢ˢ (x := 𝐯 x')σ ∶ (Γ ⸴ x ∶ A ∶ l)

liftSb⁻ p q = liftSb p q (sbJg p q)

lift＝Sb :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ∶𝐔 l)
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → --------------------------------------------------------------------
  Γ' ⸴ x' ∶ σ * A ∶ l ⊢ˢ (x := 𝐯 x')σ ＝ (x := 𝐯 x')σ' ∶ (Γ ⸴ x ∶ A ∶ l)

lift＝Sb{l}{σ}{σ'}{Γ}{Γ'}{A}{x}{x'} p q h =
  ∷ (wk＝Sb x' (sbJg h q) p') q q''
  where
  p' : Γ' ⊢ˢ (x := 𝐯 x') σ ＝ (x := 𝐯 x') σ' ∶ Γ
  p' = sb＝Ext p
    (λ y r → symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ it r }))
    λ y r → symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ it r })

  q'' : Γ' ⸴ x' ∶ σ * A ∶ l ⊢
      (x := 𝐯 x')σ x ＝ (x := 𝐯 x')σ' x ∶ (x := 𝐯 x')σ * A ∶ l
  q'' rewrite updateFresh σ x (𝐯 x') A (∉∪₁ (⊢# q it))
      | :=Eq{f = σ}{𝐯 x'} x
      | :=Eq{f = σ'}{𝐯 x'} x =
    Refl (⊢𝐯 (∷⁻ (sbJg h q)) (isInNew refl))

lift＝Sb² :
  {l l' : Lvl}
  {x y x' y' : 𝔸}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  ⦃ _ : y # (Γ , x) ⦄
  ⦃ _ : y' # (Γ' , x') ⦄
  (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (p₁ : Γ ⊢ A ∶𝐔 l)
  (p₂ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ∶𝐔 l')
  (p₃ : σ * A ≡ A')
  (p₄ : (x := 𝐯 x')σ * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------------------------------------------------
  (Γ' ⸴ x' ∶ A' ∶ l ⸴ y' ∶ B' ∶ l') ⊢ˢ
    (y := 𝐯 y')((x := 𝐯 x')σ)  ＝
    (y := 𝐯 y')((x := 𝐯 x')σ') ∶ (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ B ∶ l')

lift＝Sb² p p₁ p₂ refl refl h =
  lift＝Sb (lift＝Sb p p₁ h) p₂ (liftSb⁻ h p₁)

----------------------------------------------------------------------
-- Action of convertible substitutions
----------------------------------------------------------------------
＝sbTm :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ∶ A ∶ l)
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ------------------------------
  Γ' ⊢ σ * a ＝ σ' * a ∶ σ * A ∶ l

＝sbTm p (⊢conv q₀ q₁) h = ＝conv (＝sbTm p q₀ h) (sbJg h q₁)

＝sbTm{σ = σ}{σ'} p (⊢𝐯{x = x} _ q) h
  rewrite ‿unit (σ x) ⦃ it ⦄
  | ‿unit (σ' x) ⦃ it ⦄ = sbVar＝ p q

＝sbTm p (⊢𝐔 _) h = Refl (⊢𝐔 (okSb＝ p))

＝sbTm{σ = σ}{σ'}{Γ' = Γ'} p (⊢𝚷{l}{l'}{A = A}{B}{x} q₀ q₁ q₂) h =
  -- helper hypotheses used
  𝚷Cong{x = x'}
    (＝sbTm p q₀ h)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
      (sbUpdate⟨⟩ σ' x (𝐯 x') B q₂)
      (＝sbTm (lift＝Sb p q₀ h) q₁ (liftSb⁻ h q₀)))
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

＝sbTm{σ = σ}{σ'}{Γ' = Γ'} p (⊢𝛌{l}{l'}{A}{B}{b}{x}
  q₀ (q₁ ∉∪ q₁') h₀ h₁) h' =
  -- helper hypotheses used
  𝛌Cong{x = x'}
    (＝sbTm p h₀ h')
    (subst₃ (λ c c' C → Γ' ⸴ x' ∶ σ * A ∶ l ⊢ c ＝ c' ∶ C ∶ l')
      (sbUpdate⟨⟩ σ x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ' x (𝐯 x') b q₁')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (＝sbTm (lift＝Sb p h₀ h') q₀ (liftSb⁻ h' h₀)))
    x'#
    (sbJg h' h₀)
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₁)
      (sbJg (liftSb h' h₀ (sbJg h' h₀)) h₁))
  where
  S = supp ((σ * B , σ * b , σ' * b) , Γ')
  x' = new S
  x'# = ∉∪₁ (new∉ S)
  x'#Γ' = ∉∪₂ (new∉ S)
  instance
    _ : x' # Γ'
    _ = x'#Γ'

＝sbTm{σ = σ}{σ'}{Γ' = Γ'} p
  (⊢∙{l}{l'}{A}{B}{a}{b}{x} q₀ q₁ q₂ q₃ h') h
  rewrite sb⟨⟩ σ B a =
  -- helper hypotheses used
  ∙Cong{x = x'}
    (＝sbTm p h' h)
    (subst₂ (λ C C' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ C ＝ C' ∶𝐔 l')
      (sbUpdate⟨⟩ σ x (𝐯 x') B q₃)
      (sbUpdate⟨⟩ σ' x (𝐯 x') B q₃)
      (＝sbTm (lift＝Sb p h' h) q₂ (liftSb⁻ h h')))
    (＝sbTm p q₀ h)
    (＝sbTm p q₁ h)
    x'#
    (sbJg h h')
    (subst (λ B' → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ B' ∶𝐔 l')
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

＝sbTm p (⊢𝐈𝐝 q₀ q₁ h) h' = 𝐈𝐝Cong
  (＝sbTm p h h')
  (＝sbTm p q₀ h')
  (＝sbTm p q₁ h')

＝sbTm p (⊢𝐫𝐞𝐟𝐥 q h') h = 𝐫𝐞𝐟𝐥Cong
  (＝sbTm p q h)
  (sbJg h h')

＝sbTm{σ = σ}{σ'}{Γ' = Γ'} p (⊢𝐉{l}{l'}{A}{C}{a}{b}{c}{e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁) h
  rewrite sb⟨⟩² σ C b e =
  -- helper hypotheses used
  𝐉Cong{x = x'}{y'}
    q₀'
    (＝sbTm p q₁ h)
    (＝sbTm p q₂ h)
    (subst (λ C' → Γ' ⊢ σ * c ＝ σ' * c ∶ C' ∶ l')
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

  h₁' : (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶𝐔 l
  h₁' = subst (λ I → (Γ' ⸴ x' ∶ σ * A ∶ l) ⊢ I ∶𝐔 l)
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

  q₀' : (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢
    (σ * C) ⟨ x' ⸴ y' ⟩ ＝ (σ' * C) ⟨ x' ⸴ y' ⟩ ∶𝐔 l'
  q₀' = subst₂ (λ D D' →
    (Γ' ⸴ x' ∶ σ * A ∶ l ⸴ y' ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x') ∶ l) ⊢ D ＝ D' ∶𝐔 l')
    (eq' σ)
    (eq' σ')
    (＝sbTm (lift＝Sb² p h₀ h₁ refl eq h) q₀
      (liftSb² h h₀ h₁ refl eq (sbJg h h₀) h₁'))

＝sbTm p (⊢𝐍𝐚𝐭 _) _ = Refl (⊢𝐍𝐚𝐭 (okSb＝ p))

＝sbTm p (⊢𝐳𝐞𝐫𝐨 _) _ = Refl (⊢𝐳𝐞𝐫𝐨 (okSb＝ p))

＝sbTm p (⊢𝐬𝐮𝐜𝐜 q) h = 𝐬𝐮𝐜𝐜Cong (＝sbTm p q h)

＝sbTm{σ = σ}{σ'}{Γ' = Γ'} p (⊢𝐧𝐫𝐞𝐜{l}{C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ q₅) h
  rewrite sb⟨⟩ σ C a =
  -- helper hypotheses used
  𝐧𝐫𝐞𝐜Cong {x = x'} {y'}
    (subst₂ (λ D D' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ D ＝ D' ∶𝐔 l)
      (eq σ)
      (eq σ')
      (＝sbTm (lift＝Sb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) h) q₅
      (liftSb h (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okSb＝ p)))))
    (subst (λ D → Γ' ⊢ σ * c₀ ＝ σ' * c₀ ∶ D ∶ l)
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

  h' :  (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ (σ * C) ⟨ x' ⟩ ∶𝐔 l
  h' = subst (λ C' → (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0) ⊢ C' ∶𝐔 l)
    (eq σ)
    (sbJg (liftSb h (⊢𝐍𝐚𝐭 (⊢ok q₀)) (⊢𝐍𝐚𝐭 (okSb h))) q₅)

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

  q₂' : (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C)⟨ x' ⟩ ∶ l) ⊢
      (σ * c₊)⟨ x' ⸴ y' ⟩ ＝ (σ' * c₊)⟨ x' ⸴ y' ⟩ ∶ (σ * C) ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x') ⟩ ∶ l
  q₂' = subst₃ (λ d d' D →
    (Γ' ⸴ x' ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y' ∶ (σ * C) ⟨ x' ⟩ ∶ l) ⊢ d ＝ d' ∶ D ∶ l)
      (eq₊ σ)
      (eq₊ σ')
      eq''
      (＝sbTm (lift＝Sb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) q₅ refl (eq σ) h) q₁
        (liftSb² h (⊢𝐍𝐚𝐭 (⊢ok q₀)) q₅ refl (eq σ)
          (⊢𝐍𝐚𝐭 (okSb h)) h'))

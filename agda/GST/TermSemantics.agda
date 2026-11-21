module GST.TermSemantics where

open import Prelude
open import WSLN

open import GST.Syntax
open import GST.Context
open import GST.TypeSystem
open import GST.WellScoped
open import GST.Setoid
open import GST.Renaming
open import GST.Substitution
open import GST.Admissible
open import GST.UniqueTypes
open import GST.NormalForm
open import GST.Presheaf
open import GST.TypeSemantics
open import GST.ReifyReflect

----------------------------------------------------------------------
-- Presheaf semantics of terms
----------------------------------------------------------------------
⟦_⟧ :
  {Γ : Cx}
  {a : Tm}
  {A : Ty}
  (_ : Γ ⊢ a ∶ A)
  → ---------------
  ℝ^[ 𝓔 Γ ⟶ 𝓓 A ]

nrec₁ :
  {C : Ty}
  {Γ : Cx}
  (_ : ∣ 𝓓 C ⊙ Γ ∣)
  (_ : ∣ 𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙ Γ ∣)
  (_ : ∣ 𝓓 𝐍𝐚𝐭 ⊙ Γ ∣)
  → ---------------------------
  ∣ 𝓓 C ⊙ Γ ∣

nrec₁ 𝓬₀ _ (mk∣Norm∣ _ Zero) = 𝓬₀
nrec₁{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ _ (Succ q)) =
  hom ev^ ₀
    (hom ev^ ₀ (𝓬₊ , mk∣Norm∣ _ q) ,
     nrec₁{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ _ q))
nrec₁{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ _ (Neu q)) =
  ↑₀{C} (Nrec (↓₀⊢ 𝓬₀) (↓₀⊢ 𝓬₊) q)

hom-ev^₁ :
  {A B : Ty}
  {Γ : Cx}
  (𝓯 𝓯' : ∣ 𝓓 (A ⇒ B) ⊙ Γ ∣)
  (𝓪 𝓪' : ∣ 𝓓 A ⊙ Γ ∣)
  (_ : 𝓓 (A ⇒ B) ⊙ Γ ∋ 𝓯 ~ 𝓯')
  (_ : 𝓓 A ⊙ Γ ∋ 𝓪 ~ 𝓪')
  → -----------------------------------------------
  𝓓 B ⊙ Γ ∋ hom ev^ ₀ (𝓯 , 𝓪) ~ hom ev^ ₀ (𝓯' , 𝓪')

hom-ev^₁ 𝓯 𝓯' 𝓪 𝓪' e e' =
  _₁_ (hom (ev^)) {𝓯 , 𝓪} {𝓯' , 𝓪'} (e , e')

nrec₂ :
  {C : Ty}
  {Γ : Cx}
  {𝓬₀ 𝓬₀' : ∣ 𝓓 C ⊙ Γ ∣}
  {𝓬₊ 𝓬₊' : ∣ 𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙ Γ ∣}
  (𝓪 𝓪' : ∣ 𝓓 𝐍𝐚𝐭 ⊙ Γ ∣)
  (_ : 𝓓 C ⊙ Γ ∋ 𝓬₀ ~ 𝓬₀')
  (_ : 𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙ Γ ∋ 𝓬₊ ~ 𝓬₊')
  (_ : 𝓓 𝐍𝐚𝐭 ⊙ Γ ∋ 𝓪 ~ 𝓪')
  → ----------------------------------------------
  𝓓 C ⊙ Γ ∋ nrec₁{C} 𝓬₀ 𝓬₊ 𝓪 ~ nrec₁{C} 𝓬₀' 𝓬₊' 𝓪'

nrec₂ (mk∣Norm∣ 𝐳𝐞𝐫𝐨 Zero) (mk∣Norm∣ _ Zero) e _ refl = e
nrec₂{C}{Γ}{𝓬₊ = 𝓬₊}{𝓬₊'}
  (mk∣Norm∣ (𝐬𝐮𝐜𝐜 a) (Succ q))
  (mk∣Norm∣ _ (Succ q')) e₀ e₁ refl =
  let
    𝓪 : ∣ Norm 𝐍𝐚𝐭 ⊙ Γ ∣
    𝓪 = mk∣Norm∣ a q
    𝓪' : ∣ Norm 𝐍𝐚𝐭 ⊙ Γ ∣
    𝓪' = mk∣Norm∣ a q'
  in
  hom-ev^₁{C}{C}
    (hom ev^ ₀ (𝓬₊ , 𝓪))
    (hom ev^ ₀ (𝓬₊' , 𝓪'))
    _
    _
    (hom-ev^₁{𝐍𝐚𝐭}{C ⇒ C} 𝓬₊ 𝓬₊' 𝓪 𝓪' e₁ refl)
    (nrec₂{C} 𝓪 𝓪' e₀ e₁ refl)

nrec₂{C}{Γ}{𝓬₀}{𝓬₀'}{𝓬₊}{𝓬₊'}
  (mk∣Norm∣ a (Neu q))
  (mk∣Norm∣ a (Neu q')) e₀ e₁ refl =
  hom (↑ C) ₁ e
  where
  e : 𝐧𝐫𝐞𝐜 (↓₀ C 𝓬₀) (↓₀ (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬₊) a ≡
      𝐧𝐫𝐞𝐜 (↓₀ C 𝓬₀') (↓₀ (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬₊') a
  e rewrite hom (↓ C) ₁ e₀
    | _₁_ (hom (↓ (𝐍𝐚𝐭 ⇒ C ⇒ C))) {x = 𝓬₊}{𝓬₊'} e₁ = refl

nrec₃ :
  {C : Ty}
  {Γ Γ' : Cx}
  (𝓬₀ : ∣ 𝓓 C ⊙ Γ ∣)
  (𝓬₊ : ∣ 𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙ Γ ∣)
  (𝓪 : ∣ 𝓓 𝐍𝐚𝐭 ⊙ Γ ∣)
  (p : ∣ Γ' →ᵣ Γ ∣)
  → ----------------------------
  𝓓 C ⊙ Γ' ∋
  nrec₁{C}
    (𝓓 C ⊙′ p ₀ 𝓬₀)
    (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙′ p ₀ 𝓬₊)
    (𝓓 𝐍𝐚𝐭 ⊙′ p ₀ 𝓪)
  ~
  𝓓 C ⊙′ p ₀ (nrec₁{C} 𝓬₀ 𝓬₊ 𝓪)

nrec₃{C}{Γ' = Γ'} 𝓬₀ _ (mk∣Norm∣ _ Zero) p =
  ~Refl (𝓓 C ⊙ Γ') (𝓓 C ⊙′ p ₀ 𝓬₀)
nrec₃{C}{Γ}{Γ'} 𝓬₀ 𝓬₊ (mk∣Norm∣ (𝐬𝐮𝐜𝐜 a) (Succ q)) p =
  ~Trans (𝓓 C ⊙ Γ')
    (hom-ev^₁{C}{C}
      (hom ev^ ₀ (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙′ p ₀ 𝓬₊ , _))
      (𝓓 (C ⇒ C) ⊙′ p ₀ (hom ev^ ₀ (𝓬₊ , mk∣Norm∣ a q)))
      (nrec₁ {C}
        (𝓓 C ⊙′ p ₀ 𝓬₀)
        (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ⊙′ p ₀ 𝓬₊)
        (𝓓 𝐍𝐚𝐭 ⊙′ p ₀ (mk∣Norm∣ a q)))
      (𝓓 C ⊙′ p ₀ nrec₁{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ _ q))
      (ntl ev^ p (𝓬₊ , mk∣Norm∣ a q))
      (nrec₃{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ a q) p))
    (ntl ev^ p
      (hom ev^ ₀ (𝓬₊ , mk∣Norm∣ a q) ,
       nrec₁{C} 𝓬₀ 𝓬₊ (mk∣Norm∣ a q)))

nrec₃{C}{Γ' = Γ'} 𝓬₀ 𝓬₊ (mk∣Norm∣ a (Neu q)) p = ~Trans (𝓓 C ⊙ Γ')
  (hom (↑ C) ₁ cong₃ 𝐧𝐫𝐞𝐜
    (ntl (↓ C) p 𝓬₀)
    (ntl (↓ (𝐍𝐚𝐭 ⇒ C ⇒ C)) p 𝓬₊)
    refl)
  (ntl (↑ C) p
    (mk∣Neut∣ (𝐧𝐫𝐞𝐜 (↓₀ C 𝓬₀) (↓₀ (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬₊) a)
              (Nrec (↓₀⊢ 𝓬₀) (↓₀⊢ 𝓬₊) q)))

⟦𝐳𝐞𝐫𝐨⟧ : ∀{Γ} → ℝ^[ 𝓔 Γ ⟶ Norm 𝐍𝐚𝐭 ]

hom ⟦𝐳𝐞𝐫𝐨⟧ {Γ} ₀ _ = mk∣Norm∣ 𝐳𝐞𝐫𝐨 Zero
hom ⟦𝐳𝐞𝐫𝐨⟧ ₁ _ = refl
ntl ⟦𝐳𝐞𝐫𝐨⟧ _ _ = refl

⟦𝐬𝐮𝐜𝐜⟧ : ℝ^[ Norm 𝐍𝐚𝐭 ⟶ Norm 𝐍𝐚𝐭 ]

hom ⟦𝐬𝐮𝐜𝐜⟧ ₀ mk∣Norm∣ a q = mk∣Norm∣ (𝐬𝐮𝐜𝐜 a) (Succ q)
hom ⟦𝐬𝐮𝐜𝐜⟧ ₁ refl = refl
ntl ⟦𝐬𝐮𝐜𝐜⟧ _ _ = refl


⟦𝐧𝐫𝐞𝐜⟧ : ∀{C} → ℝ^[ 𝓓 C ×^ (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) ×^ 𝓓 𝐍𝐚𝐭 ⟶ 𝓓 C ]

hom (⟦𝐧𝐫𝐞𝐜⟧{C}) ₀ ((𝓬₀ , 𝓬₊) , 𝓪) = nrec₁{C} 𝓬₀ 𝓬₊ 𝓪
_₁_ (hom (⟦𝐧𝐫𝐞𝐜⟧{C})) {_ , 𝓪} {_ , 𝓪'} ((e₁ , e₂) , e₃) =
  nrec₂{C} 𝓪 𝓪' e₁ e₂ e₃
ntl (⟦𝐧𝐫𝐞𝐜⟧{C}) p ((𝓬₀ , 𝓬₊) , 𝓪) = nrec₃ {C} 𝓬₀ 𝓬₊ 𝓪 p

⟦ Var q ⟧ = val q
⟦ Lam q x# ⟧ = cur^ ⟦ q ⟧
⟦ App q₀ q₁ ⟧ = ev^ ∘ pair^ ⟦ q₀ ⟧ ⟦ q₁ ⟧
⟦_⟧{Γ } Zero = ⟦𝐳𝐞𝐫𝐨⟧{Γ}
⟦ Succ q ⟧ = ⟦𝐬𝐮𝐜𝐜⟧ ∘ ⟦ q ⟧
⟦ Nrec{C} q₀ q₁ q₂ ⟧ =
  ⟦𝐧𝐫𝐞𝐜⟧{C} ∘ pair^ (pair^ ⟦ q₀ ⟧ ⟦ q₁ ⟧) ⟦ q₂ ⟧

⟦_⟧₀ :
  {Γ Γ' : Cx}
  {a : Tm}
  {A : Ty}
  (_ : Γ ⊢ a ∶ A)
  (_ : ∣ 𝓔 Γ ⊙ Γ' ∣)
  → ----------------
  ∣ 𝓓 A ⊙ Γ' ∣

⟦ q ⟧₀ 𝓼 = hom ⟦ q ⟧ ₀ 𝓼

----------------------------------------------------------------------
-- Semantics of renaming
----------------------------------------------------------------------
⟦rn⟧ :
  {Γ Γ' Γ'' : Cx}
  {A : Ty}
  {a : Tm}
  (p : ℝ[ Γ' ⟶ Γ ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (q : Γ ⊢ a ∶ A)
  → ----------------------------------------------
  𝓓 A ⊙ Γ'' ∋ ⟦ rn⊢ (pf p) q ⟧₀ 𝓼 ~ ⟦ q ⟧₀ (p ⊚ 𝓼)

rnSem :
  {Γ Γ' Γ'' : Cx}
  {A A' : Ty}
  {a a' : Tm}
  (p : ℝ[ Γ' ⟶ Γ ])
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (q : Γ ⊢ a ∶ A)
  (q' : Γ' ⊢ a' ∶ A')
  (_ : rn p * a ≡ a')
  (e : A ≡ A')
  → --------------------------------------------
  𝓓 A' ⊙ Γ'' ∋ ⟦ q' ⟧₀ 𝓼 ~
  subst (λ X → ∣ 𝓓 X ⊙ Γ'' ∣) e (⟦ q ⟧₀ (p ⊚ 𝓼))

⟦rn⟧ p 𝓼 q = rnSem p 𝓼 q (rn⊢ (pf p) q) refl refl

rnSem{Γ}{Γ'}{Γ''} p 𝓼
  (Lam{A}{B}{b}{x} q x#)
  (Lam{x = x'} q' x'#)
  refl e {Γ'''} (p' , 𝓪)
  with refl ← π₂ (⇒inj e)
  rewrite ! ⦃ !≡ ⦄ e refl = ~Trans (𝓓 B ⊙ Γ''')
    (rnSem p'' (𝓔 Γ' ⊙′ p' ₀ 𝓼 , 𝓪) q q' e' refl)
    (hom ⟦ q ⟧ ₁ 𝓮)
  where
  p'' : ∣ (Γ' ⨟ x' ∶ A) →ᵣ (Γ ⨟ x ∶ A) ∣
  p'' = p ⋉[ x , x' ] A

  e' : rn p'' * (b [ x ]) ≡ (rn p * b)[ x' ]
  e' = rnUpdate[] (rn p) x x' b x#

  𝓮 : 𝓔 (Γ ⨟ x ∶ A) ⊙ Γ''' ∋
    p'' ⊚ (𝓔 Γ' ⊙′ p' ₀ 𝓼 , 𝓪) ~ (𝓔 Γ ⊙′ p' ₀ (p ⊚ 𝓼) , 𝓪)
  𝓮 = ~Trans (𝓔 (Γ ⨟ x ∶ A) ⊙ Γ''')
    (renUpdate p (𝓔 Γ' ⊙′ p' ₀ 𝓼) 𝓪)
    (ntl⊚ p p' 𝓼 , ~Refl (𝓓 A ⊙ Γ''') 𝓪)

rnSem p 𝓼 (Var q) (Var q') refl refl = renVal p 𝓼 q q'

rnSem{Γ'' = Γ''}{B} p 𝓼
  (App{A = A} q₀ q₁) (App{A = A'} q₀' q₁') refl refl
  with refl ← svTy q₁' (rn⊢ (pf p) q₁) =
  hom-ev^₁{A}{B}
    (⟦ q₀' ⟧₀ 𝓼)
    (⟦ q₀ ⟧₀ (p ⊚ 𝓼))
    (⟦ q₁' ⟧₀ 𝓼)
    (⟦ q₁ ⟧₀ (p ⊚ 𝓼))
    (rnSem p 𝓼 q₀ q₀' refl refl)
    (rnSem p 𝓼 q₁ q₁' refl refl)

rnSem _ _ Zero Zero refl refl = refl

rnSem p 𝓼 (Succ q) (Succ q') refl refl =
  cong 𝐬𝐮𝐜𝐜 (rnSem p 𝓼 q q' refl refl)

rnSem{Γ'' = Γ''}{C} p 𝓼
  (Nrec q₀ q₁ q₂) (Nrec q₀' q₁' q₂') refl refl = nrec₂{C}
  (⟦ q₂' ⟧₀ 𝓼)
  (⟦ q₂ ⟧₀ (p ⊚ 𝓼))
  (rnSem p 𝓼 q₀ q₀' refl refl)
  (rnSem p 𝓼 q₁ q₁' refl refl)
  (rnSem p 𝓼 q₂ q₂' refl refl)

-- The semantics of terms is proof irrelevant
irrelSem :
  {Γ Γ' : Cx}
  {A : Ty}
  {a a' : Tm}
  (q : Γ ⊢ a ∶ A)
  (q' : Γ ⊢ a' ∶ A)
  (_ : a ≡ a')
  (𝓼 : ∣ 𝓔 Γ ⊙ Γ' ∣)
  → ------------------------------
  𝓓 A ⊙ Γ' ∋ ⟦ q ⟧₀ 𝓼 ~ ⟦ q' ⟧₀ 𝓼

irrelSem{Γ}{Γ'}{A}{a} q q' refl 𝓼  =
  subst (λ 𝓼' → 𝓓 A ⊙ Γ' ∋ ⟦ q ⟧₀ 𝓼 ~ ⟦ q' ⟧₀ 𝓼')
    (⊚unit 𝓼)
    (rnSem (idr Γ) 𝓼 q' q (rnUnit a) refl)

-- The semantics of abstractions is independent of
-- the choice of fresh name at which they are concreted
rnSem¹ :
  {Γ Γ' : Cx}
  {A B : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ ⦄
  (b : Tm[ 1 ])
  (q : Γ ⨟ x ∶ A ⊢ b [ x ] ∶ B)
  (q' : Γ ⨟ x' ∶ A ⊢ b [ x' ] ∶ B)
  (_ : x # b)
  (_ : x' # b)
  (𝓼 : ∣ 𝓔 Γ ⊙ Γ' ∣)
  (𝓪 : ∣ 𝓓 A ⊙ Γ' ∣)
  → -----------------------------------------
  𝓓 B ⊙ Γ' ∋ ⟦ q ⟧₀ (𝓼 , 𝓪) ~ ⟦ q' ⟧₀ (𝓼 , 𝓪)

rnSem¹{Γ}{Γ'}{A}{B}{x}{x'} b q q' x#b x'#b 𝓼 𝓪 =
  ~Trans (𝓓 B ⊙ Γ')
    (rnSem p (𝓼 , 𝓪) q' q (srn[] x' x b x'#b) refl)
    (hom ⟦ q' ⟧ ₁ 𝓮)
  where
  p : ℝ[ (Γ ⨟ x  ∶ A) ⟶ (Γ ⨟ x'  ∶ A) ]
  p = idr Γ ⋉[ x' , x ] A

  𝓮 : 𝓔 (Γ ⨟ x'  ∶ A) ⊙ Γ' ∋ p ⊚ (𝓼 , 𝓪) ~ (𝓼 , 𝓪)
  𝓮 = subst (λ 𝓼' →
    𝓔 (Γ ⨟ x'  ∶ A) ⊙ Γ' ∋ p ⊚ (𝓼 , 𝓪) ~ (𝓼' , 𝓪))
    (⊚unit 𝓼)
    (renUpdate (idr Γ) 𝓼 𝓪)

----------------------------------------------------------------------
-- Semantics of weakening
----------------------------------------------------------------------
wkSem :
  {Γ Γ' : Cx}
  {A A' : Ty}
  {a : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (q : Γ ⊢ a ∶ A)
  (q' : Γ ⨟ x ∶ A' ⊢ a ∶ A)
  (𝓼 : ∣ 𝓔 Γ ⊙ Γ' ∣)
  (𝓪 : ∣ 𝓓 A' ⊙ Γ' ∣)
  → ------------------------------------
  𝓓 A ⊙ Γ' ∋ ⟦ q' ⟧₀ (𝓼 , 𝓪) ~ ⟦ q ⟧₀ 𝓼

wkSem {Γ}{Γ'}{A}{A'}{a} q q' 𝓼 𝓪 = ~Trans (𝓓 A ⊙ Γ')
  (rnSem (wkrn (idr Γ) A') (𝓼 , 𝓪) q q' (rnUnit a) refl)
  (hom ⟦ q ⟧ ₁ 𝓮)
  where
  e : wkrn (idr Γ) A' ⊚ (𝓼 , 𝓪) ≡ 𝓼
  e rewrite renWk (idr Γ) A' 𝓼 𝓪
    | ⊚unit{Γ} 𝓼  = refl

  𝓮 : 𝓔 Γ ⊙ Γ' ∋ wkrn (idr Γ) A' ⊚ (𝓼 , 𝓪) ~ 𝓼
  𝓮 rewrite renWk (idr Γ) A' 𝓼 𝓪
    | ⊚unit{Γ} 𝓼 = ~Refl (𝓔 Γ ⊙ Γ') 𝓼

----------------------------------------------------------------------
-- Semantics of substitution
----------------------------------------------------------------------
⟦_⟧ˢ :
  {Γ Γ' : Cx}
  {σ : Sb}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  ℝ^[ 𝓔 Γ' ⟶ 𝓔 Γ ]

⟦ ◇ ⟧ˢ        = !^
⟦ [] q₀ q₁ ⟧ˢ = pair^ ⟦ q₀ ⟧ˢ ⟦ q₁ ⟧

⟦_⟧ˢ₀ :
  {Γ Γ' Γ'' : Cx}
  {σ : Sb}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  → ---------------------
  ∣ 𝓔 Γ ⊙ Γ'' ∣

⟦ q ⟧ˢ₀ 𝓼 = hom ⟦ q ⟧ˢ ₀ 𝓼

irrelSemˢ :
  {Γ Γ' Γ'' : Cx}
  {σ σ' : Sb}
  (q : Γ' ⊢ˢ σ ∶ Γ)
  (q' : Γ' ⊢ˢ σ' ∶ Γ)
  (_ : Sb[ Γ ] ∋ σ ~ σ')
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  → --------------------------------
  𝓔 Γ ⊙ Γ'' ∋ ⟦ q ⟧ˢ₀ 𝓼 ~ ⟦ q' ⟧ˢ₀ 𝓼

irrelSemˢ {◇} ◇ ◇ _ _ = tt
irrelSemˢ {_ ⨟ x ∶ _} ([] q₀ q₁) ([] q₀' q₁') e 𝓼 =
  (irrelSemˢ q₀ q₀' (λ x r → e x (∈∪₁ r)) 𝓼
  ,
  irrelSem  q₁ q₁' (e x (∈∪₂ ∈｛｝)) 𝓼)

rnSemˢ :
  {Γ Γ' Γ'' Γ''' : Cx}
  {σ σ' : Sb}
  (p : ℝ[ Γ'' ⟶ Γ' ])
  (𝓼 : ∣ 𝓔 Γ'' ⊙ Γ''' ∣)
  (q : Γ' ⊢ˢ σ ∶ Γ)
  (q' : Γ'' ⊢ˢ σ' ∶ Γ)
  (_ : Sb[ Γ ] ∋ 𝐚∘ (rn p) ∘ˢ σ ~ σ')
  → ---------------------------------------
  𝓔 Γ ⊙ Γ''' ∋ ⟦ q' ⟧ˢ₀ 𝓼 ~ ⟦ q ⟧ˢ₀ (p ⊚ 𝓼)

rnSemˢ {◇} _ _ _ _ _ = tt
rnSemˢ {Γ ⨟ x ∶ _} p 𝓼 ([] q₀ q₁) ([] q₀' q₁') e =
  (rnSemˢ{Γ} p 𝓼 q₀ q₀' (λ x r → e x (∈∪₁ r))
  ,
  rnSem p 𝓼 q₁ q₁' (e x (∈∪₂ ∈｛｝)) refl)

wkSemˢ :
  {Γ Γ' Γ'' : Cx}
  {σ : Sb}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ' ⦄
  (q : Γ' ⊢ˢ σ ∶ Γ)
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (𝓪 : ∣ 𝓓 A ⊙ Γ'' ∣)
  → ------------------------------------------
  𝓔 Γ ⊙ Γ'' ∋ ⟦ wkSb q ⟧ˢ₀ (𝓼 , 𝓪) ~ ⟦ q ⟧ˢ₀ 𝓼

wkSemˢ {Γ}{Γ'}{Γ''}{σ}{A} q 𝓼 𝓪 =
   subst (λ 𝓼' →
     𝓔 Γ ⊙ Γ'' ∋
       ⟦ wkSb q ⟧ˢ₀ (𝓼 , 𝓪) ~ ⟦ q ⟧ˢ₀ 𝓼')
    (trans (renWk (idr Γ') A 𝓼 𝓪) (⊚unit 𝓼))
    (rnSemˢ (wkrn (idr Γ') A) (𝓼 , 𝓪) q
      (wkSb q) (λ x' _ → sbUnit (σ x')))

semˢUnit :
  {Γ Γ' : Cx}
  (𝓼 : ∣ 𝓔 Γ ⊙ Γ' ∣)
  → ---------------------------
  𝓔 Γ ⊙ Γ' ∋ ⟦_⟧ˢ₀{Γ} ⊢idˢ 𝓼 ~ 𝓼

semˢUnit {◇} _ = tt
semˢUnit {Γ ⨟ x ∶ A}{Γ'} (𝓼 , 𝓪) =
  (~begin 𝓔 Γ ⊙ Γ' ∋
     ⟦ rnSb (wkRn ⊢ʳid) ⊢idˢ ⟧ˢ₀ (𝓼 , 𝓪)
   ~⟨ irrelSemˢ (rnSb (wkRn ⊢ʳid) ⊢idˢ)
      (wkSb ⊢idˢ) (λ _ _ → refl ) (𝓼 , 𝓪) ⟩
     ⟦ wkSb ⊢idˢ ⟧ˢ₀ (𝓼 , 𝓪)
   ~⟨ wkSemˢ{Γ} ⊢idˢ 𝓼 𝓪 ⟩
     ⟦_⟧ˢ₀{Γ} ⊢idˢ 𝓼
   ~⟨ semˢUnit{Γ} 𝓼 ⟩
     𝓼
   ~∎)
  ,
  ~Refl (𝓓 A ⊙ Γ') 𝓪

sbSemVar :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x : 𝔸}
  (q : Γ' ⊢ˢ σ ∶ Γ)
  (q' : (x , A) isIn Γ)
  → ------------------------------------------------
  𝓔 Γ' ⟶^ 𝓓 A ∋ ⟦ ⊢sbVar q' q ⟧ ~ val{Γ} q' ∘ ⟦ q ⟧ˢ

sbSemVar {Γ = Γ ⨟ _ ∶ A} ([] _ q) (isInNew refl) {Γ'} 𝓼 =
  ~Refl (𝓓 A ⊙ Γ') (⟦ q ⟧₀ 𝓼)
sbSemVar {Γ = Γ ⨟ _ ∶ A} ([] q _) (isInOld q') =
  sbSemVar{Γ = Γ} q q'

sbSemLift :
  {σ : Sb}
  {Γ Γ' Γ'' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  (q : Γ' ⊢ˢ σ ∶ Γ)
  (q' : Γ' ⨟ x' ∶ A ⊢ˢ (σ ∘/ x := 𝐯 x') ∶ Γ ⨟ x ∶ A)
  (𝓼 : ∣ 𝓔 Γ' ⊙ Γ'' ∣)
  (𝓪 : ∣ 𝓓 A ⊙ Γ'' ∣)
  → ------------------------------------------------------
  𝓔 (Γ ⨟ x ∶ A) ⊙ Γ'' ∋ ⟦ q' ⟧ˢ₀ (𝓼 , 𝓪) ~ (⟦ q ⟧ˢ₀ 𝓼 , 𝓪)

sbSemLift{σ}{Γ}{Γ'}{Γ''}{A}{x}{x'} q q' 𝓼 𝓪 =
  ~Trans (𝓔 (Γ ⨟ x ∶ A) ⊙ Γ'')
    (irrelSemˢ{Γ ⨟ x ∶ A} q'
      (liftSb q)
      (λ _ _ → refl)
      (𝓼 , 𝓪))
    (𝓮₁ , 𝓮₂)
  where
  𝓮₁ :  𝓔 Γ ⊙ Γ'' ∋
    ⟦ ⊢ˢExt (sbUpdate#{a = 𝐯 x'} σ it) (wkSb q) ⟧ˢ₀ (𝓼 , 𝓪)
    ~ ⟦ q ⟧ˢ₀ 𝓼
  𝓮₁ = ~Trans (𝓔 Γ ⊙ Γ'')
    (irrelSemˢ
      (⊢ˢExt (sbUpdate# σ it) (wkSb q))
      (wkSb q)
      (~Symm Sb[ Γ ] (sbUpdate# σ it))
      (𝓼 , 𝓪))
    (wkSemˢ q 𝓼 𝓪)

  𝓮₂ : 𝓓 A ⊙ Γ'' ∋
      ⟦ subst (λ z → Γ' ⨟ x' ∶ A ⊢ z ∶ A)
        (symm (:=Eq{f = σ} x))
        (Var (isInNew refl)) ⟧₀ (𝓼 , 𝓪) ~ 𝓪
  𝓮₂ = irrelSem
    (subst (λ z → Γ' ⨟ x' ∶ A ⊢ z ∶ A)
       (symm (:=Eq{f = σ} x))
        (Var (isInNew refl)))
    (Var (isInNew refl))
    (:=Eq{f = σ} x)
    (𝓼 , 𝓪)

sbSem :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {a : Tm}
  (p : Γ' ⊢ˢ σ ∶ Γ)
  (q : Γ ⊢ a ∶ A)
  → ----------------------------------------
  𝓔 Γ' ⟶^ 𝓓 A ∋ ⟦ sb⊢ p q ⟧ ~ ⟦ q ⟧ ∘ ⟦ p ⟧ˢ

sbSem{σ}{Γ} p (Var{x = x} q)
  rewrite ‿unit (σ x) ⦃ ≤refl ⦄ = sbSemVar{Γ = Γ} p q
sbSem{σ}{Γ}{Γ'} p (Lam{A}{B}{b}{x} q x#) {Γ''} 𝓼 {Γ'''} (r , 𝓪) = 𝓮
  where
  S : Fset𝔸
  S = supp (σ * b , Γ')

  x' : 𝔸
  x' = new S

  x'#b : x' # σ * b
  x'#b = ∉∪₁ (new∉ S)

  instance
    _ : x' # Γ'
    _ = ∉∪₂ (new∉ S)

  p' : Γ' ⨟ x' ∶ A ⊢ˢ (σ ∘/ x := 𝐯 x') ∶ Γ ⨟ x ∶ A
  p' = liftSb p

  q' : Γ' ⨟ x' ∶ A ⊢ (σ * b) [ x' ] ∶ B
  q' = subst (λ c → Γ' ⨟ x' ∶ A ⊢ c ∶ B)
    (sbUpdate[] σ x (𝐯 x') b x#)
    (sb⊢ (liftSb p) q)

  𝓮₁ : 𝓓 B ⊙ Γ''' ∋
      ⟦ q' ⟧₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)
      ~
      ⟦ sb⊢ p' q ⟧₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)
  𝓮₁ = irrelSem
    q'
    (sb⊢ p' q)
    (symm (sbUpdate[] σ x (𝐯 x') b x#))
    (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)

  𝓮₂ : 𝓓 B ⊙ Γ''' ∋
    ⟦ sb⊢ p' q ⟧₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)
    ~
    ⟦ q ⟧₀ (⟦ p' ⟧ˢ₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪))
  𝓮₂ = sbSem p' q (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)

  𝓮₃ : 𝓓 B ⊙ Γ''' ∋
    ⟦ q ⟧₀ (⟦ p' ⟧ˢ₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪))
    ~
    ⟦ q ⟧₀ (⟦ p ⟧ˢ₀ (𝓔 Γ' ⊙′ r ₀ 𝓼) , 𝓪)
  𝓮₃ = hom ⟦ q ⟧ ₁ sbSemLift p p' (𝓔 Γ' ⊙′ r ₀ 𝓼) 𝓪

  𝓮₄ :  𝓓 B ⊙ Γ''' ∋
    ⟦ q ⟧₀ (⟦ p ⟧ˢ₀ (𝓔 Γ' ⊙′ r ₀ 𝓼) , 𝓪)
    ~
    ⟦ q ⟧₀ (𝓔 Γ ⊙′ r ₀ ⟦ p ⟧ˢ₀ 𝓼 , 𝓪)
  𝓮₄ = hom ⟦ q ⟧ ₁ (ntl ⟦ p ⟧ˢ r 𝓼 , ~Refl (𝓓 A ⊙ Γ''') 𝓪)

  𝓮 : 𝓓 B ⊙ Γ''' ∋
      ⟦ q' ⟧₀ (𝓔 Γ' ⊙′ r ₀ 𝓼 , 𝓪)
      ~ ⟦ q ⟧₀ (𝓔 Γ ⊙′ r ₀ ⟦ p ⟧ˢ₀ 𝓼 , 𝓪)
  𝓮 = ~Trans (𝓓 B ⊙ Γ''') 𝓮₁
    (~Trans (𝓓 B ⊙ Γ''') 𝓮₂
      (~Trans (𝓓 B ⊙ Γ''') 𝓮₃ 𝓮₄))

sbSem p (App{A}{B} q₀ q₁) 𝓼 = hom-ev^₁{A}{B}
  (⟦ sb⊢ p q₀ ⟧₀ 𝓼)
  (⟦ q₀ ⟧₀ (⟦ p ⟧ˢ₀ 𝓼))
  (⟦ sb⊢ p q₁ ⟧₀ 𝓼)
  (⟦ q₁ ⟧₀ (⟦ p ⟧ˢ₀ 𝓼))
  (sbSem p q₀ 𝓼)
  (sbSem p q₁ 𝓼)

sbSem _ Zero _ = refl

sbSem{Γ = Γ} p (Succ q) 𝓼
  rewrite sbSem{Γ = Γ} p q 𝓼 = refl

sbSem p (Nrec{C} q₀ q₁ q₂) 𝓼 = nrec₂{C}
  (⟦ sb⊢ p q₂ ⟧₀ 𝓼)
  (⟦ q₂ ⟧₀ (⟦ p ⟧ˢ₀ 𝓼))
  (sbSem p q₀ 𝓼)
  (sbSem p q₁ 𝓼)
  (sbSem p q₂ 𝓼)

----------------------------------------------------------------------
-- Semantics of concretion
----------------------------------------------------------------------
concSem :
  {Γ : Cx}
  {A B : Ty}
  {a : Tm}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q₀ : Γ ⨟ x ∶ A ⊢ b [ x ] ∶ B)
  (q₁ : Γ ⊢ a ∶ A)
  (q₂ : Γ ⊢ b [ a ] ∶ B)
  (x# : x # b)
  → -----------------------------------------------------
  𝓔 Γ ⟶^ 𝓓 B ∋ ⟦ q₀ ⟧ ∘ pair^ (id^ (𝓔 Γ)) ⟦ q₁ ⟧ ~ ⟦ q₂ ⟧

concSem {Γ}{A}{B}{a} b x q₀ q₁ q₂ x#b {Γ'} 𝓼 =
  ~Symm (𝓓 B ⊙ Γ') (~Trans (𝓓 B ⊙ Γ')
    (irrelSem
      q₂
      (sb⊢ ([]' ⊢idˢ q₁) q₀)
      (symm (ssb[] x a b x#b))
      𝓼)
    (~Trans (𝓓 B ⊙ Γ')
    (sbSem ([]' ⊢idˢ q₁) q₀ 𝓼)
    (hom ⟦ q₀ ⟧ ₁ (
      ~Trans (𝓔 Γ ⊙ Γ')
        (irrelSemˢ
          (⊢ˢExt (sbUpdate# idˢ it) ⊢idˢ)
          ⊢idˢ
          (~Symm Sb[ Γ ] (sbUpdate# idˢ it))
          𝓼)
        (semˢUnit{Γ} 𝓼)
    ,
    irrelSem (subst (λ z → Γ ⊢ z ∶ A) (symm (:=Eq x)) q₁)
      q₁
      (:=Eq x)
      𝓼))))

module MLTT.Substitution where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.Cofinite
open import MLTT.Ok
open import MLTT.WellScoped
open import MLTT.Weakening

----------------------------------------------------------------------
-- Weakening substitutions
----------------------------------------------------------------------
▷Sb :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ : Sb}
  {A : Ty}
  (x : 𝔸)
  (_ : Γ' ⊢ A ⦂ l)
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : x # Γ')
  → -----------------------
  (Γ' ⨟ x ∶ A ⦂ l)⊢ˢ σ ∶ Γ

▷Sb x q (◇ˢ q') q'' = ◇ˢ (ok⨟ q q'' q')
▷Sb x q (⨟ˢ q₀ q₁ q₂ q₃) q' =
  ⨟ˢ (▷Sb x q q₀ q') q₁ (▷Jg (proj q q') q₂)  q₃

▷＝Sb :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  (x : 𝔸)
  (_ : Γ' ⊢ A ⦂ l)
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : x # Γ')
  → ----------------------------
  (Γ' ⨟ x ∶ A ⦂ l)⊢ˢ σ ＝ σ' ∶ Γ

▷＝Sb x q (＝◇ˢ q') q'' = ＝◇ˢ (ok⨟ q q'' q')
▷＝Sb x q (＝⨟ˢ q₀ q₁ q₂ q₃) q' =
  ＝⨟ˢ (▷＝Sb x q q₀ q') q₁ (▷Jg (proj q q') q₂)  q₃

----------------------------------------------------------------------
-- Identity substitution is well-typed
----------------------------------------------------------------------
⊢idˢ :
  {Γ : Cx}
  (_ : Ok Γ)
  → ---------
  Γ ⊢ˢ idˢ ∶ Γ

⊢idˢ ok◇ = ◇ˢ ok◇
⊢idˢ (ok⨟{l}{Γ}{A}{x} q q' q'') = ⨟ˢ
  (▷Sb _ q (⊢idˢ q'') q')
  q
  (⊢𝐯 (ok⨟⁻ q q') (subst (λ A' → (x , A' , l) isIn (Γ ⨟ x ∶ A ⦂ l))
    (symm (sbUnit A))
    isInNew))
  q'

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

sbExt (◇ˢ q) _ = ◇ˢ q
sbExt{σ}{σ'} (⨟ˢ{A = A}{x} q₀ q₁ q₂ q₃) e
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ (∈∪₁ p'))))
  | e x (∈∪₂ ∈｛｝) = ⨟ˢ (sbExt q₀ (λ y r → e y (∈∪₁ r))) q₁ q₂ q₃

sb＝Ext :
  {σ' τ' σ τ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ＝ τ ∶ Γ)
  (_ : ∀ x → x ∈ dom Γ → σ x ≡ σ' x)
  (_ : ∀ x → x ∈ dom Γ → τ x ≡ τ' x)
  → --------------------------------
  Γ' ⊢ˢ σ' ＝ τ' ∶ Γ

sb＝Ext (＝◇ˢ q) _ _ = ＝◇ˢ q
sb＝Ext{σ'}{τ'} (＝⨟ˢ{σ = σ}{τ}{A = A}{x} q₀ q₁ q₂ q₃) e e'
  rewrite sbRespSupp σ σ' A (λ x' p' → e x' (∈∪₁ (⊢supp q₁ (∈∪₁ p'))))
  | e x (∈∪₂ ∈｛｝)
  | e' x (∈∪₂ ∈｛｝)= ＝⨟ˢ
    (sb＝Ext q₀ (λ y r → e y (∈∪₁ r)) (λ y' r' → e' y' (∈∪₁ r')))
    q₁
    q₂
    q₃

----------------------------------------------------------------------
-- Lifting substitutions
----------------------------------------------------------------------
liftSb :
  {l : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : x # Γ)
  (_ : x' # Γ')
  -- helper hypothesis
  (_ : Γ' ⊢ σ * A ⦂ l)
  → --------------------------------------------------------
  (Γ' ⨟ x' ∶ σ * A ⦂ l)⊢ˢ (σ ∘/ x := 𝐯 x') ∶ (Γ ⨟ x ∶ A ⦂ l)

liftSb{l}{σ}{Γ}{Γ'}{A}{x}{x'} ⊢σ ⊢A x#Γ x'#Γ' ⊢σA =
  ⨟ˢ (▷Sb x' ⊢σA ⊢σ' x'#Γ') ⊢A ⊢A' x#Γ
  where
  ⊢σ' : Γ' ⊢ˢ (σ ∘/ x := 𝐯 x') ∶ Γ
  ⊢σ' = sbExt ⊢σ (λ y r →
    symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ x#Γ r }))

  ⊢A' : (Γ' ⨟ x' ∶ σ * A ⦂ l)⊢
    (σ ∘/ x := 𝐯 x') x ∶ (σ ∘/ x := 𝐯 x') * A ⦂ l
  ⊢A' rewrite updateFresh σ x (𝐯 x') A (∉∪₁ (⊢# ⊢A x#Γ))
      | :=Eq{f = σ}{𝐯 x'} x = ⊢𝐯 (ok⨟⁻ ⊢σA x'#Γ') isInNew

-- Iterated lifting
liftSb² :
  {l l' : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  {x y x' y' : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : (Γ ⨟ x ∶ A ⦂ l)⊢ B ⦂ l')
  (_ : x' # Γ')
  (_ : y # (Γ , x))
  (_ : y' # (Γ' , x'))
  (_ : σ * A ≡ A')
  (_ : (σ ∘/ x := 𝐯 x') * B ≡ B')
  -- helper hypotheses
  (_ : Γ' ⊢ A' ⦂ l)
  (_ : (Γ' ⨟ x' ∶ A' ⦂ l) ⊢ B' ⦂ l')
  → -------------------------------------------------------------
  (Γ' ⨟ x' ∶ A' ⦂ l ⨟ y' ∶ B' ⦂ l') ⊢ˢ
    ((σ ∘/ x := 𝐯 x') ∘/ y := 𝐯 y')∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l')

liftSb² q₀ q₁ q₂ q₃ q₄ q₅ refl refl h h' =
  liftSb (liftSb q₀ q₁ (π₁ ([]⁻¹ (⊢ok q₂))) q₃ h) q₂ q₄ q₅ h'

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
  Γ' ⊢ σ x ∶ σ * A ⦂ l

sbVar (⨟ˢ _ _ q _)  isInNew     = q
sbVar (⨟ˢ q _ _ _) (isInOld q') = sbVar q q'

sbVar＝ :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_  : (x , A , l) isIn Γ)
  → --------------------------
  Γ' ⊢ σ x ＝ σ' x ∶ σ * A ⦂ l

sbVar＝ (＝⨟ˢ _ _ q _)  isInNew     = q
sbVar＝ (＝⨟ˢ q _ _ _) (isInOld q') = sbVar＝ q q'

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
  {Δ Γ : Cx}
  {J : Jg}
  (_ : Δ ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ J)
  → --------------
  Δ ⊢ σ * J

sbJg p (⊢conv q₀ q₁) = ⊢conv
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ} p (⊢𝐯{x = x} _ q)
  rewrite ‿unit (σ x) ⦃ it ⦄ = sbVar p q

sbJg p (⊢𝐔 _) = ⊢𝐔 (okSb p)

sbJg{σ}{Δ} p (⊢𝚷{l}{l'}{A = A}{B} S q₀ q₁) = ⊢𝚷
  (S ∪ supp (Δ , B))
  (sbJg p q₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#B) →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p q₀ (π₁ ([]⁻¹(⊢ok (q₁ x x#S)))) x#Δ (sbJg p q₀))
        (q₁ x x#S))}

sbJg{σ}{Δ} p (⊢𝛌{l}{l'}{A = A}{B}{b} S q₀ h₀ h₁) = ⊢𝛌
  (S ∪ supp (Δ , B , b))
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst₂ (λ b' B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ b' ∶ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) b x#b)
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (q₀ x x#S))})
  (sbJg p h₀)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))})

sbJg{σ}{Δ} p (⊢∙{l}{l'}{A = A}{B = B}{a}{b} S q₀ q₁ q₂ h)
  rewrite sb[] σ B a = ⊢∙
  (S ∪ supp (Δ , B))
  (sbJg p q₀)
  (sbJg p q₁)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B) →
    subst (λ C → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ C ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h (π₁ ([]⁻¹(⊢ok (q₂ x x#S)))) x#Δ (sbJg p h))
        (q₂ x x#S))})
  (sbJg p h)

sbJg p (⊢𝐈𝐝 q₀ q₁ h) = ⊢𝐈𝐝
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p h)

sbJg p (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐫𝐞𝐟𝐥
  (sbJg p q)
  (sbJg p h)

sbJg{σ}{Δ} p (⊢𝐉{l}{l'}{A}{C}{a}{b}{c}{e} S q₀ q₁ q₂ q₃ q₄ h₀ h₁)
  rewrite sb[]² σ C b e = ⊢𝐉{l = l}{l'}{A = σ * A}{σ * C}
  (S ∪ supp (Δ , C))
  (λ{x y (##:: (y#S ∉∪ y#Δ ∉∪ y#C)
           (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C) ##◇)) →
    subst (λ C' →
      (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝 (σ * A) (σ * a) (𝐯 x) ⦂ l) ⊢ C' ⦂ l')
      (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ (#symm x#y)))
      (sbJg
        (liftSb² p h₀ (h₁ x x#S) x#Δ
          ((π₁ ([]⁻¹(⊢ok (h₁ y y#S)))) ∉∪ #symm x#y)
          (y#Δ ∉∪ (#symm x#y)) refl (eq x x#S x#Δ x#C) (sbJg p h₀)
          (h₁' x x#S x#Δ x#C))
        (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))})
  (sbJg p q₁)
  (sbJg p q₂)
  (subst (λ C' → Δ ⊢ σ * c ∶ C' ⦂ l')
    (sb[]² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₃))
  (sbJg p q₄)
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C) → h₁' x x#S x#Δ x#C}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)
    where
    eq : (σ ∘/ x := 𝐯 x) * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x)
    eq rewrite  updateFresh σ x (𝐯 x) A
                (∉∪₂ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
       | updateFresh σ x (𝐯 x) a (∉∪₁
         (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
       | :=Eq{f = σ}{𝐯 x} x = refl

    h₁' : (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l
    h₁' = subst (λ I → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ I ⦂ l)
      eq
      (sbJg
        (liftSb p h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))

sbJg p (⊢𝐍𝐚𝐭 _) = ⊢𝐍𝐚𝐭 (okSb p)

sbJg p (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (okSb p)

sbJg p (⊢𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (sbJg p q)

sbJg{σ}{Δ} p (⊢𝐧𝐫𝐞𝐜{l}{C}{c₀}{a}{c₊} S q₀ q₁ q₂ h)
  rewrite sb[] σ C a = ⊢𝐧𝐫𝐞𝐜
  (S ∪ supp (Δ , C , c₊))
  (subst (λ C' → Δ ⊢ σ * c₀ ∶ C' ⦂ l)
    (sb[] σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀))
  (λ{x y (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#c₊)
           (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) ##◇))
     → q₁' x x#S x#Δ x#C x#c₊ y y#S y#Δ y#C y#c₊ x#y})
  (sbJg p q₂)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) → h' x x#S x#Δ x#C x#c₊}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)(x#c₊ : x # c₊)
    where
    h' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ⦂ l
    h' = subst (λ C' → (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (π₁ ([]⁻¹(⊢ok (h x x#S)))) x#Δ
        (⊢𝐍𝐚𝐭 (okSb p))) (h x x#S))

    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)(y#C : y # C)
      (y#c₊ : y # c₊)(x#y : x # y)
      where
      eq' : ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y)* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
        (σ * C)[ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
      eq' rewrite sb[] ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y) C (𝐬𝐮𝐜𝐜 (𝐯 x))
           | updateFresh ((σ ∘/ x := 𝐯 x)) y (𝐯 y) C y#C
           | updateFresh σ x (𝐯 x) C x#C
           | :=Neq{f = (σ ∘/ x := 𝐯 x)}{𝐯 y} y x
              (λ{refl → ∉→¬∈ (∉∪₂
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: x#S (##:: (x#y ∉∪ y#S) ##◇)))))))
              (∈｛｝)})
           | :=Eq{f = σ}{𝐯 x} x = refl

      q₁' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢
        (σ * c₊)[ x ][ y ] ∶ (σ * C) [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
      q₁' = subst₂ (λ c' C' →
        (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢ c' ∶ C' ⦂ l)
          (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊  x#c₊ (y#c₊ ∉∪ (#symm x#y)))
          eq'
          (sbJg
            (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (h x x#S) x#Δ
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))))
              (y#Δ ∉∪ (#symm x#y))
              refl
              (sbUpdate[] σ x (𝐯 x) C x#C)
              (⊢𝐍𝐚𝐭(okSb p)) h')
            (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))

sbJg p (Refl q) = Refl (sbJg p q)

sbJg p (Symm q) = Symm (sbJg p q)

sbJg p (Trans q₀ q₁) = Trans (sbJg p q₀) (sbJg p q₁)

sbJg p (＝conv q q₁) = ＝conv (sbJg p q) (sbJg p q₁)

sbJg{σ}{Δ} p (𝚷Cong{l}{l'}{A}{A'}{B}{B'} S q₀ q₁ h) = 𝚷Cong
  (S ∪ supp (Δ , B , B'))
  (sbJg p q₀)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#B') →
    subst₂ (λ C C' → Δ ⨟ x ∶ σ * A ⦂ l ⊢ C ＝ C' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbUpdate[] σ x (𝐯 x) B' x#B')
      (sbJg
        (liftSb p h (π₁([]⁻¹(⊢ok (q₁ x x#S)))) x#Δ (sbJg p h))
        (q₁ x x#S))})
  (sbJg p h)

sbJg{σ}{Δ} p (𝛌Cong{l}{l'}{A}{A'}{B}{b}{b'} S q₀ q₁ h₀ h₁) = 𝛌Cong
  (S ∪ supp (Δ , B , b , b'))
  (sbJg p q₀)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b ∉∪ x#b') →
    subst₃ (λ c c' C → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ c ＝ c' ∶ C ⦂ l')
      (sbUpdate[] σ x (𝐯 x) b x#b)
      (sbUpdate[] σ x (𝐯 x) b' x#b')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (q₁ x x#S))})
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b ∉∪ x#b') →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
    (sbUpdate[] σ x (𝐯 x) B x#B)
    (sbJg
        (liftSb p h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))}

sbJg{σ}{Δ} p (∙Cong{l}{l'}{A}{A'}{B}{B'}{a}{a'}{b}{b'}
  S q₀ q₁ q₂ q₃ h₀ h₁)
  rewrite sb[] σ B a = ∙Cong
  (S ∪ supp (Δ , B , B'))
  (sbJg p q₀)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#B') →
    subst₂ (λ C C' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ C ＝ C' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbUpdate[] σ x (𝐯 x) B' x#B')
      (sbJg
        (liftSb p h₀ ((π₁([]⁻¹(⊢ok (h₁ x x#S))))) x#Δ (sbJg p h₀))
        (q₁ x x#S))})
  (sbJg p q₂)
  (sbJg p q₃)
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#B') →
    subst (λ C → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ C ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ ((π₁([]⁻¹(⊢ok (h₁ x x#S))))) x#Δ (sbJg p h₀))
        (h₁ x x#S))}

sbJg p (𝐈𝐝Cong q₀ q₁ q₂) = 𝐈𝐝Cong
  (sbJg p q₀)
  (sbJg p q₁)
  (sbJg p q₂)

sbJg p (𝐫𝐞𝐟𝐥Cong q₀ q₁) = 𝐫𝐞𝐟𝐥Cong
  (sbJg p q₀)
  (sbJg p q₁)

sbJg{σ}{Δ} p (𝐉Cong{l}{l'}{A}{C}{C'}{a}{a'}{b}{b'}{c}{c'}{e}{e'}
  S q₀ q₁ q₂ q₃ q₄ h₀ h₁)
  rewrite sb[]² σ C b e = 𝐉Cong{l = l}{l'}{σ * A}
  (S ∪ supp (Δ , C , C'))
  (λ{x y
    (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#C')
    (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#C') ##◇)) →
    subst₂ (λ D D' →
      (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l) ⊢ D ＝ D' ⦂ l')
        (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ #symm x#y))
        (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C' x#C' (y#C' ∉∪ #symm x#y))
        (sbJg
          (liftSb² p h₀ (h₁ x x#S) x#Δ
            ((π₁ ([]⁻¹(⊢ok (h₁ y y#S)))) ∉∪ #symm x#y)
            (y#Δ ∉∪ (#symm x#y)) refl (eq x x#S x#Δ x#C x#C') (sbJg p h₀)
            (h₁' x x#S x#Δ x#C x#C'))
          (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))})
  (sbJg p q₁)
  (sbJg p q₂)
  (subst (λ C' → Δ ⊢ σ * c ＝ σ * c' ∶ C' ⦂ l')
    (sb[]² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₃))
  (sbJg p q₄)
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#C') → h₁' x x#S x#Δ x#C x#C'}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)(x#C' : x # C')
    where
    eq : (σ ∘/ x := 𝐯 x) * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x)
    eq rewrite  updateFresh σ x (𝐯 x) A
                (∉∪₂ (∉∪₂ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))))))
      | updateFresh σ x (𝐯 x) a (∉∪₁ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
      | :=Eq{f = σ}{𝐯 x} x = refl

    h₁' : (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l
    h₁' = subst (λ I → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ I ⦂ l)
      eq
      (sbJg
        (liftSb p h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))
    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)
      (y#C : y # C)(y#C' : y # C')(x#y : x # y)
      where
      q₀' : (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l) ⊢
        (σ * C) [ x ][ y ] ＝ (σ * C') [ x ][ y ] ⦂ l'
      q₀' = subst₂ (λ D D' →
        (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l) ⊢ D ＝ D' ⦂ l')
          (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ #symm x#y))
          (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C' x#C' (y#C' ∉∪ #symm x#y))
          (sbJg
            (liftSb² p h₀ (h₁ x x#S) x#Δ
              ((π₁ ([]⁻¹(⊢ok (h₁ y y#S)))) ∉∪ #symm x#y)
              (y#Δ ∉∪ (#symm x#y)) refl eq (sbJg p h₀) h₁')
            (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))

sbJg p (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (sbJg p q)

sbJg{σ}{Δ} p (𝐧𝐫𝐞𝐜Cong{l}{C}{C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}
  S q₀ q₁ q₂ q₃ h)
  rewrite sb[] σ C a = 𝐧𝐫𝐞𝐜Cong
  (S ∪ supp (Δ , C , C' , c₊ , c₊'))
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#C' ∉∪ x#c₊ ∉∪ x#c₊') →
    q₀' x x#S x#Δ x#C x#C' x#c₊ x#c₊'})
  (subst (λ D → Δ ⊢ σ * c₀ ＝ σ * c₀' ∶ D ⦂ l)
    (sb[] σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₁))
  (λ{x y
    (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#C' ∉∪ y#c₊ ∉∪ y#c₊')
    (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#C' ∉∪ x#c₊ ∉∪ x#c₊') ##◇)) →
    q₂' x x#S x#Δ x#C x#C' x#c₊ x#c₊' y y#S y#Δ y#C y#C' y#c₊ y#c₊' x#y})
  (sbJg p q₃)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#C' ∉∪ x#c₊ ∉∪ x#c₊') →
    h' x x#S x#Δ x#C x#C' x#c₊ x#c₊'}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)
    (x#C : x # C)(x#C' : x # C')
    (x#c₊ : x # c₊)(x#c₊' : x # c₊')
    where
    h' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ⦂ l
    h' = subst (λ C' → (Δ  ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₁)) (π₁ ([]⁻¹(⊢ok (h x x#S)))) x#Δ
        (⊢𝐍𝐚𝐭 (okSb p))) (h x x#S))
    q₀' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ＝ (σ * C') [ x ] ⦂ l
    q₀' = subst₂ (λ D D' → (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ D ＝ D' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbUpdate[] σ x (𝐯 x) C' x#C')
      (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (π₁ ([]⁻¹(⊢ok (h x x#S)))) x#Δ
      (⊢𝐍𝐚𝐭 (okSb p))) (q₀ x x#S))
    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)
      (y#C : y # C)(y#C' : y # C')
      (y#c₊ : y # c₊)(y#c₊' : y # c₊')
      (x#y : x # y)
      where
      eq' : ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y)* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
        (σ * C)[ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
      eq' rewrite sb[] ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y) C (𝐬𝐮𝐜𝐜 (𝐯 x))
           | updateFresh ((σ ∘/ x := 𝐯 x)) y (𝐯 y) C y#C
           | updateFresh σ x (𝐯 x) C x#C
           | :=Neq{f = (σ ∘/ x := 𝐯 x)}{𝐯 y} y x
             (λ{refl → ≠𝔸irrefl (∉｛｝⁻¹ x#y)})
           | :=Eq{f = σ}{𝐯 x} x = refl

      q₂' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0  ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢
        (σ * c₊)[ x ][ y ] ＝ (σ * c₊')[ x ][ y ] ∶ (σ * C) [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
      q₂' = subst₃ (λ d d' D →
        (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C) [ x ] ⦂ l) ⊢ d ＝ d' ∶ D ⦂ l)
        (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊ x#c₊ (y#c₊ ∉∪ #symm x#y))
        (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊' x#c₊' (y#c₊' ∉∪ #symm x#y))
        eq'
        (sbJg
          (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₃)) (h x x#S) x#Δ
            (π₁([]⁻¹(⊢ok (q₂ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))))
            (y#Δ ∉∪ #symm x#y) refl
            (sbUpdate[] σ x (𝐯 x) C x#C)
            (⊢𝐍𝐚𝐭(okSb p)) h')
          (q₂ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))

sbJg{σ}{Δ} p (𝚷Beta{l}{l'}{A}{a}{B}{b} S q₀ q₁ h₀ h₁)
  rewrite sb[] σ b a
  | sb[] σ B a = 𝚷Beta
  (S ∪ supp (Δ , B , b))
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst₂ (λ b' B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ b' ∶ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) b x#b)
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (q₀ x x#S))})
  (sbJg p q₁)
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))}

sbJg{σ}{Δ} p (𝐈𝐝Beta{l}{l'}{A}{C}{a}{c} S q₀ q₁ q₂ h₀ h₁)
  rewrite sb[]² σ C a (𝐫𝐞𝐟𝐥 a) = 𝐈𝐝Beta
  (S ∪ supp (Δ , C))
  (λ{x y (##:: (y#S ∉∪ y#Δ ∉∪ y#C)
           (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C) ##◇)) →
    subst (λ C' →
      (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝 (σ * A) (σ * a) (𝐯 x) ⦂ l) ⊢ C' ⦂ l')
      (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ (#symm x#y)))
      (sbJg
        (liftSb² p h₀ (h₁ x x#S) x#Δ
          ((π₁ ([]⁻¹(⊢ok (h₁ y y#S)))) ∉∪ #symm x#y)
          (y#Δ ∉∪ (#symm x#y)) refl (eq x x#S x#Δ x#C) (sbJg p h₀)
          (h₁' x x#S x#Δ x#C))
        (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))})
  (sbJg p q₁)
  (subst (λ C' → Δ ⊢ σ * c ∶ C' ⦂ l')
    (sb[]² σ C a (𝐫𝐞𝐟𝐥 a))
    (sbJg p q₂))
  (sbJg p h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C) → h₁' x x#S x#Δ x#C}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)
    where
    eq : (σ ∘/ x := 𝐯 x) * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x)
    eq rewrite  updateFresh σ x (𝐯 x) A
                (∉∪₂ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
      | updateFresh σ x (𝐯 x) a (∉∪₁ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
      | :=Eq{f = σ}{𝐯 x} x = refl

    h₁' : (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l
    h₁' = subst (λ I → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ I ⦂ l)
      eq
      (sbJg
        (liftSb p h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg p h₀))
        (h₁ x x#S))

sbJg{σ}{Δ} p (𝐍𝐚𝐭Beta₀{l}{C}{c₀}{c₊} S q₀ q₁ h)
  rewrite sb[] σ C 𝐳𝐞𝐫𝐨 = 𝐍𝐚𝐭Beta₀
  (S ∪ supp (Δ , C , c₊))
  (subst (λ C' → Δ ⊢ σ * c₀ ∶ C' ⦂ l)
    (sb[] σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀))
  (λ{x y (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#c₊)
           (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) ##◇))
     → q₁' x x#S x#Δ x#C x#c₊ y y#S y#Δ y#C y#c₊ x#y})
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) → h' x x#S x#Δ x#C x#c₊}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)(x#c₊ : x # c₊)
    where
    h' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ⦂ l
    h' = subst (λ C' → (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (π₁ ([]⁻¹(⊢ok (h x x#S)))) x#Δ
        (⊢𝐍𝐚𝐭 (okSb p))) (h x x#S))

    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)(y#C : y # C)
      (y#c₊ : y # c₊)(x#y : x # y)
      where
      eq' : ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y)* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
        (σ * C)[ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
      eq' rewrite sb[] ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y) C (𝐬𝐮𝐜𝐜 (𝐯 x))
           | updateFresh ((σ ∘/ x := 𝐯 x)) y (𝐯 y) C y#C
           | updateFresh σ x (𝐯 x) C x#C
           | :=Neq{f = (σ ∘/ x := 𝐯 x)}{𝐯 y} y x
              (λ{refl → ∉→¬∈ (∉∪₂
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: x#S (##:: (x#y ∉∪ y#S) ##◇)))))))
              (∈｛｝)})
           | :=Eq{f = σ}{𝐯 x} x = refl

      q₁' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢
        (σ * c₊)[ x ][ y ] ∶ (σ * C) [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
      q₁' = subst₂ (λ c' C' →
        (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢ c' ∶ C' ⦂ l)
          (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊ x#c₊ (y#c₊ ∉∪ (#symm x#y)))
          eq'
          (sbJg
            (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (h x x#S) x#Δ
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))))
              (y#Δ ∉∪ (#symm x#y))
              refl
              (sbUpdate[] σ x (𝐯 x) C x#C)
              (⊢𝐍𝐚𝐭(okSb p)) h')
            (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))

sbJg{σ}{Δ} p (𝐍𝐚𝐭Beta₊{l}{C}{c₀}{a}{c₊} S q₀ q₁ q₂ h)
  rewrite sb[]² σ c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a)
  | sb[] σ C (𝐬𝐮𝐜𝐜 a) = 𝐍𝐚𝐭Beta₊
  (S ∪ supp (Δ , C , c₊))
  (subst (λ C' → Δ ⊢ σ * c₀ ∶ C' ⦂ l)
    (sb[] σ C 𝐳𝐞𝐫𝐨)
    (sbJg p q₀))
  (λ{x y (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#c₊)
           (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) ##◇))
     → q₁' x x#S x#Δ x#C x#c₊ y y#S y#Δ y#C y#c₊ x#y})
  (sbJg p q₂)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) → h' x x#S x#Δ x#C x#c₊}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C)(x#c₊ : x # c₊)
    where
    h' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ⦂ l
    h' = subst (λ C' → (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbJg (liftSb p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (π₁ ([]⁻¹(⊢ok (h x x#S)))) x#Δ
        (⊢𝐍𝐚𝐭 (okSb p))) (h x x#S))

    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)(y#C : y # C)
      (y#c₊ : y # c₊)(x#y : x # y)
      where
      eq' : ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y)* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
        (σ * C)[ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
      eq' rewrite sb[] ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y) C (𝐬𝐮𝐜𝐜 (𝐯 x))
           | updateFresh ((σ ∘/ x := 𝐯 x)) y (𝐯 y) C y#C
           | updateFresh σ x (𝐯 x) C x#C
           | :=Neq{f = (σ ∘/ x := 𝐯 x)}{𝐯 y} y x
              (λ{refl → ∉→¬∈ (∉∪₂
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: x#S (##:: (x#y ∉∪ y#S) ##◇)))))))
              (∈｛｝)})
           | :=Eq{f = σ}{𝐯 x} x = refl

      q₁' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢
        (σ * c₊)[ x ][ y ] ∶ (σ * C) [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
      q₁' = subst₂ (λ c' C' →
        (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢ c' ∶ C' ⦂ l)
          (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊ x#c₊ (y#c₊ ∉∪ (#symm x#y)))
          eq'
          (sbJg
            (liftSb² p (⊢𝐍𝐚𝐭 (⊢ok q₀)) (h x x#S) x#Δ
              (π₁([]⁻¹(⊢ok (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))))
              (y#Δ ∉∪ (#symm x#y))
              refl
              (sbUpdate[] σ x (𝐯 x) C x#C)
              (⊢𝐍𝐚𝐭(okSb p)) h')
            (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇))))

sbJg{σ}{Δ} p (𝚷Eta{l}{l'}{A}{B}{b}{b'} S q₀ q₁ q₂ h) = 𝚷Eta
  (S ∪ supp Δ)
  (sbJg p q₀)
  (sbJg p q₁)
  (λ{x (x#S ∉∪ x#Δ) → q₂' x x#S x#Δ})
  (sbJg p h)
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ) where
    x#Γ =  π₁ ([]⁻¹(⊢ok (q₂ x x#S)))
    x#b = ∉∪₁ (⊢# q₀ x#Γ)
    x#b' = ∉∪₁ (⊢# q₁ x#Γ)
    x#A = ∉∪₁ (∉∪₂ (⊢# q₀ x#Γ))
    x#B = ∉∪₁ (∉∪₂ (∉∪₂ (⊢# q₀ x#Γ)))

    eq : ∀ c → x # c → (σ ∘/ x := 𝐯 x) * (c ∙[ A , B ] 𝐯 x) ≡
      (σ * c) ∙[ σ * A , σ * B ] (𝐯 x)
    eq c x#c
      rewrite updateFresh σ x (𝐯 x) c x#c
      | updateFresh σ x (𝐯 x) A x#A
      | updateFresh σ x (𝐯 x) B x#B
      | :=Eq{f = σ}{𝐯 x} x = refl

    q₂' : (Δ ⨟ x ∶ σ * A ⦂ l) ⊢
      (σ * b)  ∙[ σ * A , σ * B ] (𝐯 x) ＝
      (σ * b') ∙[ σ * A , σ * B ] (𝐯 x) ∶ (σ * B) [ x ] ⦂ l'
    q₂' = subst₃ (λ c c' C → Δ ⨟ x ∶ σ * A ⦂ l ⊢ c ＝ c' ∶ C ⦂ l')
      (eq b x#b)
      (eq b' x#b')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb p h x#Γ x#Δ (sbJg p h))
        (q₂ x x#S))

----------------------------------------------------------------------
-- Conversion for substitutions is reflexive
----------------------------------------------------------------------
sb＝Refl :
  {σ : Sb}
  {Γ Γ' : Cx}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → ---------------
  Γ' ⊢ˢ σ ＝ σ ∶ Γ

sb＝Refl (◇ˢ q) = ＝◇ˢ q
sb＝Refl (⨟ˢ q₀ q₁ q₂ q₃) = ＝⨟ˢ (sb＝Refl q₀) q₁ (Refl q₂) q₃

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
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ' ⊢ a ∶ σ * A ⦂ l)
  (_ : x # Γ)
  -- helper hypothesis
  (_ : Γ ⊢ A ⦂ l)
  → -----------------------------------
  Γ' ⊢ˢ (σ ∘/ x := a) ∶ (Γ ⨟ x ∶ A ⦂ l)

sbUpdate{l}{Γ' = Γ'}{σ}{A}{a}{x} ⊢σ ⊢a x#Γ ⊢A = ⨟ˢ
  (sbExt ⊢σ (λ y r →
    symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ x#Γ r })))
  ⊢A
  (subst₂ (λ z Z → Γ' ⊢ z ∶ Z ⦂ l)
    (symm (:=Eq{f = σ}{a} x))
    (symm (updateFresh σ x a A (∉∪₁ (⊢# ⊢A x#Γ))))
    ⊢a)
  x#Γ

sb＝Update :
  {l : Lvl}
  {Γ Γ' : Cx}
  {σ σ' : Sb}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ' ⊢ a ＝ a' ∶ σ * A ⦂ l)
  (_ : x # Γ)
  -- helper hypothesis
  (_ : Γ ⊢ A ⦂ l)
  → ------------------------------------------------------
  Γ' ⊢ˢ (σ ∘/ x := a) ＝ (σ' ∘/ x := a') ∶ (Γ ⨟ x ∶ A ⦂ l)

sb＝Update{l}{Γ' = Γ'}{σ}{σ'}{A}{a}{a'}{x} σ=σ' a=a' x#Γ ⊢A = ＝⨟ˢ
  (sb＝Ext σ=σ'
    (λ y r →
      symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ x#Γ r }))
    (λ y r →
      symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ x#Γ r })))
  ⊢A
  (subst₃ (λ z z' Z → Γ' ⊢ z ＝ z' ∶ Z ⦂ l)
    (symm (:=Eq{f = σ}{a} x))
    (symm (:=Eq{f = σ'}{a'} x))
    (symm (updateFresh σ x a A (∉∪₁ (⊢# ⊢A x#Γ))))
    a=a')
  x#Γ

ssbUpdate :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : x # Γ)
  -- helper hypothesis
  (_ : Γ ⊢ A ⦂ l)
  → -----------------------------
  Γ ⊢ˢ (x := a) ∶ (Γ ⨟ x ∶ A ⦂ l)

ssbUpdate{l}{Γ}{A}{a} q x#Γ h = sbUpdate
  (⊢idˢ (⊢ok q))
  (subst (λ A' → Γ ⊢ a ∶ A' ⦂ l) (symm (sbUnit A)) q)
  x#Γ
  h

ssb＝Update :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  {x : 𝔸}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : x # Γ)
  -- helper hypothesis
  (_ : Γ ⊢ A ⦂ l)
  → ------------------------------------------
  Γ ⊢ˢ (x := a) ＝ (x := a') ∶ (Γ ⨟ x ∶ A ⦂ l)

ssb＝Update{l}{Γ}{A}{a}{a'} q x#Γ h = sb＝Update
  (sb＝Refl (⊢idˢ (⊢ok q)))
  (subst (λ A' → Γ ⊢ a ＝ a' ∶ A' ⦂ l) (symm (sbUnit A)) q)
  x#Γ
  h

ssbUpdate² :
  {l l' : Lvl}
  {Γ : Cx}
  {x y : 𝔸}
  {a b : Tm}
  {A B : Ty}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
  (_ : Γ ⊢ b ∶ (x := a) * B ⦂ l')
  (_ : y # (Γ , x))
  → ----------------------------------------------------
  Γ ⊢ˢ (x := a ∘/ y := b) ∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l')

ssbUpdate² q₀ q₁ q₂ q₃
  with ok⨟ q q' _ ← ⊢ok q₁ =
  sbUpdate (ssbUpdate q₀ q' q) q₂ q₃ q₁

ssb＝Update² :
  {l l' : Lvl}
  {Γ : Cx}
  {x y : 𝔸}
  {a a' b b' : Tm}
  {A  B : Ty}
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
  (_ : Γ ⊢ b ＝ b' ∶ (x := a) * B ⦂ l')
  (_ : y # (Γ , x))
  → ---------------------------------------------
  Γ ⊢ˢ (x := a ∘/ y := b) ＝ (x := a' ∘/ y := b')
    ∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l')

ssb＝Update² q₀ q₁ q₂ q₃
  with ok⨟ q q' _ ← ⊢ok q₁ =
  sb＝Update (ssb＝Update q₀ q' q) q₂ q₃ q₁

----------------------------------------------------------------------
-- Lifting substitutions, again
----------------------------------------------------------------------
liftSb⁻ :
  {l : Lvl}
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : x # Γ)
  (_ : x' # Γ')
  → ---------------------------------------------------------
  (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢ˢ (σ ∘/ x := 𝐯 x') ∶ (Γ ⨟ x ∶ A ⦂ l)

liftSb⁻ q₀ q₁ q₂ q₃ = liftSb q₀ q₁ q₂ q₃ (sbJg q₀ q₁)

lift＝Sb :
  {l : Lvl}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : x # Γ)
  (_ : x' # Γ')
  -- helper hypothesis
  (_ : Γ' ⊢ˢ σ ∶ Γ)
  → -------------------------------------------------------
  (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢ˢ
    (σ ∘/ x := 𝐯 x') ＝ (σ' ∘/ x := 𝐯 x') ∶ (Γ ⨟ x ∶ A ⦂ l)

lift＝Sb{l}{σ}{σ'}{Γ}{Γ'}{A}{x}{x'} p q x#Γ x'#Γ h =
  ＝⨟ˢ (▷＝Sb x' (sbJg h q) p' x'#Γ) q q'' x#Γ
  where
  p' : Γ' ⊢ˢ (σ ∘/ x := 𝐯 x') ＝ (σ' ∘/ x := 𝐯 x') ∶ Γ
  p' = sb＝Ext p
    (λ y r → symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ x#Γ r }))
    λ y r → symm (:=Neq {f = σ'} x y λ{refl → ∉→¬∈ x#Γ r })

  q'' : (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢
      (σ ∘/ x := 𝐯 x') x ＝ (σ' ∘/ x := 𝐯 x') x ∶ (σ ∘/ x := 𝐯 x') * A ⦂ l
  q'' rewrite updateFresh σ x (𝐯 x') A (∉∪₁ (⊢# q x#Γ))
      | :=Eq{f = σ}{𝐯 x'} x
      | :=Eq{f = σ'}{𝐯 x'} x =
    Refl (⊢𝐯 (ok⨟⁻ (sbJg h q) x'#Γ) isInNew)

lift＝Sb² :
  {l l' : Lvl}
  {x y x' y' : 𝔸}
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {A A' B B' : Ty}
  (_ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ A ⦂ l)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
  (_ : x' # Γ')
  (_ : y # (Γ , x))
  (_ : y' # (Γ' , x'))
  (_ : σ * A ≡ A')
  (_ : (σ ∘/ x := 𝐯 x') * B ≡ B')
  -- helper hypotheses
  (h : Γ' ⊢ˢ σ ∶ Γ)
  → --------------------------------------------------------------
  (Γ' ⨟ x' ∶ A' ⦂ l ⨟ y' ∶ B' ⦂ l') ⊢ˢ
  ((σ ∘/ x := 𝐯 x') ∘/ y := 𝐯 y')
  ＝
  ((σ' ∘/ x := 𝐯 x') ∘/ y := 𝐯 y') ∶ (Γ ⨟ x ∶ A ⦂ l  ⨟ y ∶ B ⦂ l')

lift＝Sb² q₀ q₁ q₂ q₃ q₄ q₅ refl refl h
  with ok⨟ q q' _ ← ⊢ok q₂ =
  lift＝Sb (lift＝Sb q₀ q q' q₃ h) q₂ q₄ q₅
    (liftSb⁻ h q q' q₃)

----------------------------------------------------------------------
-- Action of convertible substitutions
----------------------------------------------------------------------
＝sbTm :
  {l : Lvl}
  {σ σ' : Sb}
  {Δ Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Δ ⊢ˢ σ ＝ σ' ∶ Γ)
  (_ : Γ ⊢ a ∶ A ⦂ l)
  -- helper hypothesis
  (_ : Δ ⊢ˢ σ ∶ Γ)
  → -----------------------------
  Δ ⊢ σ * a ＝ σ' * a ∶ σ * A ⦂ l

＝sbTm p (⊢conv q₀ q₁) h = ＝conv (＝sbTm p q₀ h) (sbJg h q₁)

＝sbTm{σ = σ}{σ'} p (⊢𝐯{x = x} _ q) h
  rewrite ‿unit (σ x) ⦃ it ⦄
  | ‿unit (σ' x) ⦃ it ⦄ = sbVar＝ p q

＝sbTm p (⊢𝐔 _) h = Refl (⊢𝐔 (okSb＝ p))

＝sbTm{σ = σ}{σ'}{Δ} p (⊢𝚷{l}{l'}{A = A}{B} S q₀ q₁) h = 𝚷Cong
  (S ∪ supp (Δ , B))
  (＝sbTm p q₀ h)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B) →
    subst₂ (λ C C' → Δ ⨟ x ∶ σ * A ⦂ l ⊢ C ＝ C' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbUpdate[] σ' x (𝐯 x) B x#B)
      (＝sbTm
        (lift＝Sb p q₀ (π₁([]⁻¹(⊢ok (q₁ x x#S)))) x#Δ h)
        (q₁ x x#S)
        (liftSb⁻ h q₀ (π₁([]⁻¹(⊢ok (q₁ x x#S)))) x#Δ))})
  (sbJg h q₀)

＝sbTm{σ = σ}{σ'}{Δ} p (⊢𝛌{l}{l'}{A}{B}{b} S q₀ h₀ h₁) h = 𝛌Cong
  (S ∪ supp (Δ , B , b))
  (＝sbTm p h₀ h)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst₃ (λ c c' C → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ c ＝ c' ∶ C ⦂ l')
      (sbUpdate[] σ x (𝐯 x) b x#b)
      (sbUpdate[] σ' x (𝐯 x) b x#b)
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (＝sbTm
        (lift＝Sb p h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ h)
        (q₀ x x#S)
        (liftSb⁻ h h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ))})
  (sbJg h h₀)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B ∉∪ x#b) →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb h h₀ (π₁([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg h h₀))
        (h₁ x x#S))})

＝sbTm{σ = σ}{σ'}{Δ} p (⊢∙{l}{l'}{A}{B}{a}{b} S q₀ q₁ q₂ h₀) h
  rewrite sb[] σ B a = ∙Cong
  (S ∪ supp (Δ , B))
  (＝sbTm p h₀ h)
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#B) →
    subst₂ (λ C C' → Δ ⨟ x ∶ σ * A ⦂ l ⊢ C ＝ C' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbUpdate[] σ' x (𝐯 x) B x#B)
      (＝sbTm
        (lift＝Sb p h₀ (π₁([]⁻¹(⊢ok (q₂ x x#S)))) x#Δ h)
        (q₂ x x#S)
        (liftSb⁻ h h₀ (π₁([]⁻¹(⊢ok (q₂ x x#S)))) x#Δ))})
  (＝sbTm p q₀ h)
  (＝sbTm p q₁ h)
  (sbJg h h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#B) →
    subst (λ B' → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ B' ⦂ l')
      (sbUpdate[] σ x (𝐯 x) B x#B)
      (sbJg
        (liftSb⁻ h h₀ (π₁([]⁻¹(⊢ok (q₂ x x#S)))) x#Δ)
        (q₂ x x#S))}

＝sbTm p (⊢𝐈𝐝 q₀ q₁ h₀) h = 𝐈𝐝Cong
  (＝sbTm p h₀ h)
  (＝sbTm p q₀ h)
  (＝sbTm p q₁ h)

＝sbTm p (⊢𝐫𝐞𝐟𝐥 q h₀) h = 𝐫𝐞𝐟𝐥Cong
  (＝sbTm p q h)
  (sbJg h h₀)

＝sbTm{σ = σ}{σ'}{Δ} p (⊢𝐉{l}{l'}{A}{C}{a}{b}{c}{e}
  S q₀ q₁ q₂ q₃ q₄ h₀ h₁) h
  rewrite sb[]² σ C b e = 𝐉Cong{l = l}{A = σ * A}
  (S ∪ supp (Δ , C))
  (λ{x y
    (##:: (y#S ∉∪ y#Δ ∉∪ y#C)
    (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C) ##◇)) →
    subst₂ (λ D D' →
      (Δ ⨟ x ∶ σ * A ⦂ l ⨟ y ∶ 𝐈𝐝 (σ * A) (σ * a) (𝐯 x) ⦂ l) ⊢ D ＝ D' ⦂ l')
      (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ (#symm x#y)))
      (sbUpdate[]² σ' x y (𝐯 x) (𝐯 y) C x#C (y#C ∉∪ (#symm x#y)))
      (＝sbTm
        (lift＝Sb² p h₀ (h₁ x x#S) x#Δ
          (π₁([]⁻¹(⊢ok (h₁ y y#S))) ∉∪ #symm x#y)
          (y#Δ ∉∪ (#symm x#y)) refl (eq x x#S x#Δ x#C) h)
        (q₀ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))
        (liftSb² h h₀ (h₁ x x#S) x#Δ
          (π₁([]⁻¹(⊢ok (h₁ y y#S))) ∉∪ #symm x#y) (y#Δ ∉∪ (#symm x#y))
          refl (eq x x#S x#Δ x#C) (sbJg h h₀) (h₁' x x#S x#Δ x#C)))})
  (＝sbTm p q₁ h)
  (＝sbTm p q₂ h)
  (subst (λ C' → Δ  ⊢ σ * c ＝ σ' * c ∶ C' ⦂ l')
    (sb[]² σ C a (𝐫𝐞𝐟𝐥 a))
    (＝sbTm p q₃ h))
  (＝sbTm p q₄ h)
  (sbJg h h₀)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C) → h₁' x x#S x#Δ x#C}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)(x#C : x # C) where
    eq : (σ ∘/ x := 𝐯 x) * 𝐈𝐝 A a (𝐯 x) ≡ 𝐈𝐝(σ * A)(σ * a)(𝐯 x)
    eq rewrite  updateFresh σ x (𝐯 x) A
                (∉∪₂ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
      | updateFresh σ x (𝐯 x) a (∉∪₁ (⊢# q₁ (π₁ ([]⁻¹(⊢ok (h₁ x x#S))))))
      | :=Eq{f = σ}{𝐯 x} x = refl

    h₁' : (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝(σ * A)(σ * a)(𝐯 x) ⦂ l
    h₁' = subst (λ I → (Δ ⨟ x ∶ σ * A ⦂ l) ⊢ I ⦂ l)
      eq
      (sbJg
        (liftSb h h₀ (π₁ ([]⁻¹(⊢ok (h₁ x x#S)))) x#Δ (sbJg h h₀))
        (h₁ x x#S))

＝sbTm p (⊢𝐍𝐚𝐭 _) _ = Refl (⊢𝐍𝐚𝐭 (okSb＝ p))

＝sbTm p (⊢𝐳𝐞𝐫𝐨 _) _ = Refl (⊢𝐳𝐞𝐫𝐨 (okSb＝ p))

＝sbTm p (⊢𝐬𝐮𝐜𝐜 q) h = 𝐬𝐮𝐜𝐜Cong (＝sbTm p q h)

＝sbTm{σ = σ}{σ'}{Δ} p (⊢𝐧𝐫𝐞𝐜{l}{C}{c₀}{a}{c₊} S q₀ q₁ q₂ h₀) h
  rewrite sb[] σ C a = 𝐧𝐫𝐞𝐜Cong
  (S ∪ supp (Δ , C , c₊))
  (λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) → q₀' x x#S x#Δ x#C x#c₊})
  (subst (λ D → Δ ⊢ σ * c₀ ＝ σ' * c₀ ∶ D ⦂ l)
    (sb[] σ C 𝐳𝐞𝐫𝐨)
    (＝sbTm p q₀ h))
  (λ{x y
    (##:: (y#S ∉∪ y#Δ ∉∪ y#C ∉∪ y#c₊)
    (##:: (x#y ∉∪ x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) ##◇)) →
    q₂' x x#S x#Δ x#C x#c₊ y y#S y#Δ y#C y#c₊ x#y})
  (＝sbTm p q₂ h)
  λ{x (x#S ∉∪ x#Δ ∉∪ x#C ∉∪ x#c₊) → h' x x#S x#Δ x#C x#c₊}
  where
  module _ (x : 𝔸)(x#S : x # S)(x#Δ : x # Δ)
    (x#C : x # C)(x#c₊ : x # c₊)
    where
    h' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ⦂ l
    h' = subst (λ C' → (Δ  ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbJg (liftSb h (⊢𝐍𝐚𝐭 (⊢ok q₀)) (π₁ ([]⁻¹(⊢ok (h₀ x x#S)))) x#Δ
        (⊢𝐍𝐚𝐭 (okSb h))) (h₀ x x#S))

    q₀' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ (σ * C) [ x ] ＝ (σ' * C) [ x ] ⦂ l
    q₀' = subst₂ (λ D D' → (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ D ＝ D' ⦂ l)
      (sbUpdate[] σ x (𝐯 x) C x#C)
      (sbUpdate[] σ' x (𝐯 x) C x#C)
      (＝sbTm
        (lift＝Sb p (⊢𝐍𝐚𝐭 (sbOk h)) (π₁ ([]⁻¹(⊢ok (h₀ x x#S)))) x#Δ h)
        (h₀ x x#S)
        (liftSb h (⊢𝐍𝐚𝐭 (sbOk h))
          (π₁ ([]⁻¹(⊢ok (h₀ x x#S)))) x#Δ (⊢𝐍𝐚𝐭 (okSb h))))
    module _
      (y : 𝔸)(y#S : y # S)(y#Δ : y # Δ)
      (y#C : y # C)(y#c₊ : y # c₊)(x#y : x # y)
      where
      eq : ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y)* C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ≡
           (σ * C)[ 𝐬𝐮𝐜𝐜 (𝐯 x) ]
      eq rewrite sb[] ((σ ∘/ x := 𝐯 x) ∘/ y := 𝐯 y) C (𝐬𝐮𝐜𝐜 (𝐯 x))
         | updateFresh ((σ ∘/ x := 𝐯 x)) y (𝐯 y) C y#C
         | updateFresh σ x (𝐯 x) C x#C
         | :=Neq{f = (σ ∘/ x := 𝐯 x)}{𝐯 y} y x
           (λ{refl → ≠𝔸irrefl (∉｛｝⁻¹ x#y)})
         | :=Eq{f = σ}{𝐯 x} x = refl
      q₂' : (Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C)[ x ] ⦂ l) ⊢
        (σ * c₊)[ x ][ y ]  ＝
        (σ' * c₊)[ x ][ y ] ∶ (σ * C) [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l
      q₂' = subst₃ (λ d d' D →
        Δ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ (σ * C) [ x ] ⦂ l ⊢ d ＝ d' ∶ D ⦂ l)
        (sbUpdate[]² σ x y (𝐯 x) (𝐯 y) c₊ x#c₊ (y#c₊ ∉∪ (#symm x#y)))
        (sbUpdate[]² σ' x y (𝐯 x) (𝐯 y) c₊ x#c₊ (y#c₊ ∉∪ (#symm x#y)))
        eq
        (＝sbTm
          (lift＝Sb² p (⊢𝐍𝐚𝐭 (sbOk h)) (h₀ x x#S) x#Δ
            (π₁ ([]⁻¹(⊢ok (h₀ y y#S))) ∉∪ #symm x#y) (y#Δ ∉∪ (#symm x#y))
            refl (sbUpdate[] σ x (𝐯 x) C x#C) h)
          (q₁ x y (##:: y#S (##:: (x#y ∉∪ x#S) ##◇)))
          (liftSb² h (⊢𝐍𝐚𝐭 (sbOk h)) (h₀ x x#S) x#Δ
            ((π₁ ([]⁻¹(⊢ok (h₀ y y#S))) ∉∪ #symm x#y)) (y#Δ ∉∪ (#symm x#y))
            refl (sbUpdate[] σ x (𝐯 x) C x#C) (⊢𝐍𝐚𝐭 (okSb h)) h'))

----------------------------------------------------------------------
-- Renaming provable judgements is a special case of substitution
----------------------------------------------------------------------
rnJg :
  {ρ : Rn}
  {Δ Γ : Cx}
  {J : Jg}
  (_ : Δ ⊢ʳ ρ ∶ Γ)
  (_ : Γ ⊢ J)
  → --------------
  Δ ⊢ ρ * J

rnJg = sbJg

rn⨟ :
  {Γ : Cx}
  {x x' : 𝔸}
  {A : Ty}
  {l : Lvl}
  {J : Jg}
  (_ : Γ ⨟ x ∶ A ⦂ l ⊢ J)
  (_ : x' # Γ)
  → ----------------------------
  Γ ⨟ x' ∶ A ⦂ l ⊢ (x := 𝐯 x') * J

rn⨟{Γ}{x}{x'}{A}{l} q x'#Γ
  with ok⨟ q' x#Γ okΓ ← ⊢ok q = sbJg
    (subst (λ A' →
      (Γ ⨟ x' ∶ A' ⦂ l) ⊢ˢ (x := 𝐯 x') ∶ (Γ ⨟ x ∶ A ⦂ l))
      (sbUnit A)
      (liftSb⁻ (⊢idˢ okΓ) q' x#Γ x'#Γ))
    q

rn⨟² :
  {Γ : Cx}
  {x x' y y' : 𝔸}
  {A B : Ty}
  {l l' : Lvl}
  {J : Jg}
  (_ : Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l' ⊢ J)
  (_ : x' # Γ)
  (_ : y' # (x' , Γ))
  → -------------------------------------------
  Γ ⨟ x' ∶ A ⦂ l ⨟ y' ∶ (x := 𝐯 x') * B ⦂ l' ⊢
    (x := 𝐯 x' ∘/ y := 𝐯 y') * J

rn⨟²{Γ}{x}{x'}{y}{y'}{A}{B}{l}{l'} q x'#Γ (y'#x' ∉∪ y'#Γ)
  with ok⨟ q' (y#Γ ∉∪ y#x) (ok⨟ q'' x#Γ okΓ) ← ⊢ok q =
  sbJg p' q
  where
  p : Γ ⨟ x' ∶ A ⦂ l ⊢ˢ x := 𝐯 x' ∶ Γ ⨟ x ∶ A ⦂ l
  p = subst (λ A' →
    Γ ⨟ x' ∶ A' ⦂ l ⊢ˢ x := 𝐯 x' ∶ Γ ⨟ x ∶ A ⦂ l)
    (sbUnit A)
    (liftSb⁻ (⊢idˢ okΓ) q'' x#Γ x'#Γ)

  p' : (Γ ⨟ x' ∶ A ⦂ l ⨟ y' ∶ (x := 𝐯 x') * B ⦂ l') ⊢ˢ
    (x := 𝐯 x' ∘/ y := 𝐯 y') ∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l')
  p' = liftSb²
    (⊢idˢ okΓ) q'' q'
    x'#Γ (y#Γ ∉∪ y#x) (y'#Γ ∉∪ y'#x') (sbUnit A)
    refl q'' (sbJg p q')

module MLTTcuml.WellScoped where

open import Empty
open import Function
open import Identity
open import Notation
open import Product

open import WSLN

open import MLTTcuml.Syntax
open import MLTTcuml.Judgement
open import MLTTcuml.TypeSystem
open import MLTTcuml.ContextConversion
open import MLTTcuml.Ok

-- We use the augmented version of the type system
open MLTT⁺

----------------------------------------------------------------------
-- Provable judgements are well-scoped
----------------------------------------------------------------------
⊢supp :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → ------------
  supp J ⊆ dom Γ

cxsupp :
  {Γ : Cx}
  {x : 𝔸}
  {A : Ty}
  (_ : Ok Γ)
  (_ : (x , A) isIn Γ)
  → ------------------
  supp A ⊆ dom Γ

cxsupp (∷ p _)  (isInNew refl) = ∈∪₁ ∘ ⊢supp p
cxsupp (∷ ⊢A p) (isInOld q)    = ∈∪₁ ∘ cxsupp p q

⊢suppTy¹ :
  {Γ : Cx}
  {A : Ty}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
  (_ : x # B)
  → ---------------------------
  supp B ⊆ dom Γ

⊢suppTy¹ B x p x# q
    with ⊢supp p (⟨⟩supp B (𝐯 x) q)
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp¹ :
  {Γ : Cx}
  {A B : Ty}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B)
  (_ : x # b)
  → ------------------------------
  supp b ⊆ dom Γ

⊢supp¹ b x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢suppTy² :
  {Γ : Cx}
  {A B : Ty}
  (C : Ty[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C ⟨ x ⸴ y ⟩ ty)
  (_ : x # C)
  (_ : y # C)
  → ---------------------------------------
  supp C ⊆ dom Γ

⊢suppTy² C x y p x# y# q
    with ⊢supp p (⟨⟩²supp C (𝐯 x) (𝐯 y) q)
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp² :
  {Γ : Cx}
  {A B C : Ty}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ⸴ y ∶ B) ⊢ c ⟨ x ⸴ y ⟩ ∶ C)
  (_ : x # c)
  (_ : y # c)
  → ------------------------------------------
  supp c ⊆ dom Γ

⊢supp² c x y p x# y# q
    with ⊢supp p (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢suppTy＝¹₁ :
  {Γ : Cx}
  {A B' : Ty}
  (B : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ＝ B' ty)
  (_ : x # B)
  → ---------------------------------
  supp B ⊆ dom Γ

⊢suppTy＝¹₁ B x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp B (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢suppTy＝¹₂ :
  {Γ : Cx}
  {A B' : Ty}
  (B : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ B' ＝ B ⟨ x ⟩ ty)
  (_ : x # B)
  → ---------------------------------
  supp B ⊆ dom Γ

⊢suppTy＝¹₂ B x p x# q
    with  ⊢supp p ((∈∪₂ (⟨⟩supp B (𝐯 x) q)))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝¹₁ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ b ⟨ x ⟩ ＝ b' ∶ B)
  (_ : x # b)
  → ---------------------------------
  supp b ⊆ dom Γ

⊢supp＝¹₁ b x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝¹₂ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⊢ b' ＝ b ⟨ x ⟩ ∶ B)
  (_ : x # b)
  → ---------------------------------
  supp b ⊆ dom Γ

⊢supp＝¹₂ b x p x# q
    with ⊢supp p ((∈∪₂ (∈∪₁ (⟨⟩supp b (𝐯 x) q))))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢suppTy＝²₁ :
  {Γ : Cx}
  {A B C' : Ty}
  (C : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C ⟨ x ⸴ y ⟩ ＝ C' ty)
  (_ : x # C)
  (_ : y # C)
  → ---------------------------------------------
  supp C ⊆ dom Γ

⊢suppTy＝²₁ C x y p x# y# q
    with ⊢supp p (∈∪₁ (⟨⟩²supp C (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢suppTy＝²₂ :
  {Γ : Cx}
  {A B C' : Ty}
  (C : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ C' ＝ C ⟨ x ⸴ y ⟩ ty)
  (_ : x # C)
  (_ : y # C)
  → ---------------------------------------------
  supp C ⊆ dom Γ

⊢suppTy＝²₂ C x y p x# y# q
    with ⊢supp p (∈∪₂ (⟨⟩²supp C (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp＝²₁ :
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ c ⟨ x ⸴ y ⟩ ＝ c' ∶ C)
  (_ : x # c)
  (_ : y # c)
  → ---------------------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₁ c x y p x# y# q
    with ⊢supp p (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp＝²₂ :
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⸴ y ∶ B ⊢ c' ＝ c ⟨ x ⸴ y ⟩ ∶ C)
  (_ : x # c)
  (_ : y # c)
  → ---------------------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₂ c x y p x# y# q
    with ⊢supp p (∈∪₂ (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) q)))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp (⊢𝚷ty{B = B}{x} q₀ q₁ h) =
  -- helper used here
  ⊆ub (⊢supp h) (⊆ub (⊢suppTy¹ B x q₀ q₁) λ ())
⊢supp (⊢𝐈𝐝ty q₀ q₁ h) =
  ⊆ub (⊢supp h) (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))
⊢supp (⊢𝐄𝐥 q) = ⊢supp q ∘ ∈∪₁
⊢supp (TyRefl q) = ⊆ub (⊢supp q) (⊢supp q)
⊢supp (TySymm q) = ⊆ub (⊢supp q ∘ ∈∪₂) (⊢supp q ∘ ∈∪₁)
⊢supp (TyTrans q₀ q₁) = ⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂)
⊢supp (𝚷TyCong{B = B}{B'}{x} q₀ q₁ q₂ h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp h) (⊆ub (⊢suppTy＝¹₁ B x q₁ (∉∪₁ q₂)) λ()))
    (⊆ub (⊢supp q₀ ∘ ∈∪₂) (⊆ub (⊢suppTy＝¹₂ B' x q₁ (∉∪₂ q₂)) (λ())))
⊢supp (𝐈𝐝TyCong q₀ q₁ q₂) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ()))))
  (⊆ub (⊢supp q₀ ∘ ∈∪₂) (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁) (λ()))))
⊢supp (＝𝐄𝐥 q) = ⊆ub (⊢supp q ∘ ∈∪₁) (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁)
⊢supp (⊢𝐯 q₀ q₁) = ⊆ub (λ{∈｛｝ → isIn→dom q₁}) (cxsupp q₀ q₁)
⊢supp (⊢conv q₀ q₁) = ⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂)
⊢supp (⊢𝚷{B = B}{x} q₀ q₁ q₂) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ B x q₁ q₂) (λ())))
  λ()
⊢supp (⊢𝛌{B = B}{b}{x} q₀ q₁ h₀ h₁) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp h₀) (⊆ub (⊢supp¹ b x q₀ (∉∪₂ q₁)) λ()))
    (⊆ub (⊢supp h₀) (⊆ub (⊢suppTy¹ B x h₁ (∉∪₁ q₁)) λ()))
⊢supp (⊢∙{B = B}{a}{x = x} q₀ q₁ q₂ q₃ h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp h) (⊆ub (⊢suppTy¹ B x q₂ q₃)
      (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))))
    ((⊆ub (⊢suppTy¹ B x q₂ q₃) (⊢supp q₁ ∘ ∈∪₁)) ∘  supp⟨⟩ B a)
⊢supp (⊢𝐈𝐝 q₀ q₁ q₂) = ⊆ub
  (⊆ub (⊢supp q₂ ∘ ∈∪₂)
    (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ()))))
  λ()
⊢supp (⊢𝐫𝐞𝐟𝐥 q _) = ⊆ub
  (⊆ub (⊢supp q ∘ ∈∪₁) λ())
  (⊆ub (⊢supp q ∘ ∈∪₂)
    (⊆ub (⊢supp q ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) λ())))
⊢supp (⊢𝐉{C = C}{b = b}{e = e}{x = x}{y} q₀ q₁ q₂ q₃ q₄ q₅ q₆ h _) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢suppTy² C x y q₀ q₅ q₆) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
      (⊆ub (⊢supp q₂ ∘ ∈∪₁) (⊆ub (⊢supp q₃ ∘ ∈∪₁)
        (⊆ub (⊢supp q₄ ∘ ∈∪₁) (λ()))))))
    (⊆ub
      (⊆ub (⊢suppTy² C x y q₀ q₅ q₆) (⊢supp q₂ ∘ ∈∪₁))
        (⊢supp q₄ ∘ ∈∪₁) ∘ supp⟨⟩² C b e)
⊢supp (⊢𝐍𝐚𝐭 _) = ⊆ub (λ()) λ()
⊢supp (⊢𝐳𝐞𝐫𝐨 _) = ⊆ub (λ()) λ()
⊢supp (⊢𝐬𝐮𝐜𝐜 q) = ⊆ub (⊢supp q) λ()
⊢supp (⊢𝐧𝐫𝐞𝐜{C}{a = a}{c₊ = c₊}{x}{y} q₀ q₁ q₂ q₃ q₄ h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢suppTy¹ C x h (∉∪₁ q₃)) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())))))
    (⊆ub (⊢suppTy¹ C x h (∉∪₁ q₃)) (⊢supp q₂ ∘ ∈∪₁) ∘ supp⟨⟩ C a)
⊢supp (TmRefl q) = ⊆ub
  (⊢supp q ∘ ∈∪₁)
  (⊆ub (⊢supp q ∘ ∈∪₁) (⊢supp q ∘ ∈∪₂))
⊢supp (TmSymm q) = ⊆ub
  (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁)
  (⊆ub (⊢supp q ∘ ∈∪₁) (⊢supp q ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp (TmTrans q₀ q₁) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp (＝conv q₀ q₁) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂))
⊢supp (𝚷TmCong{B = B}{B'}{x} q₀ q₁ q₂ _) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₁ B x q₁ (∉∪₁ q₂)) λ()))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp＝¹₂ B' x q₁ (∉∪₂ q₂)) λ())) λ())
⊢supp (𝛌Cong{B = B}{b}{b'}{x} q₀ q₁ q₂ _ h₁) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₁ b x q₁ (∉∪₁ (∉∪₂ q₂))) λ()))
    (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂) (⊆ub (⊢supp＝¹₂ b' x q₁ (∉∪₂ (∉∪₂ q₂))) λ()))
      (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢suppTy¹ B x h₁ (∉∪₁ q₂)) λ())))
⊢supp (∙Cong{B = B}{B'}{a = a}{x = x} q₀ q₁ q₂ q₃ q₄ _ _) = ⊆ub
  (⊆ub (⊢supp q₂ ∘ ∈∪₁) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊢suppTy＝¹₁ B x q₁ (∉∪₁ q₄)) (⊆ub (⊢supp q₃ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp q₀ ∘ ∈∪₂) (⊆ub (⊢suppTy＝¹₂ B' x q₁ (∉∪₂ q₄))
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) λ()))))
      (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁)
        (⊢supp q₃ ∘ ∈∪₁) ∘ supp⟨⟩ B a))
⊢supp (𝐈𝐝TmCong q₀ q₁ q₂) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ())))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁) λ())))
    λ())
⊢supp (𝐫𝐞𝐟𝐥Cong q h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp q ∘ ∈∪₁) λ ())
    (⊆ub (⊆ub (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) λ())
      (⊆ub (⊢supp h) (⊆ub (⊢supp q ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) λ()))))
⊢supp (𝐉Cong{C = C}{C'}{b = b}{e = e}{x = x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = ⊆ub
  (⊆ub (⊢suppTy＝²₁ C x y q₀ (∉∪₁ q₅) (∉∪₁ q₆))
    (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁)
      (⊆ub (⊢supp q₃ ∘ ∈∪₁) (⊆ub (⊢supp q₄ ∘ ∈∪₁) λ())))))
  (⊆ub (⊆ub (⊢suppTy＝²₂ C' x y q₀ (∉∪₂ q₅) (∉∪₂ q₆))
    (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁)
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₄ ∘ ∈∪₂ ∘ ∈∪₁) λ())))))
        (⊆ub (⊆ub (⊢suppTy＝²₁ C x y q₀ (∉∪₁ q₅) (∉∪₁ q₆)) (⊢supp q₂ ∘ ∈∪₁))
          (⊢supp q₄ ∘ ∈∪₁) ∘ supp⟨⟩² C b e))
⊢supp (𝐬𝐮𝐜𝐜Cong q) = ⊆ub
  (⊆ub (⊢supp q ∘ ∈∪₁) λ())
  (⊆ub (⊆ub (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) λ()) λ())
⊢supp (𝐧𝐫𝐞𝐜Cong{C = C}{C'}{a = a}{c₊ = c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') _) = ⊆ub
  (⊆ub (⊢suppTy＝¹₁ C x q₀ q₄) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₁ c₊ x y q₂ q₄'' q₅) (⊆ub (⊢supp q₃ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢suppTy＝¹₂ C' x q₀ q₄') (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₂ c₊' x y q₂ q₄''' q₅')
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) λ()))))
        (⊆ub (⊢suppTy＝¹₁ C x q₀ q₄) (⊢supp q₃ ∘ ∈∪₁) ∘ supp⟨⟩ C a))
⊢supp (𝚷Beta{a = a}{B}{b}{x} q₀ q₁ q₂ h₁ h₂) =
  -- helpers used here
  ⊆ub
    (⊆ub (⊆ub (⊢supp h₁) (⊆ub (⊢supp¹ b x q₀ (∉∪₂ q₂)) λ()))
      (⊆ub (⊢supp h₁) (⊆ub (⊢suppTy¹ B x h₂ (∉∪₁ q₂))
        (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))))
    (⊆ub (⊆ub (⊢supp¹ b x q₀ (∉∪₂ q₂)) (⊢supp q₁ ∘ ∈∪₁) ∘ supp⟨⟩ b a)
      (⊆ub (⊢suppTy¹ B x h₂ (∉∪₁ q₂)) (⊢supp q₁ ∘ ∈∪₁) ∘ supp⟨⟩ B a))
⊢supp (𝐈𝐝Beta{C = C}{a}{x = x}{y} q₀ q₁ q₂ q₃ q₄ _ _) = ⊆ub
  (⊆ub (⊢suppTy² C x y q₀ q₃ q₄) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁)
      (⊆ub (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()) λ())))))
  (⊆ub (⊢supp q₂ ∘ ∈∪₁)
    (⊆ub (⊆ub (⊢suppTy² C x y q₀ q₃ q₄) (⊢supp q₁ ∘ ∈∪₁))
      (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()) ∘ supp⟨⟩² C a (𝐫𝐞𝐟𝐥 a)))
⊢supp (𝐍𝐚𝐭Beta₀{C = C}{c₊ = c₊}{x}{y} q₀ q₁ q₂ q₃ _) =
  ⊆ub
    (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₂) q₃) (⊆ub (λ()) λ()))))
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₀ ∘ ∈∪₂))
⊢supp (𝐍𝐚𝐭Beta₊{C = C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ q₃ q₄ h) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨)
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄)
      (⊆ub (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())) λ()))))
  (⊆ub (⊆ub (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊢supp q₂ ∘ ∈∪₁))
    (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ()))))
        ∘ supp⟨⟩² c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a))
    ((⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ⟨⟩supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())))
      ∘ supp⟨⟩ C (𝐬𝐮𝐜𝐜 a)))
⊢supp{Γ} (𝚷Eta{A}{B}{b}{x} q₀ q₁ h) =
  -- helpers used here
  ⊆ub
    (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊆ub (⊢supp h) (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₁ ∘ suppAbs x b)
      (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁ ∘ suppAbs x A)
      (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁ ∘ suppCls x (inc^ iz) B refl)
        (⊆ub (∉⊆ (#abs x (𝐯 x)) (∈∪₂ ∘ suppAbs x (𝐯 x))) λ())))) λ()))
        (⊆ub (⊢supp h) (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) λ())))

----------------------------------------------------------------------
-- Freshness property of provable judgements
----------------------------------------------------------------------
⊢# :
  {Γ : Cx}
  {J : Jg}
  {x : 𝔸}
  (_ : Γ ⊢ J)
  (_ : x # Γ)
  → -------------
  x # J

⊢#{Γ} p = ⊆∉ (⊢supp p)

----------------------------------------------------------------------
-- Convertible contexts have extensionally equal domains
----------------------------------------------------------------------
dom＝ :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  dom Γ ⊆ dom Γ'

dom＝ (∷ q _ _ _) (∈∪₁ x∈Γ) = ∈∪₁ (dom＝ q x∈Γ)
dom＝ (∷ _ _ _ _) (∈∪₂ ∈｛｝) = ∈∪₂ ∈｛｝

module ETT.Sized.WellScoped where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.Sized.TypeSystem
open import ETT.Sized.ContextConversion
open import ETT.Sized.Ok

----------------------------------------------------------------------
-- Provable judgements are well-scoped
----------------------------------------------------------------------
⊢supp :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → -------------
  supp J ⊆ dom Γ

⊢supp≤ :
  (s : ℕ)
  {Γ : Cx}
  {J : Jg}
  (q : Γ ⊢ J)
  ⦃ _ : size q ≤ s ⦄
  → ----------------
  supp J ⊆ dom Γ

⊢supp q = ⊢supp≤ (size q) q ⦃ ≤refl ⦄

Oksupp :
  (s : ℕ)
  {Γ : Cx}
  {x : 𝔸}
  {A : Ty}
  {l : Lvl}
  (q : Ok Γ)
  ⦃ _ : size q ≤ s ⦄
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  supp A ⊆ dom Γ

Oksupp 0 q ⦃ p ⦄ r _
  with (_ , e) ←  Ok+ q r
  rewrite e = case p of λ{()}
Oksupp (1+ s) (∷ q) ⦃ 1+≤ ⦄ (isInNew refl) = ∈∪₁ ∘ ⊢supp≤ s q
Oksupp (1+ s) (∷ q) ⦃ 1+≤ ⦄ (isInOld r) =
  let (q' , p') = ⊢ok≤ s q ⦃ it ⦄
  in ∈∪₁ ∘ Oksupp s q' ⦃ it ∘ p' ∘ ≤step ⦄ r

⊢suppTy¹ :
  {s : ℕ}
  {Γ : Cx}
  {A : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # B)
  → ----------------------------------
  supp B ⊆ dom Γ

⊢suppTy¹ {s} B x q x# p
    with ⊢supp≤ s q (⟨⟩supp B (𝐯 x) p)
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢suppTy¹' :
  {s : ℕ}
  {Γ : Cx}
  {A : Ty}
  {l l' : Lvl}
  {b : Tm}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ∶ B ⟨ x ⟩ ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # B)
  → --------------------------------------
  supp B ⊆ dom Γ

⊢suppTy¹' {s} B x q x# p
    with ⊢supp≤ s q (∈∪₂ (⟨⟩supp B (𝐯 x) p))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢suppTy¹'' :
  {s : ℕ}
  {Γ : Cx}
  {A : Ty}
  {l l' : Lvl}
  {b b' : Tm}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ＝ b' ∶ B ⟨ x ⟩ ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # B)
  → --------------------------------------------
  supp B ⊆ dom Γ

⊢suppTy¹'' {s} B x q x# p
    with ⊢supp≤ s q (∈∪₂ (∈∪₂ (⟨⟩supp B (𝐯 x) p)))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp¹ :
  {s : ℕ}
  {Γ : Cx}
  {A B : Ty}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # b)
  → --------------------------------------
  supp b ⊆ dom Γ

⊢supp¹ {s} b x q x# p
    with ⊢supp≤ s q (∈∪₁ (⟨⟩supp b (𝐯 x) p))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp² :
  {s : ℕ}
  {Γ : Cx}
  {A B C : Ty}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    c ⟨ x ⸴ y ⟩ ∶ C ⦂ l'')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # c)
  (_ : y # c)
  → ---------------------------------
  supp c ⊆ dom Γ

⊢supp² {s} c x y q x# y# p
    with ⊢supp≤ s q (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) p))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# p)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# p)

⊢supp＝Ty¹₁ :
  {s : ℕ}
  {Γ : Cx}
  {A B' : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ＝ B' ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # B)
  → ----------------------------------------
  supp B ⊆ dom Γ

⊢supp＝Ty¹₁ {s} B x q x# p
    with ⊢supp≤ s q (∈∪₁ (⟨⟩supp B (𝐯 x) p))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp＝Ty¹₂ :
  {s : ℕ}
  {Γ : Cx}
  {A B' : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : Γ ⸴ x ∶ A ⦂ l ⊢ B' ＝ B ⟨ x ⟩ ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # B)
  → --------------------------------------
  supp B ⊆ dom Γ

⊢supp＝Ty¹₂ {s} B x q x# p
    with ⊢supp≤ s q (∈∪₂ (⟨⟩supp B (𝐯 x) p))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp＝¹₁ :
  {s : ℕ}
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ＝ b' ∶ B ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # b)
  → --------------------------------------------
  supp b ⊆ dom Γ

⊢supp＝¹₁ {s} b x q x# p
    with ⊢supp≤ s q (∈∪₁ (⟨⟩supp b (𝐯 x) p))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp＝¹₂ :
  {s : ℕ}
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l) ⊢ b' ＝ b ⟨ x ⟩ ∶ B ⦂ l')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # b)
  → --------------------------------------------
  supp b ⊆ dom Γ

⊢supp＝¹₂ {s} b x q x# p
    with ⊢supp≤ s q ((∈∪₂ (∈∪₁ (⟨⟩supp b (𝐯 x) p))))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# p)

⊢supp＝²₁ :
  {s : ℕ}
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    c ⟨ x ⸴ y ⟩ ＝ c' ∶ C ⦂ l'')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # c)
  (_ : y # c)
  → ----------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₁ {s} c x y q x# y# p
    with ⊢supp≤ s q (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) p))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# p)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# p)

⊢supp＝²₂ :
  {s : ℕ}
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (q : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    c' ＝ c ⟨ x ⸴ y ⟩ ∶ C ⦂ l'')
  ⦃ _ : size q ≤ s ⦄
  (_ : x # c)
  (_ : y # c)
  → ---------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₂ {s} c x y q x# y# p
    with ⊢supp≤ s q (∈∪₂ (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) p)))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# p)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# p)

⊢supp≤ 0 q ⦃ p ⦄
  with (_ , e) ← Jg+ q
  rewrite e = case p of λ{()}
⊢supp≤ (1+ s) (⊢𝚷{B = B}{x} q x#) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q = ⊆ub
    (⊢supp≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄)
    (⊆ub (⊢suppTy¹ B x q x#) λ())
⊢supp≤ (1+ s) (⊢𝐈𝐝 q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
  (⊆ub (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁) λ())
⊢supp≤ (1+ s) (⊢conv q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
  (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₂)
⊢supp≤ (1+ s) (⊢𝐯 q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (λ{∈｛｝ → isIn→dom q₁})
  (Oksupp s q₀ q₁)
⊢supp≤ (1+ s) (⊢𝛌{B = B}{b}{x} q₀ (q₁ ∉∪ q₁')) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q₀ = ⊆ub
  (⊆ub (⊢supp¹ b x q₀ q₁') λ())
  (⊆ub (⊢supp≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄)
    (⊆ub (⊢suppTy¹' B x q₀ q₁) λ()))
⊢supp≤ (1+ s) (⊢∙{B = B}{a}{x = x} q₀ q₁ q₂ q₃) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub (⊢supp≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ ∘ ∈∪₁)
    (⊆ub (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁) λ()))
  ((⊆ub
     (⊢suppTy¹ B x q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ q₃)
     (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁))
   ∘ supp⟨⟩ B a)
⊢supp≤ (1+ s) (⊢𝐫𝐞𝐟𝐥 q) ⦃ 1+≤ ⦄ = ⊆ub
  (λ())
  (⊆ub
    (⊢supp≤ s q ∘ ∈∪₁)
    (⊆ub (⊢supp≤ s q ∘ ∈∪₁) λ()))
⊢supp≤ (1+ _) (⊢𝐳𝐞𝐫𝐨 _) ⦃ 1+≤ ⦄ = ⊆ub (λ()) λ()
⊢supp≤ (1+ s) (⊢𝐬𝐮𝐜𝐜 q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub (⊢supp≤ s q ∘ ∈∪₁) λ())
  λ()
⊢supp≤ (1+ s) (⊢𝐧𝐫𝐞𝐜{C = C}{a = a}{c₊ = c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄) ⦃ 1+≤ ⦄
  with (∷ q' , p') ←
    ⊢ok≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ =
  let qC = ⊢suppTy¹ C x q'
            ⦃ (it ∘ ≤max³₂ (size q₀) _ (size q₂)) ∘ p' ∘ ≤step ∘ ≤step ⦄
            q₃
  in
  ⊆ub
    (⊆ub
      qC
      (⊆ub
        (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₁)
        (⊆ub
          (⊢supp² c₊ x y q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ q₃' q₄)
          (⊆ub
            (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
            λ()))))
    ((⊆ub qC (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁))
     ∘ supp⟨⟩ C a)
⊢supp≤ (1+ s) (TyRefl q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q)
  (⊢supp≤ s q)
⊢supp≤ (1+ s) (TySymm q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q ∘ ∈∪₂)
  (⊢supp≤ s q ∘ ∈∪₁)
⊢supp≤ (1+ s) (TyTrans q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
  (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₂)
⊢supp≤ (1+ s) (𝚷Cong{B = B}{B'}{x} q₀ q₁ (q₂ ∉∪ q₂')) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
    (⊆ub (⊢supp＝Ty¹₁ B x q₁ ⦃ it ∘ ≤max₂ (size q₀) _ ⦄ q₂) λ()))
  (⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₂)
    (⊆ub
      (⊢supp＝Ty¹₂ B' x q₁ ⦃ it ∘ ≤max₂ (size q₀) _ ⦄ q₂')
      λ()))
⊢supp≤ (1+ s) (𝐈𝐝Cong q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
    (⊆ub
      (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁) λ()))
  (⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁) λ()))
⊢supp≤ (1+ s) (TmRefl q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q ∘ ∈∪₁)
  (⊆ub
    (⊢supp≤ s q ∘ ∈∪₁)
    (⊢supp≤ s q ∘ ∈∪₂))
⊢supp≤ (1+ s) (TmSymm q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q ∘ ∈∪₂ ∘ ∈∪₁)
  (⊆ub
    (⊢supp≤ s q ∘ ∈∪₁)
    (⊢supp≤ s q ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp≤ (1+ s) (TmTrans q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
  (⊆ub
    (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp≤ (1+ s) (＝conv q₀ q₁) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
  (⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₂))
⊢supp≤ (1+ s) (⊢Reflect q₀ q₁ q₂) ⦃ 1+≤ ⦄ = ⊆ub
  (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₁)
  (⊆ub
    (⊢supp≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ ∘ ∈∪₁)
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₂))
⊢supp≤ (1+ s) (𝛌Cong{B = B}{b}{b'}{x}
  q₀ (q₁ ∉∪ q₁' ∉∪ q₁'')) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q₀ = ⊆ub
  (⊆ub (⊢supp＝¹₁ b x q₀ q₁') λ())
  (⊆ub
    (⊆ub (⊢supp＝¹₂ b' x q₀ q₁'') λ())
    (⊆ub
      (⊢supp≤ s q' ⦃ it ∘ p' ∘ ≤step ∘ ≤step ⦄ )
      (⊆ub
        (⊢suppTy¹'' B x q₀ q₁)
        λ())))
⊢supp≤ (1+ s) (∙Cong{B = B}{a = a}{x = x} q₀ q₁ q₂ q₃) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub
    (⊢supp≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ ∘ ∈∪₁)
    (⊆ub
      (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
      λ()))
  (⊆ub
    (⊆ub
      (⊢supp≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
      (⊆ub
        (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
        λ()))
    ((⊆ub
      (⊢suppTy¹{s} B x q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ q₃)
      (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁))
     ∘ supp⟨⟩ B a))
⊢supp≤ (1+ s) (𝐬𝐮𝐜𝐜Cong q) ⦃ 1+≤ ⦄ = ⊆ub
  (⊆ub
    (⊢supp≤ s q ∘ ∈∪₁)
    λ())
  (⊆ub
    (⊆ub
      (⊢supp≤ s q ∘ ∈∪₂ ∘ ∈∪₁)
      λ())
    λ())
⊢supp≤ (1+ s) (𝐧𝐫𝐞𝐜Cong{C = C}{C'}{a = a}{c₊ = c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅')) ⦃ 1+≤ ⦄ =
  ⊆ub
    (⊆ub
      (⊢supp＝Ty¹₁{s} C x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ q₄)
      (⊆ub
        (⊢supp≤ s q₁
          ⦃ it ∘ ≤max⁴₂ (size q₀) _ (size q₂) (size q₃) ⦄ ∘ ∈∪₁)
        (⊆ub
          (⊢supp＝²₁ {s} c₊ x y q₂
            ⦃ it ∘ ≤max⁴₃ (size q₀) (size q₁) _ (size q₃) ⦄ q₄'' q₅)
          (⊆ub
            (⊢supp≤ s q₃
              ⦃ it ∘ ≤max⁴₄ (size q₀) (size q₁) (size q₂) _ ⦄ ∘ ∈∪₁)
            λ()))))
    (⊆ub
      (⊆ub
        (⊢supp＝Ty¹₂{s} C' x q₀ ⦃ it ∘ ≤max₁ _ _  ⦄ q₄')
        (⊆ub
          ((⊢supp≤ s q₁
             ⦃ it ∘ ≤max⁴₂ (size q₀) _ (size q₂) (size q₃) ⦄ ∘ ∈∪₂ ∘ ∈∪₁))
          (⊆ub
            (⊢supp＝²₂ {s} c₊' x y q₂
              ⦃ it ∘ ≤max⁴₃ (size q₀) (size q₁) _ (size q₃) ⦄ q₄''' q₅')
            (⊆ub
              (⊢supp≤ s q₃
                 ⦃ it ∘ ≤max⁴₄ (size q₀) (size q₁) (size q₂) _ ⦄ ∘ ∈∪₂ ∘ ∈∪₁)
              λ()))))
      ((⊆ub
        (⊢supp＝Ty¹₁{s} C x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ q₄)
        (⊢supp≤ s q₃ ⦃ it ∘ ≤max⁴₄ (size q₀) (size q₁) (size q₂) _ ⦄ ∘ ∈∪₁))
       ∘ supp⟨⟩ C a))
⊢supp≤ (1+ s) (𝚷Beta{a = a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂')) ⦃ 1+≤ ⦄ =
  ⊆ub
    (⊆ub
      (⊆ub
        (⊢supp¹ b x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ q₂')
        λ())
      (⊆ub
        (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁)
        λ()))
    (⊆ub
      (⊆ub
        (⊢supp¹ b x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ q₂')
        (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁)
       ∘ supp⟨⟩ b a)
      (⊆ub
        (⊢suppTy¹' B x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ q₂)
        (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁)
       ∘ supp⟨⟩ B a))
⊢supp≤ (1+ s) (𝐍𝐚𝐭Beta₀{C = C}{c₊ = c₊}{x}{y}
  q₀ q₁ (q₂ ∉∪ q₂') q₃) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ =
  ⊆ub
    (⊆ub
      (⊢suppTy¹{s} C x q'
        ⦃ it ∘ ≤max₂ _ _ ∘ p' ∘ ≤step ∘ ≤step ⦄ q₂)
      (⊆ub
        (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
        (⊆ub
          (⊢supp² c₊ x y q₁ ⦃ it ∘ ≤max₂ (size q₀) _ ⦄ q₂' q₃)
          (⊆ub (λ()) λ()))))
    (⊆ub
      (⊢supp≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ ∘ ∈∪₁)
      (⊆ub
        (⊢suppTy¹{s} C x q'
          ⦃ it ∘ ≤max₂ _ _ ∘ p' ∘ ≤step ∘ ≤step ⦄ q₂)
        (λ())
       ∘ supp⟨⟩ C 𝐳𝐞𝐫𝐨))
⊢supp≤ (1+ s) (𝐍𝐚𝐭Beta₊{C = C}{c₀}{a}{c₊}{x}{y}
  q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ =
  ⊆ub
    (⊆ub
      (⊢suppTy¹{s} C x q'
        ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ∘ p' ∘ ≤step ∘ ≤step ⦄ q₃)
      (⊆ub
        (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₁)
        (⊆ub
          (⊢supp² c₊ x y q₁
            ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ q₃' q₄)
          (⊆ub
            (⊆ub
              (⊢supp≤ s q₂
                ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
              λ())
            λ()))))
    (⊆ub
      (⊆ub
        (⊆ub
          (⊢supp² c₊ x y q₁
            ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ q₃' q₄)
          (⊢supp≤ s q₂
            ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁))
        (⊆ub
          (⊢suppTy¹{s} C x q'
            ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ∘ p' ∘ ≤step ∘ ≤step ⦄ q₃)
          (⊆ub
            (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₁)
            (⊆ub
              (⊢supp² c₊ x y q₁
            ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ q₃' q₄)
              (⊆ub
                (⊢supp≤ s q₂
                  ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
                λ()))))
       ∘ supp⟨⟩² c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a))
      (⊆ub
        (⊢suppTy¹{s} C x q'
            ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ∘ p' ∘ ≤step ∘ ≤step ⦄ q₃)
        (⊆ub
          (⊢supp≤ s q₂
            ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
          (λ()))
       ∘ supp⟨⟩ C (𝐬𝐮𝐜𝐜 a)))
⊢supp≤ (1+ s) (𝚷Eta{A = A}{B}{b}{x} q₀ q₁) ⦃ 1+≤ ⦄
  with (∷ q' , p') ← ⊢ok≤ s q₀ ⦃ it ∘ ≤max₁ _ _ ⦄ =
  ⊆ub
    (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁)
    (⊆ub
      (⊆ub
        (⊆ub
          ((⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄ ∘ ∈∪₁) ∘ suppAbs x b)
          (⊆ub (λ{y} p → Øelim (∉→¬∈ (y#x．𝐯x x y) p)) λ()))
        λ())
      (⊆ub
        (⊢supp≤ s q' ⦃ it ∘ ≤max₁ _ _ ∘ p' ∘ ≤step ∘ ≤step ⦄)
        (⊆ub
          (⊢suppTy¹ {s} B x q₀ ⦃ it ∘ ≤max₁ _ _ ⦄
            ((⊆∉ (⊢supp≤ s q₁ ⦃ it ∘ ≤max₂ _ _ ⦄
              ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) it)))
          λ())))
⊢supp≤ (1+ s) (UIP q₀ q₁ q₂) ⦃ 1+≤ ⦄ =
  ⊆ub
    (⊢supp≤ s q₀ ⦃ it ∘ ≤max³₁ _ (size q₁) (size q₂) ⦄ ∘ ∈∪₁)
    (⊆ub
      (λ())
      (⊆ub
        (⊢supp≤ s q₁ ⦃ it ∘ ≤max³₂ (size q₀) _ (size q₂) ⦄ ∘ ∈∪₁)
        (⊆ub
          (⊢supp≤ s q₂ ⦃ it ∘ ≤max³₃ (size q₀) (size q₁) _ ⦄ ∘ ∈∪₁)
          λ())))
⊢supp≤ (1+ s) (Ty→Tm q) = ⊆ub (⊢supp≤ (1+ s) q) λ()
⊢supp≤ (1+ s) (Tm→Ty q) = ⊢supp≤ (1+ s) q ∘ ∈∪₁
⊢supp≤ (1+ s) (=Ty→Tm q) =
  ⊆ub
    (⊢supp≤ (1+ s) q ∘ ∈∪₁)
    (⊆ub (⊢supp≤ (1+ s) q ∘ ∈∪₂) λ())
⊢supp≤ (1+ s) (=Tm→Ty q) =
  ⊆ub
    (⊢supp≤ (1+ s) q ∘ ∈∪₁)
    (⊢supp≤ (1+ s) q ∘ ∈∪₂ ∘ ∈∪₁)

----------------------------------------------------------------------
-- Freshness property of provable judgements
----------------------------------------------------------------------
⊢# :
  {Γ : Cx}
  {J : Jg}
  {x : 𝔸}
  (_ : Γ ⊢ J)
  (_ : x # Γ)
  → ---------
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

dom＝ (∷ q _) (∈∪₁ p)    = ∈∪₁ (dom＝ q p)
dom＝ (∷ _ _) (∈∪₂ ∈｛｝) = ∈∪₂ ∈｛｝

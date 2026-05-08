module ETT.WellScoped where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem
open import ETT.ContextConversion
open import ETT.Ok

----------------------------------------------------------------------
-- Provable judgements are well-scoped
----------------------------------------------------------------------
⊢supp :
  {Γ : Cx}
  {J : Jg}
  (_ : Γ ⊢ J)
  → ------------
  supp J ⊆ dom Γ

Oksupp :
  {Γ : Cx}
  {x : 𝔸}
  {A : Ty}
  {l : Lvl}
  (_ : Ok Γ)
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  supp A ⊆ dom Γ

Oksupp (∷ p _)  isInNew     = ∈∪₁ ∘ ⊢supp p
Oksupp (∷ ⊢A p) (isInOld q) = ∈∪₁ ∘ Oksupp p q

⊢suppTy¹ :
  {Γ : Cx}
  {A : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
  (_ : x # B)
  → -----------------------------------
  supp B ⊆ dom Γ

⊢suppTy¹ B x p x# q
    with ⊢supp p (⟨⟩supp B (𝐯 x) q)
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp¹ :
  {Γ : Cx}
  {A B : Ty}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⦂ l')
  (_ : x # b)
  → --------------------------------------
  supp b ⊆ dom Γ

⊢supp¹ b x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp² :
  {Γ : Cx}
  {A B C : Ty}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l') ⊢
    c ⟨ x ⸴ y ⟩ ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → ---------------------------------
  supp c ⊆ dom Γ

⊢supp² c x y p x# y# q
    with ⊢supp p (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp＝Ty¹₁ :
  {Γ : Cx}
  {A B' : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    B ⟨ x ⟩ ＝ B' ⦂ l')
  (_ : x # B)
  → -----------------------
  supp B ⊆ dom Γ

⊢supp＝Ty¹₁ B x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp B (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝Ty¹₂ :
  {Γ : Cx}
  {A B' : Ty}
  {l l' : Lvl}
  (B : Ty[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    B' ＝ B ⟨ x ⟩ ⦂ l')
  (_ : x # B)
  → --------------------
  supp B ⊆ dom Γ

⊢supp＝Ty¹₂ B x p x# q
    with ⊢supp p (∈∪₂ (⟨⟩supp B (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝¹₁ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    b ⟨ x ⟩ ＝ b' ∶ B ⦂ l')
  (_ : x # b)
  → -----------------------
  supp b ⊆ dom Γ

⊢supp＝¹₁ b x p x# q
    with ⊢supp p (∈∪₁ (⟨⟩supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝¹₂ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    b' ＝ b ⟨ x ⟩ ∶ B ⦂ l')
  (_ : x # b)
  → ----------------------
  supp b ⊆ dom Γ

⊢supp＝¹₂ b x p x# q
    with ⊢supp p ((∈∪₂ (∈∪₁ (⟨⟩supp b (𝐯 x) q))))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x# q)

⊢supp＝²₁ :
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l' ⊢
    c ⟨ x ⸴ y ⟩ ＝ c' ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → --------------------------------
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
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ B ⦂ l' ⊢
    c' ＝ c ⟨ x ⸴ y ⟩ ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → --------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₂ c x y p x# y# q
    with ⊢supp p (∈∪₂ (∈∪₁ (⟨⟩²supp c (𝐯 x) (𝐯 y) q)))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x# q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y# q)

⊢supp (⊢𝐔 _) = λ()
⊢supp (⊢𝚷{B = B}{x} q₀ q₁ q₂) = ⊆ub
  (⊢supp q₀)
  (⊆ub (⊢suppTy¹ B x q₁ q₂) λ())
⊢supp (⊢𝐈𝐝 q₀ q₁ q₂) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ())
⊢supp (⊢𝐍𝐚𝐭 _) = λ()
⊢supp (Tm→Ty q) = ⊢supp q ∘ ∈∪₁
⊢supp (⊢conv q₀ q₁) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊢supp q₁ ∘ ∈∪₂)
⊢supp (⊢𝐯 q₀ q₁) = ⊆ub
  (λ{∈｛｝ → isIn→dom q₁})
  (Oksupp q₀ q₁)
⊢supp (Ty→Tm q) = ⊆ub (⊢supp q) λ()
⊢supp (⊢𝛌{B = B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) = ⊆ub
  (⊆ub (⊢supp¹ b x q₀ q₁') λ())
  (⊆ub (⊢supp h₀) (⊆ub (⊢suppTy¹ B x h₁ q₁) λ()))
⊢supp (⊢∙{B = B}{a}{x = x} q₀ q₁ q₂ q₃ h) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))
  ((⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₁)) ∘ supp⟨⟩ B a)
⊢supp (⊢𝐫𝐞𝐟𝐥 q h) = ⊆ub
  (λ())
  (⊆ub (⊢supp q ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) λ()))
⊢supp (⊢𝐳𝐞𝐫𝐨 q) = ⊆ub (λ()) λ()
⊢supp (⊢𝐬𝐮𝐜𝐜 q) = ⊆ub (⊢supp q) λ()
⊢supp (⊢𝐧𝐫𝐞𝐜{C = C}{a = a}{c₊ = c₊}{x}{y} q q₁ q₂ (q₃ ∉∪ q₃') q₄ h) = ⊆ub
  (⊆ub (⊢suppTy¹ C x h q₃) (⊆ub (⊢supp q ∘ ∈∪₁)
    (⊆ub (⊢supp² c₊ x y q₁ q₃' q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ()))))
  ((⊆ub (⊢suppTy¹ C x h q₃) (⊢supp q₂ ∘ ∈∪₁)) ∘ supp⟨⟩ C a)
⊢supp (TyRefl q) = ⊆ub (⊢supp q) (⊢supp q)
⊢supp (TySymm q) = ⊆ub (⊢supp q ∘ ∈∪₂) (⊢supp q ∘ ∈∪₁)
⊢supp (TyTrans q₀ q₁) = ⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂)
⊢supp (𝚷Cong{B = B}{B'}{x} q₀ q₁ (q₂ ∉∪ q₂') h) = ⊆ub
  (⊆ub (⊢supp h) (⊆ub (⊢supp＝Ty¹₁ B x q₁ q₂) λ()))
  (⊆ub (⊢supp q₀ ∘ ∈∪₂) (⊆ub (⊢supp＝Ty¹₂ B' x q₁ q₂') λ()))
⊢supp (𝐈𝐝Cong q₀ q₁ h) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))
  (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) λ()))
⊢supp (=Tm→Ty q) = ⊆ub
  (⊢supp q ∘ ∈∪₁)
  (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁)
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
⊢supp (=Ty→Tm q) = ⊆ub
  (⊢supp q ∘ ∈∪₁)
  (⊆ub (⊢supp q ∘ ∈∪₂) λ())
⊢supp (⊢Reflect q q₁ q₂ h) = ⊆ub
  (⊢supp q ∘ ∈∪₁)
  (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊢supp h))
⊢supp (𝛌Cong{B = B}{b}{b'}{x} q₀ (q₁ ∉∪ q₁' ∉∪ q₁'') h₀ h₁) = ⊆ub
  (⊆ub (⊢supp＝¹₁ b x q₀ q₁') λ())
  (⊆ub (⊆ub (⊢supp＝¹₂ b' x q₀ q₁'') λ())
    (⊆ub (⊢supp h₀) (⊆ub (⊢suppTy¹ B x h₁ q₁) λ ())))
⊢supp (∙Cong{B = B}{a = a}{x = x} q₀ q₁ q₂ h₀ h₁) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) λ()))
    ((⊆ub (⊢suppTy¹ B x h₁ q₂) (⊢supp q₁ ∘ ∈∪₁)) ∘ supp⟨⟩ B a))
⊢supp (𝐬𝐮𝐜𝐜Cong q) = ⊆ub
  (⊆ub (⊢supp q ∘ ∈∪₁) λ())
  (⊆ub (⊆ub (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) λ()) λ())
⊢supp (𝐧𝐫𝐞𝐜Cong{C = C}{C'}{a = a}{c₊ = c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅')  h) = ⊆ub
  (⊆ub (⊢supp＝Ty¹₁ C x q₀ q₄) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₁ c₊ x y q₂ q₄'' q₅) (⊆ub (⊢supp q₃ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢supp＝Ty¹₂ C' x q₀ q₄') (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₂ c₊' x y q₂ q₄''' q₅') (⊢supp q₃ ∘ ∈∪₂))))
      ((⊆ub (⊢supp＝Ty¹₁ C x q₀ q₄) (⊢supp q₃ ∘ ∈∪₁)) ∘ supp⟨⟩ C a))
⊢supp (𝚷Beta{a = a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) = ⊆ub
  (⊆ub (⊆ub (⊢supp¹ b x q₀ q₂') λ()) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))
  (⊆ub ((⊆ub (⊢supp¹ b x q₀ q₂') (⊢supp q₁ ∘ ∈∪₁)) ∘ supp⟨⟩ b a)
    ((⊆ub (⊢suppTy¹ B x h₁ q₂) (⊢supp q₁ ∘ ∈∪₁)) ∘ supp⟨⟩ B a))
⊢supp (𝐍𝐚𝐭Beta₀{C = C}{c₊ = c₊}{x}{y} q₀ q₁ (q₂ ∉∪ q₂') q₃ h) = ⊆ub
  (⊆ub (⊢suppTy¹ C x h q₂) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊢supp² c₊ x y q₁ q₂' q₃) (⊆ub (λ()) λ()))))
  (⊆ub (⊢supp q₀ ∘ ∈∪₁)
    ((⊆ub (⊢suppTy¹ C x h q₂) λ()) ∘ supp⟨⟩ C 𝐳𝐞𝐫𝐨))
⊢supp (𝐍𝐚𝐭Beta₊{C = C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ (q₃ ∉∪ q₃') q₄ h) = ⊆ub
  (⊆ub (⊢suppTy¹ C x h q₃) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊢supp² c₊ x y q₁ q₃' q₄) (⊆ub (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ()) λ()))))
  (⊆ub
    ((⊆ub (⊆ub (⊢supp² c₊ x y q₁ q₃' q₄) (⊢supp q₂ ∘ ∈∪₁))
      (⊆ub (⊢suppTy¹ C x h q₃) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
        (⊆ub (⊢supp² c₊ x y q₁ q₃' q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ())))))
          ∘ supp⟨⟩² c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a))
    ((⊆ub (⊢suppTy¹ C x h q₃) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ()))
      ∘ supp⟨⟩ C (𝐬𝐮𝐜𝐜 a)))
⊢supp (𝚷Eta{A = A}{B}{b}{x} q₀ q₁ h) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊆ub (⊆ub ((⊢supp q₀ ∘ ∈∪₁) ∘ suppAbs x b)
    (⊆ub (λ{y} p → Øelim (∉→¬∈ (y#x．𝐯x x y) p)) λ())) λ())
    (⊆ub (⊢supp h)
      (⊆ub (⊢suppTy¹ B x q₁ (⊆∉ (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) it)) λ())))
⊢supp (UIP q₀ q₁ q₂ h) = ⊆ub
  (⊢supp q₂ ∘ ∈∪₁)
  (⊆ub (λ()) (⊆ub ( ⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ())))

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

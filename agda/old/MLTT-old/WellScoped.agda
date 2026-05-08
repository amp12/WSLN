module MLTT.WellScoped where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem
open import MLTT.Ok

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

Oksupp ([] p _ _)  isInNew     = ∈∪₁ ∘ ⊢supp p ∘ ∈∪₁
Oksupp ([] ⊢A _ p) (isInOld q) = ∈∪₁ ∘ Oksupp p q

⊢supp¹ :
  {Γ : Cx}
  {A B : Ty}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢ b [ x ] ∶ B ⦂ l')
  (_ : x # b)
  → --------------------------------------
  supp b ⊆ dom Γ

⊢supp¹ b x p x#b q
    with ⊢supp p (∈∪₁ ([]supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x#b q)

⊢supp² :
  {Γ : Cx}
  {A B C : Ty}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢
    c [ x ][ y ] ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → ----------------------------------
  supp c ⊆ dom Γ

⊢supp² c x y p x#c y#c q
    with ⊢supp p (∈∪₁ ([]²supp c (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x#c q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y#c q)

⊢supp＝¹₁ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢
    b [ x ] ＝ b' ∶ B ⦂ l')
  (_ : x # b)
  → -----------------------
  supp b ⊆ dom Γ

⊢supp＝¹₁ b x p x#b q
    with ⊢supp p (∈∪₁ ([]supp b (𝐯 x) q))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x#b q)

⊢supp＝¹₂ :
  {Γ : Cx}
  {A B : Ty}
  {b' : Tm}
  {l l' : Lvl}
  (b : Tm[ 1 ])
  (x : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l) ⊢
    b' ＝ b [ x ] ∶ B ⦂ l')
  (_ : x # b)
  → ----------------------
  supp b ⊆ dom Γ

⊢supp＝¹₂ b x p x#b q
    with ⊢supp p ((∈∪₂ (∈∪₁ ([]supp b (𝐯 x) q))))
... | ∈∪₁ x∈Γ = x∈Γ
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ x#b q)

⊢supp＝²₁ :
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢
    c [ x ][ y ] ＝ c' ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → ----------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₁ c x y p x#c y#c q
    with ⊢supp p (∈∪₁ ([]²supp c (𝐯 x) (𝐯 y) q))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x#c q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y#c q)

⊢supp＝²₂ :
  {Γ : Cx}
  {A B C : Ty}
  {c' : Tm}
  {l l' l'' : Lvl}
  (c : Tm[ 2 ])
  (x y : 𝔸)
  (_ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢
    c' ＝ c [ x ][ y ] ∶ C ⦂ l'')
  (_ : x # c)
  (_ : y # c)
  → ----------------------------------
  supp c ⊆ dom Γ

⊢supp＝²₂ c x y p x#c y#c q
    with ⊢supp p (∈∪₂ (∈∪₁ ([]²supp c (𝐯 x) (𝐯 y) q)))
... | ∈∪₁ (∈∪₁ x∈Γ) = x∈Γ
... | ∈∪₁ (∈∪₂ ∈｛｝) = Øelim (∉→¬∈ x#c q)
... | ∈∪₂ ∈｛｝ = Øelim (∉→¬∈ y#c q)

⊢supp (⊢conv q₀ q₁) = ⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁)
⊢supp (⊢𝐯 q₀ q₁) = ⊆ub (λ{∈｛｝ → isIn→dom q₁}) (Oksupp q₀ q₁)
⊢supp (⊢𝐔 _) = ⊆ub (λ()) λ()
⊢supp (⊢𝚷{B = B}{x} q₀ q₁ q₂) =
  ⊆ub
    (⊆ub
      (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp¹ B x q₁ q₂) λ()))
  λ()
⊢supp (⊢𝛌{B = B}{b}{x} q₀ (q₁ ∉∪ q₁') h₀ h₁) = ⊆ub
  (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ b x q₀ q₁') λ()))
  (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ B x h₁ q₁) λ()))
⊢supp (⊢∙{B = B}{a}{x = x}  q₀ q₁ q₂ q₃ h) =
  -- helper used here
  ⊆ub
   (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp h ∘ ∈∪₁)
     (⊆ub (⊢supp¹ B x q₂ q₃) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))))
   (⊆ub (⊢supp¹ B x q₂ q₃) (⊢supp q₁ ∘ ∈∪₁) ∘ supp[] B a)
⊢supp (⊢𝐈𝐝 q₀ q₁ h) = ⊆ub
  (⊆ub (⊢supp h ∘ ∈∪₁) (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ())))
  λ()
⊢supp (⊢𝐫𝐞𝐟𝐥 q _) = ⊆ub
  (⊆ub (⊢supp q ∘ ∈∪₁) λ())
  (⊆ub (⊢supp q ∘ ∈∪₂)
    (⊆ub (⊢supp q ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) λ())))
⊢supp (⊢𝐉{C = C}{b = b}{e = e}{x = x}{y} q₀ q₁ q₂ q₃ q₄ q₅ q₆ h _) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp² C x y q₀ q₅ q₆) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
      (⊆ub (⊢supp q₂ ∘ ∈∪₁) (⊆ub (⊢supp q₃ ∘ ∈∪₁)
        (⊆ub (⊢supp q₄ ∘ ∈∪₁) (λ()))))))
    (⊆ub
      (⊆ub (⊢supp² C x y q₀ q₅ q₆) (⊢supp q₂ ∘ ∈∪₁))
        (⊢supp q₄ ∘ ∈∪₁) ∘ supp[]² C b e)
⊢supp (⊢𝐍𝐚𝐭 _) = ⊆ub (λ()) λ()
⊢supp (⊢𝐳𝐞𝐫𝐨 _) = ⊆ub (λ()) λ()
⊢supp (⊢𝐬𝐮𝐜𝐜 q) = ⊆ub (⊢supp q) λ()
⊢supp (⊢𝐧𝐫𝐞𝐜{C = C}{a = a}{c₊ = c₊}{x}{y} q₀ q₁ q₂ q₃ q₄ h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp¹ C x h (∉∪₁ q₃)) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())))))
    (⊆ub (⊢supp¹ C x h (∉∪₁ q₃)) (⊢supp q₂ ∘ ∈∪₁) ∘ supp[] C a)
⊢supp (Refl q) = ⊆ub
  (⊢supp q ∘ ∈∪₁)
  (⊆ub (⊢supp q ∘ ∈∪₁) (⊢supp q ∘ ∈∪₂))
⊢supp (Symm q) = ⊆ub
  (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁)
  (⊆ub (⊢supp q ∘ ∈∪₁) (⊢supp q ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp (Trans q₀ q₁) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂))
⊢supp (＝conv q₀ q₁) = ⊆ub
  (⊢supp q₀ ∘ ∈∪₁)
  (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁))
⊢supp (𝚷Cong{B = B}{B'}{x} q₀ q₁ q₂ _) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₁ B x q₁ (∉∪₁ q₂)) λ()))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp＝¹₂ B' x q₁ (∉∪₂ q₂)) λ())) λ())
⊢supp (𝛌Cong{B = B}{b}{b'}{x} q₀ q₁ (q₂ ∉∪ q₂' ∉∪ q₂'') h₀ h₁) = ⊆ub
  (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₁ b x q₁ q₂') λ()))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₂ b' x q₁ q₂'') λ()))
    (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ B x h₁ q₂) λ())))
⊢supp (∙Cong{B = B}{B'}{a = a}{x = x} q₀ q₁ q₂ q₃ q₄ _ _) = ⊆ub
  (⊆ub (⊢supp q₂ ∘ ∈∪₁) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊢supp＝¹₁ B x q₁ (∉∪₁ q₄)) (⊆ub (⊢supp q₃ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp＝¹₂ B' x q₁ (∉∪₂ q₄))
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) λ()))))
      (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁)
        (⊢supp q₃ ∘ ∈∪₁) ∘ supp[] B a))
⊢supp (𝐈𝐝Cong q₀ q₁ q₂) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ())))
  (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁) λ())))
    λ())
⊢supp (𝐫𝐞𝐟𝐥Cong q h) =
  -- helper used here
  ⊆ub
    (⊆ub (⊢supp q ∘ ∈∪₁) λ())
    (⊆ub (⊆ub (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) λ())
      (⊆ub (⊢supp h ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) (⊆ub (⊢supp q ∘ ∈∪₁) λ()))))
⊢supp (𝐉Cong{C = C}{C'}{b = b}{e = e}{x = x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ _ _) = ⊆ub
  (⊆ub (⊢supp＝²₁ C x y q₀ (∉∪₁ q₅) (∉∪₁ q₆))
    (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁)
      (⊆ub (⊢supp q₃ ∘ ∈∪₁) (⊆ub (⊢supp q₄ ∘ ∈∪₁) λ())))))
  (⊆ub (⊆ub (⊢supp＝²₂ C' x y q₀ (∉∪₂ q₅) (∉∪₂ q₆))
    (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₂ ∘ ∈∪₁)
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) (⊆ub (⊢supp q₄ ∘ ∈∪₂ ∘ ∈∪₁) λ())))))
        (⊆ub (⊆ub (⊢supp＝²₁ C x y q₀ (∉∪₁ q₅) (∉∪₁ q₆)) (⊢supp q₂ ∘ ∈∪₁))
          (⊢supp q₄ ∘ ∈∪₁) ∘ supp[]² C b e))
⊢supp (𝐬𝐮𝐜𝐜Cong q) = ⊆ub
  (⊆ub (⊢supp q ∘ ∈∪₁) λ())
  (⊆ub (⊆ub (⊢supp q ∘ ∈∪₂ ∘ ∈∪₁) λ()) λ())
⊢supp (𝐧𝐫𝐞𝐜Cong{C = C}{C'}{a = a}{c₊ = c₊}{c₊'}{x}{y}
  q₀ q₁ q₂ q₃ (q₄ ∉∪ q₄' ∉∪ q₄'' ∉∪ q₄''') (q₅ ∉∪ q₅') _) = ⊆ub
  (⊆ub (⊢supp＝¹₁ C x q₀ q₄) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₁ c₊ x y q₂ q₄'' q₅) (⊆ub (⊢supp q₃ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢supp＝¹₂ C' x q₀ q₄') (⊆ub (⊢supp q₁ ∘ ∈∪₂ ∘ ∈∪₁)
    (⊆ub (⊢supp＝²₂ c₊' x y q₂ q₄''' q₅')
      (⊆ub (⊢supp q₃ ∘ ∈∪₂ ∘ ∈∪₁) λ()))))
        (⊆ub (⊢supp＝¹₁ C x q₀ q₄) (⊢supp q₃ ∘ ∈∪₁) ∘ supp[] C a))
⊢supp (𝚷Beta{a = a}{B}{b}{x} q₀ q₁ (q₂ ∉∪ q₂') h₀ h₁) = ⊆ub
  (⊆ub (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ b x q₀ q₂') λ()))
    (⊆ub (⊢supp h₀ ∘ ∈∪₁) (⊆ub (⊢supp¹ B x h₁ q₂) (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()))))
  (⊆ub (⊆ub (⊢supp¹ b x q₀ q₂') (⊢supp q₁ ∘ ∈∪₁) ∘ supp[] b a)
    (⊆ub (⊢supp¹ B x h₁ q₂) (⊢supp q₁ ∘ ∈∪₁) ∘ supp[] B a))
⊢supp (𝐈𝐝Beta{C = C}{a}{x = x}{y} q₀ q₁ q₂ q₃ q₄ _ _) = ⊆ub
  (⊆ub (⊢supp² C x y q₀ q₃ q₄) (⊆ub (⊢supp q₁ ∘ ∈∪₁)
    (⊆ub (⊢supp q₁ ∘ ∈∪₁) (⊆ub (⊢supp q₂ ∘ ∈∪₁)
      (⊆ub (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()) λ())))))
  (⊆ub (⊢supp q₂ ∘ ∈∪₁)
    (⊆ub (⊆ub (⊢supp² C x y q₀ q₃ q₄) (⊢supp q₁ ∘ ∈∪₁))
      (⊆ub (⊢supp q₁ ∘ ∈∪₁) λ()) ∘ supp[]² C a (𝐫𝐞𝐟𝐥 a)))
⊢supp (𝐍𝐚𝐭Beta₀{C = C}{c₊ = c₊}{x}{y} q₀ q₁ q₂ q₃ _) =
  ⊆ub
    (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₂) q₃) (⊆ub (λ()) λ()))))
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊢supp q₀ ∘ ∈∪₂))
⊢supp (𝐍𝐚𝐭Beta₊{C = C}{c₀}{a}{c₊}{x}{y} q₀ q₁ q₂ q₃ q₄ h) = ⊆ub
  (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨)
    (⊆ub (⊢supp q₀ ∘ ∈∪₁) (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄)
      (⊆ub (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())) λ()))))
  (⊆ub (⊆ub (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊢supp q₂ ∘ ∈∪₁))
    (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₀ ∘ ∈∪₁)
      (⊆ub (⊢supp² c₊ x y q₁ (∉∪₂ q₃) q₄) (⊆ub (⊢supp q₂ ∘ ∈∪₁) λ()))))
        ∘ supp[]² c₊ a (𝐧𝐫𝐞𝐜 C c₀ c₊ a))
    ((⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ []supp C 𝐳𝐞𝐫𝐨) (⊆ub (⊢supp q₂ ∘ ∈∪₁) (λ())))
      ∘ supp[] C (𝐬𝐮𝐜𝐜 a)))
⊢supp{Γ} (𝚷Eta{A = A}{B}{b}{x} q₀ q₁ h) =
  -- helpers used here
  ⊆ub
    (⊢supp q₀ ∘ ∈∪₁)
    (⊆ub (⊆ub (⊢supp h ∘ ∈∪₁) (⊆ub (⊆ub (⊢supp q₀ ∘ ∈∪₁ ∘ suppAbs x b)
      (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₁ ∘ suppAbs x A)
      (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁ ∘ suppCls x (suc^ zero) B refl)
        (⊆ub (∉⊆ (#abs x (𝐯 x)) (∈∪₂ ∘ suppAbs x (𝐯 x))) λ())))) λ()))
        (⊆ub (⊢supp h ∘ ∈∪₁) (⊆ub (⊢supp q₀ ∘ ∈∪₂ ∘ ∈∪₂ ∘ ∈∪₁) λ())))

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

dom＝ ([] q _ _ _ _) (∈∪₁ x∈Γ) = ∈∪₁ (dom＝ q x∈Γ)
dom＝ ([] _ _ _ _ _) (∈∪₂ ∈｛｝) = ∈∪₂ ∈｛｝

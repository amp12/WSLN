module ETT.AltTypeSystem where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem

----------------------------------------------------------------------
-- Provable judgements in context: alternative definition using only
-- judgements of the form a ∶ A ⦂ l and a ＝ a' ∶ A ⦂ l
----------------------------------------------------------------------
infix 3 _⊢ᵃ_
data Okᵃ : Cx → Set
data _⊢ᵃ_ (Γ : Cx) : Jg → Set

data Okᵃ where
  ◇ : Okᵃ ◇
  ∷ :
    {l : Lvl}
    {Γ : Cx}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    -- helper hypothesis
    (h : Okᵃ Γ)
    → -----------------------
    Okᵃ (Γ ⸴ x ∶ A ⦂ l)

data _⊢ᵃ_  Γ where
  ⊢ᵃ𝐔 :
    {l : Lvl}
    (q : Okᵃ Γ)
    → -------------------------
    Γ ⊢ᵃ 𝐔 l ∶ 𝐔 (1 + l) ⦂ 2+ l

  ⊢ᵃ𝚷 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    (q₂ : x # B)
    → ---------------------------------------
    Γ ⊢ᵃ 𝚷 A B ∶ 𝐔 (max l l') ⦂ 1+ (max l l')

  ⊢ᵃ𝐈𝐝 :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ a' ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → -------------------------
    Γ ⊢ᵃ 𝐈𝐝 A a a' ∶ 𝐔 l ⦂ 1+ l

  ⊢ᵃ𝐍𝐚𝐭 :
    (q : Okᵃ Γ)
    → ---------------
    Γ ⊢ᵃ 𝐍𝐚𝐭 ∶ 𝐔 0 ⦂ 1

  ⊢ᵃconv :
    {l : Lvl}
    {a : Tm}
    {A A' : Ty}
    (q₀ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    → -----------------------------
    Γ ⊢ᵃ a ∶ A' ⦂ l

  ⊢ᵃ𝐯 :
    {l : Lvl}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Okᵃ Γ)
    (q₁ : (x , A , l) isIn Γ)
    → -----------------------
    Γ ⊢ᵃ 𝐯 x ∶ A ⦂ l

  ⊢ᵃ𝛌 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # (B , b))
    -- helper hypotheses
    (h₀ : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    → ---------------------------
    Γ ⊢ᵃ 𝛌 A b ∶ 𝚷 A B ⦂ max l l'

  ⊢ᵃ∙ :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₂ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    (q₃ : x # B)
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → ------------------------------
    Γ ⊢ᵃ b ∙[ A , B ] a ∶ B ⟨ a ⟩ ⦂ l'

  ⊢ᵃ𝐫𝐞𝐟𝐥 :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ᵃ a ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → ------------------------
    Γ ⊢ᵃ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ⦂ l

  ⊢ᵃ𝐳𝐞𝐫𝐨 :
    (q : Okᵃ Γ)
    → ----------------
    Γ ⊢ᵃ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 ⦂ 0

  ⊢ᵃ𝐬𝐮𝐜𝐜 :
    {a : Tm}
    (q : Γ ⊢ᵃ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    → -------------------
    Γ ⊢ᵃ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭 ⦂ 0

  ⊢ᵃ𝐧𝐫𝐞𝐜 :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ᵃ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢ᵃ
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : Γ ⊢ᵃ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    --  helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ᵃ C ⟨ x ⟩ ∶ 𝐔 l ⦂ 1+ l)
    → --------------------------------------------
    Γ ⊢ᵃ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ⦂ l

  𝚷Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : Γ ⸴ x ∶ A ⦂ l ⊢ᵃ
      B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    (q₂ : x # (B , B'))
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → --------------------------------------------------
    Γ ⊢ᵃ 𝚷 A B ＝ 𝚷 A' B' ∶ 𝐔 (max l l') ⦂ 1+ (max l l')

  𝐈𝐝Cong :
    {l : Lvl}
    {A A' : Ty}
    {a a' b b' : Tm}
    (q₀ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
    (q₂ : Γ ⊢ᵃ b ＝ b' ∶ A ⦂ l)
    → ---------------------------------------
    Γ ⊢ᵃ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ∶ 𝐔 l ⦂ 1+ l

  Refl :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ᵃ a ∶ A ⦂ l)
    → -----------------
    Γ ⊢ᵃ a ＝ a ∶ A ⦂ l

  Symm :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
    → -----------------------
    Γ ⊢ᵃ a' ＝ a ∶ A ⦂ l

  Trans :
    {l : Lvl}
    {A : Ty}
    {a a' a'' : Tm}
    (q₀ : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ a' ＝ a'' ∶ A ⦂ l)
    → -------------------------
    Γ ⊢ᵃ a ＝ a'' ∶ A ⦂ l

  ＝conv :
    {l : Lvl}
    {A A' : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    → -----------------------------
    Γ ⊢ᵃ a ＝ a' ∶ A' ⦂ l

  ⊢ᵃReflect :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ b ∶ A ⦂ l)
    (q₂ : Γ ⊢ᵃ e ∶ 𝐈𝐝 A a b ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → --------------------------
    Γ ⊢ᵃ a ＝ b ∶ A ⦂ l

  𝛌Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B : Ty[ 1 ]}
    {b b' : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₂ : x # (B , b , b'))
    -- helper hypothesis
    (h₀ : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    → ----------------------------------------------
    Γ ⊢ᵃ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B ⦂ max l l'

  ∙Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {a a' b b' : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : Γ ⸴ x ∶ A ⦂ l ⊢ᵃ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    (q₂ : Γ ⊢ᵃ b ＝ b' ∶ 𝚷 A B ⦂ max l l')
    (q₃ : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
    (q₄ : x # (B , B'))
    -- helper hypotheses
    (h₀ : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    → -------------------------------------------------------
    Γ ⊢ᵃ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B ⟨ a ⟩ ⦂ l'

  𝐬𝐮𝐜𝐜Cong :
    {a a' : Tm}
    (q : Γ ⊢ᵃ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    → -----------------------------
    Γ ⊢ᵃ 𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭 ⦂ 0

  𝐧𝐫𝐞𝐜Cong :
    {l : Lvl}
    {C C' : Ty[ 1 ]}
    {c₀ c₀' a a'  : Tm}
    {c₊ c₊' : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢ᵃ
      C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ∶ 𝐔 l ⦂ 1+ l)
    (q₁ : Γ ⊢ᵃ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₂ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l ⊢ᵃ
      c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₃ : Γ ⊢ᵃ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₄ : x # (C , C' , c₊ , c₊'))
    (q₅ : y # (c₊ , c₊'))
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ᵃ C ⟨ x ⟩ ∶ 𝐔 l ⦂ 1+ l)
    → ------------------------------------------------------
    Γ ⊢ᵃ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩ ⦂ l

  𝚷Beta :
    {l l' : Lvl}
    {A : Ty}
    {a : Tm}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₂ : x # (B , b))
    -- helper hypothesis
    (h₀ : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    → -------------------------------------------------
    Γ ⊢ᵃ (𝛌 A b) ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ⦂ l'

  𝐍𝐚𝐭Beta₀ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ᵃ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢ᵃ
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : x # (C , c₊))
    (q₃ : y # c₊)
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ᵃ C ⟨ x ⟩ ∶ 𝐔 l ⦂ 1+ l)
    → --------------------------------------------
    Γ ⊢ᵃ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l

  𝐍𝐚𝐭Beta₊ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ᵃ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢ᵃ
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : Γ ⊢ᵃ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ᵃ C ⟨ x ⟩ ∶ 𝐔 l ⦂ 1+ l)
    → --------------------------------------------
    Γ ⊢ᵃ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ⦂ l

  𝚷Eta :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ᵃ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ᵃ
      B ⟨ x ⟩ ∶ 𝐔 l' ⦂ 1+ l')
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → -------------------------------------------------------
    Γ ⊢ᵃ b ＝ 𝛌 A (x ．(b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B ⦂ max l l'

  UIP :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ᵃ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ᵃ b ∶ A ⦂ l)
    (q₂ : Γ ⊢ᵃ e ∶ 𝐈𝐝 A a b ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)
    → -----------------------------
    Γ ⊢ᵃ e ＝ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a b ⦂ l

----------------------------------------------------------------------
-- Standard implies alternate
----------------------------------------------------------------------
Ok→Okᵃ : ∀{Γ} → Ok Γ → Okᵃ Γ
⊢Ty→⊢ᵃ : ∀{Γ l A} → Γ ⊢ A ⦂ l → Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l
⊢Tm→⊢ᵃ : ∀{Γ l A a} → Γ ⊢ a ∶ A ⦂ l → Γ ⊢ᵃ a ∶ A ⦂ l
＝Ty→⊢ᵃ : ∀{Γ l A A'} → Γ ⊢ A ＝ A' ⦂ l → Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l
＝Tm→⊢ᵃ : ∀{Γ l A a a'} → Γ ⊢ a ＝ a' ∶ A ⦂ l → Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l

Ok→Okᵃ ◇ = ◇
Ok→Okᵃ (∷ q₀ q₁) = ∷ (⊢Ty→⊢ᵃ q₀) (Ok→Okᵃ q₁)

⊢Ty→⊢ᵃ (⊢𝐔 q) = ⊢ᵃ𝐔 (Ok→Okᵃ q)
⊢Ty→⊢ᵃ (⊢𝚷 q₀ q₁ q₂) = ⊢ᵃ𝚷 (⊢Ty→⊢ᵃ q₀) (⊢Ty→⊢ᵃ q₁) q₂
⊢Ty→⊢ᵃ (⊢𝐈𝐝 q₀ q₁ q₂) = ⊢ᵃ𝐈𝐝 (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) (⊢Ty→⊢ᵃ q₂)
⊢Ty→⊢ᵃ (⊢𝐍𝐚𝐭 q) = ⊢ᵃ𝐍𝐚𝐭 (Ok→Okᵃ q)
⊢Ty→⊢ᵃ (Tm→Ty q) = ⊢Tm→⊢ᵃ q

⊢Tm→⊢ᵃ (⊢conv q₀ q₁) = ⊢ᵃconv (⊢Tm→⊢ᵃ q₀) (＝Ty→⊢ᵃ q₁)
⊢Tm→⊢ᵃ (⊢𝐯 q₀ q₁) = ⊢ᵃ𝐯 (Ok→Okᵃ q₀) q₁
⊢Tm→⊢ᵃ (Ty→Tm q) = ⊢Ty→⊢ᵃ q
⊢Tm→⊢ᵃ (⊢𝛌 q₀ q₁ q₂ q₃) =
  ⊢ᵃ𝛌 (⊢Tm→⊢ᵃ q₀) q₁ (⊢Ty→⊢ᵃ q₂) (⊢Ty→⊢ᵃ q₃)
⊢Tm→⊢ᵃ (⊢∙ q q₁ q₂ q₃ q₄) =
  ⊢ᵃ∙ (⊢Tm→⊢ᵃ q) (⊢Tm→⊢ᵃ q₁) (⊢Ty→⊢ᵃ q₂) q₃ (⊢Ty→⊢ᵃ q₄)
⊢Tm→⊢ᵃ (⊢𝐫𝐞𝐟𝐥 q₀ q₁) = ⊢ᵃ𝐫𝐞𝐟𝐥 (⊢Tm→⊢ᵃ q₀) (⊢Ty→⊢ᵃ q₁)
⊢Tm→⊢ᵃ (⊢𝐳𝐞𝐫𝐨 q) = ⊢ᵃ𝐳𝐞𝐫𝐨 (Ok→Okᵃ q)
⊢Tm→⊢ᵃ (⊢𝐬𝐮𝐜𝐜 q) = ⊢ᵃ𝐬𝐮𝐜𝐜 (⊢Tm→⊢ᵃ q)
⊢Tm→⊢ᵃ (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ q₅) =
  ⊢ᵃ𝐧𝐫𝐞𝐜 (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) (⊢Tm→⊢ᵃ q₂) q₃ q₄ (⊢Ty→⊢ᵃ q₅)

＝Ty→⊢ᵃ (TyRefl q) = Refl (⊢Ty→⊢ᵃ q)
＝Ty→⊢ᵃ (TySymm q) = Symm (＝Ty→⊢ᵃ q)
＝Ty→⊢ᵃ (TyTrans q₀ q₁) = Trans (＝Ty→⊢ᵃ q₀) (＝Ty→⊢ᵃ q₁)
＝Ty→⊢ᵃ (𝚷Cong q₀ q₁ q₂ q₃) =
  𝚷Cong (＝Ty→⊢ᵃ q₀) (＝Ty→⊢ᵃ q₁) q₂ (⊢Ty→⊢ᵃ q₃)
＝Ty→⊢ᵃ (𝐈𝐝Cong q₀ q₁ q₂) = 𝐈𝐝Cong (＝Ty→⊢ᵃ q₀) (＝Tm→⊢ᵃ q₁) (＝Tm→⊢ᵃ q₂)
＝Ty→⊢ᵃ (=Tm→Ty q) = ＝Tm→⊢ᵃ q

＝Tm→⊢ᵃ (TmRefl q) = Refl (⊢Tm→⊢ᵃ q)
＝Tm→⊢ᵃ (TmSymm q) = Symm (＝Tm→⊢ᵃ q)
＝Tm→⊢ᵃ (TmTrans q₀ q₁) = Trans (＝Tm→⊢ᵃ q₀) (＝Tm→⊢ᵃ q₁)
＝Tm→⊢ᵃ (＝conv q₀ q₁) = ＝conv (＝Tm→⊢ᵃ q₀) (＝Ty→⊢ᵃ q₁)
＝Tm→⊢ᵃ (=Ty→Tm q) = ＝Ty→⊢ᵃ q
＝Tm→⊢ᵃ (⊢Reflect q₀ q₁ q₂ q₃) =
  ⊢ᵃReflect (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) (⊢Tm→⊢ᵃ q₂) (⊢Ty→⊢ᵃ q₃)
＝Tm→⊢ᵃ (𝛌Cong q₀ q₁ q₂ h₀ h₁) =
  𝛌Cong (＝Ty→⊢ᵃ q₀) (＝Tm→⊢ᵃ q₁) q₂ (⊢Ty→⊢ᵃ h₀) (⊢Ty→⊢ᵃ h₁)
＝Tm→⊢ᵃ (∙Cong q₀ q₁ q₂ q₃ q₄ h₀ h₁) =
  ∙Cong (＝Ty→⊢ᵃ q₀) (＝Ty→⊢ᵃ q₁) (＝Tm→⊢ᵃ q₂) (＝Tm→⊢ᵃ q₃) q₄ (⊢Ty→⊢ᵃ h₀) (⊢Ty→⊢ᵃ h₁)
＝Tm→⊢ᵃ (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (＝Tm→⊢ᵃ q)
＝Tm→⊢ᵃ (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
  𝐧𝐫𝐞𝐜Cong (＝Ty→⊢ᵃ q₀) (＝Tm→⊢ᵃ q₁) (＝Tm→⊢ᵃ q₂) (＝Tm→⊢ᵃ q₃) q₄ q₅ (⊢Ty→⊢ᵃ q₆)
＝Tm→⊢ᵃ (𝚷Beta{B = B} q₀ q₁ q₂ q₃ q₄) =
  𝚷Beta{B = B} (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) q₂ (⊢Ty→⊢ᵃ q₃) (⊢Ty→⊢ᵃ q₄)
＝Tm→⊢ᵃ (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ q₄) =
  𝐍𝐚𝐭Beta₀ (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) q₂ q₃ (⊢Ty→⊢ᵃ q₄)
＝Tm→⊢ᵃ (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ q₅) =
  𝐍𝐚𝐭Beta₊ (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) (⊢Tm→⊢ᵃ q₂) q₃ q₄ (⊢Ty→⊢ᵃ q₅)
＝Tm→⊢ᵃ (𝚷Eta q₀ q₁ q₂) =
  𝚷Eta (⊢Tm→⊢ᵃ q₀) (⊢Ty→⊢ᵃ q₁) (⊢Ty→⊢ᵃ q₂)
＝Tm→⊢ᵃ (UIP q₀ q₁ q₂ q₃) =
  UIP (⊢Tm→⊢ᵃ q₀) (⊢Tm→⊢ᵃ q₁) (⊢Tm→⊢ᵃ q₂) (⊢Ty→⊢ᵃ q₃)

----------------------------------------------------------------------
-- Alternate implies standard
----------------------------------------------------------------------
Okᵃ→Ok :
  {Γ : Cx}
  (_ : Okᵃ Γ)
  → ---------
  Ok Γ
⊢ᵃTy→⊢ :
  {Γ : Cx}
  {l m : Lvl}
  {A B : Ty}
  (_ : Γ ⊢ᵃ A ∶ B ⦂ m)
  (_ : B ≡ 𝐔 l)
  (_ : m ≡ 1+ l)
  → ------------------
  Γ ⊢ A ⦂ l
⊢ᵃTm→⊢ :
  {Γ : Cx}
  {l : Lvl}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ᵃ a ∶ A ⦂ l)
  → ------------------
  Γ ⊢ a ∶ A ⦂ l
＝ᵃTy→⊢ :
  {Γ : Cx}
  {l m : Lvl}
  {A A' B : Ty}
  (_ : Γ ⊢ᵃ A ＝ A' ∶ B ⦂ m)
  (_ : B ≡ 𝐔 l)
  (_ : m ≡ 1+ l)
  → ------------------------
  Γ ⊢ A ＝ A' ⦂ l
＝ᵃTm→⊢ :
  {Γ : Cx}
  {l : Lvl}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)
  → ------------------------
  Γ ⊢ a ＝ a' ∶ A ⦂ l

Okᵃ→Ok ◇ = ◇
Okᵃ→Ok (∷ q₀ q₁) = ∷ (⊢ᵃTy→⊢ q₀ refl refl) (Okᵃ→Ok q₁)

⊢ᵃTy→⊢ (⊢ᵃ𝐔 q) refl e
  with refl ← ! ⦃ !≡ ⦄ e refl = ⊢𝐔 (Okᵃ→Ok q)
⊢ᵃTy→⊢ (⊢ᵃ𝚷 q₀ q₁ q₂) refl e
  with refl ← ! ⦃ !≡ ⦄ e refl =
  ⊢𝚷 (⊢ᵃTy→⊢ q₀ refl refl) (⊢ᵃTy→⊢ q₁ refl refl) q₂
⊢ᵃTy→⊢ (⊢ᵃ𝐈𝐝 q₀ q₁ q₂) refl e
  with refl ← ! ⦃ !≡ ⦄ e refl =
  ⊢𝐈𝐝 (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (⊢ᵃTy→⊢ q₂ refl refl)
⊢ᵃTy→⊢ (⊢ᵃ𝐍𝐚𝐭 q) refl refl = ⊢𝐍𝐚𝐭 (Okᵃ→Ok q)
⊢ᵃTy→⊢ (⊢ᵃconv q₀ q₁) refl refl =
  Tm→Ty (⊢conv (⊢ᵃTm→⊢ q₀) (=Tm→Ty (＝ᵃTm→⊢ q₁)))
⊢ᵃTy→⊢ (⊢ᵃ𝐯 q₀ q₁) refl refl = Tm→Ty (⊢𝐯 (Okᵃ→Ok q₀) q₁)
⊢ᵃTy→⊢{Γ}{l} (⊢ᵃ∙{a = a}{b} q₀ q₁ q₂ q₃ q₄) e refl = {!!}
  -- Tm→Ty (subst (λ C → Γ ⊢ b ∙ a ∶ C ⦂ 1+ l) e
  --   (⊢∙ (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁)
  --     (Tm→Ty (⊢ᵃTm→⊢ q₂)) q₃ (Tm→Ty (⊢ᵃTm→⊢ q₄))))
⊢ᵃTy→⊢{Γ}{l} (⊢ᵃ𝐧𝐫𝐞𝐜{C = C}{c₀}{a}{c₊} q₀ q₁ q₂ q₃ q₄ q₅) e refl =
  Tm→Ty (subst (λ C' →  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C' ⦂ 1+ l) e
    (⊢𝐧𝐫𝐞𝐜{C = C}{c₊ = c₊} (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁)
      (⊢ᵃTm→⊢ q₂) q₃ q₄ (Tm→Ty (⊢ᵃTm→⊢ q₅))))

⊢ᵃTm→⊢ (⊢ᵃ𝐔 q) = Ty→Tm (⊢𝐔 (Okᵃ→Ok q))
⊢ᵃTm→⊢ (⊢ᵃ𝚷 q₀ q₁ q₂) = Ty→Tm
  (⊢𝚷 (Tm→Ty (⊢ᵃTm→⊢ q₀)) (Tm→Ty (⊢ᵃTm→⊢ q₁)) q₂)
⊢ᵃTm→⊢ (⊢ᵃ𝐈𝐝 q₀ q₁ q₂) = Ty→Tm
  (⊢𝐈𝐝 (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (Tm→Ty (⊢ᵃTm→⊢ q₂)))
⊢ᵃTm→⊢ (⊢ᵃ𝐍𝐚𝐭 q) = Ty→Tm (⊢𝐍𝐚𝐭 (Okᵃ→Ok q))
⊢ᵃTm→⊢ (⊢ᵃconv q₀ q₁) = ⊢conv (⊢ᵃTm→⊢ q₀) (=Tm→Ty (＝ᵃTm→⊢ q₁))
⊢ᵃTm→⊢ (⊢ᵃ𝐯 q₀ q₁) = ⊢𝐯 (Okᵃ→Ok q₀) q₁
⊢ᵃTm→⊢ (⊢ᵃ𝛌 q₀ q₁ q₂ q₃) =
  ⊢𝛌 (⊢ᵃTm→⊢ q₀) q₁ (Tm→Ty (⊢ᵃTm→⊢ q₂)) (Tm→Ty (⊢ᵃTm→⊢ q₃))
⊢ᵃTm→⊢ (⊢ᵃ∙ q₀ q₁ q₂ q₃ q₄) =
  ⊢∙ (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (Tm→Ty (⊢ᵃTm→⊢ q₂)) q₃ (Tm→Ty (⊢ᵃTm→⊢ q₄))
⊢ᵃTm→⊢ (⊢ᵃ𝐫𝐞𝐟𝐥 q₀ q₁) = ⊢𝐫𝐞𝐟𝐥 (⊢ᵃTm→⊢ q₀) (Tm→Ty (⊢ᵃTm→⊢ q₁))
⊢ᵃTm→⊢ (⊢ᵃ𝐳𝐞𝐫𝐨 q) = ⊢𝐳𝐞𝐫𝐨 (Okᵃ→Ok q)
⊢ᵃTm→⊢ (⊢ᵃ𝐬𝐮𝐜𝐜 q) = ⊢𝐬𝐮𝐜𝐜 (⊢ᵃTm→⊢ q)
⊢ᵃTm→⊢ (⊢ᵃ𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ q₅) =
  ⊢𝐧𝐫𝐞𝐜 (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (⊢ᵃTm→⊢ q₂) q₃ q₄ (Tm→Ty (⊢ᵃTm→⊢ q₅))

＝ᵃTy→⊢ (𝚷Cong q₀ q₁ q₂ q₃) refl e
  with refl ← ! ⦃ !≡ ⦄ e refl =
  𝚷Cong (＝ᵃTy→⊢ q₀ refl refl) (＝ᵃTy→⊢ q₁ refl refl) q₂ (Tm→Ty (⊢ᵃTm→⊢ q₃))
＝ᵃTy→⊢ (𝐈𝐝Cong q₀ q₁ q₂) refl e
  with refl ← ! ⦃ !≡ ⦄ e refl =  {!!}
  -- 𝐈𝐝Cong (＝ᵃTm→⊢ q₀) (＝ᵃTm→⊢ q₁) (Tm→Ty (⊢ᵃTm→⊢ q₂))
＝ᵃTy→⊢ (Refl q) refl refl = TyRefl (Tm→Ty (⊢ᵃTm→⊢ q))
＝ᵃTy→⊢ (Symm q) refl refl = TySymm (＝ᵃTy→⊢ q refl refl)
＝ᵃTy→⊢ (Trans q₀ q₁) refl refl =
  TyTrans (＝ᵃTy→⊢ q₀ refl refl) (＝ᵃTy→⊢ q₁ refl refl)
＝ᵃTy→⊢ (＝conv q₀ q₁) refl refl = =Tm→Ty
  (＝conv (＝ᵃTm→⊢ q₀) (=Tm→Ty (＝ᵃTm→⊢ q₁)))
＝ᵃTy→⊢ (⊢ᵃReflect q₀ q₁ q₂ q₃) refl refl =
  =Tm→Ty (⊢Reflect (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (⊢ᵃTm→⊢ q₂) (Tm→Ty (⊢ᵃTm→⊢ q₃)))
＝ᵃTy→⊢{Γ}{l} (∙Cong{B = B}{B'}{a}{a'}{b}{b'} q₀ q₁ q₂ q₃ q₄ h₀ h₁) e refl = =Tm→Ty
  {!!}
  -- =Tm→Ty
  -- (subst (λ C' → Γ ⊢ b ∙ a ＝ b' ∙ a' ∶ C' ⦂ 1+ l) e
  --   (∙Cong{B = B} (＝ᵃTm→⊢ q₀) (＝ᵃTm→⊢ q₁) q₂
  --     (Tm→Ty (⊢ᵃTm→⊢ q₃)) (Tm→Ty (⊢ᵃTm→⊢ q₄))))
＝ᵃTy→⊢{Γ}{l} (𝐧𝐫𝐞𝐜Cong{C = C}{ C'}{c₀}{c₀'}{a}{a'}{c₊}{c₊'}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆) e refl = =Tm→Ty
  (subst (λ D → Γ ⊢
    𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ D ⦂ 1+ l) e
    (𝐧𝐫𝐞𝐜Cong {C = C} {C'} (＝ᵃTy→⊢ q₀ refl refl) (＝ᵃTm→⊢ q₁)
      (＝ᵃTm→⊢ q₂) (＝ᵃTm→⊢ q₃) q₄ q₅ (Tm→Ty (⊢ᵃTm→⊢ q₆))))
＝ᵃTy→⊢{Γ}{l} (𝚷Beta{A = A}{a}{B}{b} q₀ q₁ q₂ q₃ q₄) e refl = {!!}
  -- =Tm→Ty
  -- (subst (λ D → Γ ⊢ (𝛌 b) ∙ a ＝ b ⟨ a ⟩ ∶ D ⦂ 1+ l) e
  -- (𝚷Beta{B = B}{b} (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) q₂
  --   (Tm→Ty (⊢ᵃTm→⊢ q₃)) (Tm→Ty (⊢ᵃTm→⊢ q₄))))
＝ᵃTy→⊢{Γ}{l} (𝐍𝐚𝐭Beta₀{C = C}{c₀}{c₊}
  q₀ q₁ q₂ q₃ q₄) e refl = =Tm→Ty
  (subst (λ D → Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ D ⦂ 1+ l) e
  (𝐍𝐚𝐭Beta₀{C = C}{c₊ = c₊} (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) q₂ q₃
    (Tm→Ty (⊢ᵃTm→⊢ q₄))))
＝ᵃTy→⊢{Γ}{l} (𝐍𝐚𝐭Beta₊{C = C}{c₀}{a}{c₊}
  q₀ q₁ q₂ q₃ q₄ q₅) e refl = =Tm→Ty
  (subst (λ D → Γ ⊢  𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ D ⦂ 1+ l) e
    (𝐍𝐚𝐭Beta₊{C = C}{c₊ = c₊} (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁)
      (⊢ᵃTm→⊢ q₂) q₃ q₄ (Tm→Ty (⊢ᵃTm→⊢ q₅))))

＝ᵃTm→⊢ (𝚷Cong q₀ q₁ q₂ q₃) = =Ty→Tm
  (𝚷Cong (=Tm→Ty (＝ᵃTm→⊢ q₀)) (=Tm→Ty (＝ᵃTm→⊢ q₁)) q₂ (Tm→Ty (⊢ᵃTm→⊢ q₃)))
＝ᵃTm→⊢ (𝐈𝐝Cong q₀ q₁ q₂) = {!!}
  -- =Ty→Tm
  -- (𝐈𝐝Cong (＝ᵃTm→⊢ q₀) (＝ᵃTm→⊢ q₁) (Tm→Ty (⊢ᵃTm→⊢ q₂)))
＝ᵃTm→⊢ (Refl q) = TmRefl (⊢ᵃTm→⊢ q)
＝ᵃTm→⊢ (Symm q) = TmSymm (＝ᵃTm→⊢ q)
＝ᵃTm→⊢ (Trans q₀ q₁) = TmTrans (＝ᵃTm→⊢ q₀) (＝ᵃTm→⊢ q₁)
＝ᵃTm→⊢ (＝conv q₀ q₁) = ＝conv (＝ᵃTm→⊢ q₀) (=Tm→Ty (＝ᵃTm→⊢ q₁))
＝ᵃTm→⊢ (⊢ᵃReflect q₀ q₁ q₂ q₃) =
  ⊢Reflect (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (⊢ᵃTm→⊢ q₂)
    (Tm→Ty (⊢ᵃTm→⊢ q₃))
＝ᵃTm→⊢ (𝛌Cong q₀ q₁ q₂ h₀ h₁) = {!!}
  -- 𝛌Cong (＝ᵃTm→⊢ q₀) q₁ (Tm→Ty (⊢ᵃTm→⊢ q₂)) (Tm→Ty (⊢ᵃTm→⊢ q₃))
＝ᵃTm→⊢ (∙Cong q₀ q₁ q₂ q₃ q₄ h₀ h₁) = {!!}
  -- ∙Cong (＝ᵃTm→⊢ q₀) (＝ᵃTm→⊢ q₁) q₂
  --   (Tm→Ty (⊢ᵃTm→⊢ q₃)) (Tm→Ty (⊢ᵃTm→⊢ q₄))
＝ᵃTm→⊢ (𝐬𝐮𝐜𝐜Cong q) = 𝐬𝐮𝐜𝐜Cong (＝ᵃTm→⊢ q)
＝ᵃTm→⊢ (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆) =
  𝐧𝐫𝐞𝐜Cong (=Tm→Ty (＝ᵃTm→⊢ q₀)) (＝ᵃTm→⊢ q₁) (＝ᵃTm→⊢ q₂)
    (＝ᵃTm→⊢ q₃) q₄ q₅ (Tm→Ty (⊢ᵃTm→⊢ q₆))
＝ᵃTm→⊢ (𝚷Beta{B = B} q₀ q₁ q₂ q₃ q₄) =
  𝚷Beta{B = B} (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) q₂
    (Tm→Ty (⊢ᵃTm→⊢ q₃)) (Tm→Ty (⊢ᵃTm→⊢ q₄))
＝ᵃTm→⊢ (𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ q₄) =
  𝐍𝐚𝐭Beta₀ (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) q₂ q₃ (Tm→Ty (⊢ᵃTm→⊢ q₄))
＝ᵃTm→⊢ (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ q₅) =
  𝐍𝐚𝐭Beta₊ (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁)
    (⊢ᵃTm→⊢ q₂) q₃ q₄ (Tm→Ty (⊢ᵃTm→⊢ q₅))
＝ᵃTm→⊢ (𝚷Eta q₀ q₁ q₂) =
  𝚷Eta (⊢ᵃTm→⊢ q₀) (Tm→Ty (⊢ᵃTm→⊢ q₁)) (Tm→Ty (⊢ᵃTm→⊢ q₂))
＝ᵃTm→⊢ (UIP q₀ q₁ q₂ q₃) =
  UIP (⊢ᵃTm→⊢ q₀) (⊢ᵃTm→⊢ q₁) (⊢ᵃTm→⊢ q₂) (Tm→Ty (⊢ᵃTm→⊢ q₃))

----------------------------------------------------------------------
-- Standard and alternate type systems are propositionally equivalent
----------------------------------------------------------------------
Ok↔Okᵃ : ∀{Γ} → Ok Γ ↔ Okᵃ Γ

_$_ Ok↔Okᵃ = Ok→Okᵃ
_°$_ Ok↔Okᵃ = Okᵃ→Ok

⊢Ty↔⊢ᵃ : ∀{Γ l A} → (Γ ⊢ A ⦂ l) ↔ (Γ ⊢ᵃ A ∶ 𝐔 l ⦂ 1+ l)

_$_ ⊢Ty↔⊢ᵃ = ⊢Ty→⊢ᵃ
⊢Ty↔⊢ᵃ °$ q = ⊢ᵃTy→⊢ q refl refl

⊢Tm↔⊢ᵃ : ∀{Γ l A a} → (Γ ⊢ a ∶ A ⦂ l) ↔ (Γ ⊢ᵃ a ∶ A ⦂ l)

_$_ ⊢Tm↔⊢ᵃ = ⊢Tm→⊢ᵃ
_°$_ ⊢Tm↔⊢ᵃ = ⊢ᵃTm→⊢

＝Ty↔⊢ᵃ : ∀{Γ l A A'} → (Γ ⊢ A ＝ A' ⦂ l) ↔ (Γ ⊢ᵃ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)

_$_ ＝Ty↔⊢ᵃ = ＝Ty→⊢ᵃ
_°$_ ＝Ty↔⊢ᵃ q = ＝ᵃTy→⊢ q refl refl

＝Tm↔⊢ᵃ : ∀{Γ l A a a'} → (Γ ⊢ a ＝ a' ∶ A ⦂ l) ↔ (Γ ⊢ᵃ a ＝ a' ∶ A ⦂ l)

_$_ ＝Tm↔⊢ᵃ = ＝Tm→⊢ᵃ
_°$_ ＝Tm↔⊢ᵃ = ＝ᵃTm→⊢

module ETT.Sized.TypeSystem where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement

{- A version of the type system indexed by a notion of height. -}

----------------------------------------------------------------------
-- Provable judgements in context
----------------------------------------------------------------------
infix 3 Ok _⊢_
data Ok : Cx → Set
data _⊢_ (Γ : Cx) : Jg → Set

data Ok where
  -----------------------------
  -- Well-formed contexts: Ok Γ
  -----------------------------
  ◇ : Ok ◇
  ∷ :
    {l : Lvl}
    {Γ : Cx}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q : Γ ⊢ A ⦂ l)
    → ----------------
    Ok (Γ ⸴ x ∶ A ⦂ l)

data _⊢_  Γ where
  -------------------------------
  -- Well-formed types: Γ ⊢ A ⦂ l
  -------------------------------
  ⊢𝐔 :
    {l : Lvl}
    (q : Ok Γ)
    → ------------
    Γ ⊢ 𝐔 l ⦂ 1+ l

  ⊢𝚷 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # B)
    → -----------------------------------
    Γ ⊢ 𝚷 A B ⦂ max l l'

  ⊢𝐈𝐝 :
    {l : Lvl}
    {A : Ty}
    {a b : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    → ------------------
    Γ ⊢ 𝐈𝐝 a b ⦂ l

  ⊢𝐍𝐚𝐭 :
    (q : Ok Γ)
    → ---------
    Γ ⊢ 𝐍𝐚𝐭 ⦂ 0

  -----------------------------------
  -- Well-formed terms: Γ ⊢ a ∶ A ⦂ l
  -----------------------------------
  ⊢conv :
    {l : Lvl}
    {a : Tm}
    {A A' : Ty}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    → --------------------
    Γ ⊢ a ∶ A' ⦂ l

  ⊢𝐯 :
    {l : Lvl}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Ok Γ)
    (q₁ : (x , A , l) isIn Γ)
    → -----------------------
    Γ ⊢ 𝐯 x ∶ A ⦂ l

  ⊢𝛌 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # (B , b))
    → ---------------------------------------------
    Γ ⊢ 𝛌 b ∶ 𝚷 A B ⦂ max l l'

  ⊢∙ :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    ----
    (p : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    ----
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : x # B)
    → -----------------------------------
    Γ ⊢ b ∙ a ∶ B ⟨ a ⟩ ⦂ l'

  ⊢𝐫𝐞𝐟𝐥 :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ⦂ l)
    → -------------------
    Γ ⊢ 𝐫𝐞𝐟𝐥 ∶ 𝐈𝐝 a a ⦂ l

  ⊢𝐳𝐞𝐫𝐨 :
    (q : Ok Γ)
    → ----------------
    Γ ⊢ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 ⦂ 0

  ⊢𝐬𝐮𝐜𝐜 :
    {a : Tm}
    (q : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    → -------------------
    Γ ⊢ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭 ⦂ 0

  ⊢𝐧𝐫𝐞𝐜 :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    → ------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ⦂ l

  -----------------------------------
  -- Type conversion: Γ ⊢ A ＝ A' ⦂ l
  -----------------------------------
  TyRefl :
    {l : Lvl}
    {A : Ty}
    (q : Γ ⊢ A ⦂ l)
    → -------------
    Γ ⊢ A ＝ A ⦂ l

  TySymm :
    {l : Lvl}
    {A A' : Ty}
    (q : Γ ⊢ A ＝ A' ⦂ l)
    → ------------------
    Γ ⊢ A' ＝ A ⦂ l

  TyTrans :
    {l : Lvl}
    {A A' A'' : Ty}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : Γ ⊢ A' ＝ A'' ⦂ l)
    → ----------------------
    Γ ⊢ A ＝ A'' ⦂ l

  𝚷Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢
      B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ⦂ l')
    (q₂ : x # (B , B'))
    → -----------------------------
    Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ⦂ max l l'

  𝐈𝐝Cong :
    {l : Lvl}
    {A : Ty}
    {a a' b b' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
    → ------------------------
    Γ ⊢ 𝐈𝐝 a b ＝ 𝐈𝐝 a' b' ⦂ l

  --------------------------------------------
  -- Term conversion: Γ ⊢ a ＝ a' ∶ A ⦂ l
  --------------------------------------------
  TmRefl :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ⦂ l)
    → -----------------
    Γ ⊢ a ＝ a ∶ A ⦂ l

  TmSymm :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    → -----------------------
    Γ ⊢ a' ＝ a ∶ A ⦂ l

  TmTrans :
    {l : Lvl}
    {A : Ty}
    {a a' a'' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ a' ＝ a'' ∶ A ⦂ l)
    → --------------------------
    Γ ⊢ a ＝ a'' ∶ A ⦂ l

  ＝conv :
    {l : Lvl}
    {A A' : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    → ------------------------
    Γ ⊢ a ＝ a' ∶ A' ⦂ l

  ⊢Reflect :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    (q₂ : Γ ⊢ e ∶ 𝐈𝐝 a b ⦂ l)
    → -----------------------
    Γ ⊢ a ＝ b ∶ A ⦂ l

  𝛌Cong :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b b' : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢
      b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # (B , b , b'))
    → -----------------------------------
    Γ ⊢ 𝛌 b ＝ 𝛌 b' ∶ 𝚷 A B ⦂ max l l'

  ∙Cong :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a a' b b' : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    ----
    (p : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    ----
    (q₀ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₂ : x # B)
    → -----------------------------------
    Γ ⊢ b ∙ a ＝ b' ∙ a' ∶ B ⟨ a ⟩ ⦂ l'

  𝐬𝐮𝐜𝐜Cong :
    {a a' : Tm}
    (q : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    → -----------------------------
    Γ ⊢ 𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭 ⦂ 0

  𝐧𝐫𝐞𝐜Cong :
    {l : Lvl}
    {C C' : Ty[ 1 ]}
    {c₀ c₀' a a'  : Tm}
    {c₊ c₊' : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ⦂ l)
    (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₂ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₄ : x # (C , C' , c₊ , c₊'))
    (q₅ : y # (c₊ , c₊'))
    → -----------------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩ ⦂ l

  𝚷Beta :
    {l l' : Lvl}
    {A : Ty}
    {a : Tm}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : x # (B , b))
    → ---------------------------------------------
    Γ ⊢ (𝛌 b) ∙ a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ⦂ l'

  𝐍𝐚𝐭Beta₀ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : x # (C , c₊))
    (q₃ : y # c₊)
    → ------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l

  𝐍𝐚𝐭Beta₊ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    → -------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ⦂ l

  𝚷Eta :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    (q₁ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    → -------------------------------------------
    Γ ⊢ b ＝ 𝛌 (x ．(b ∙ 𝐯 x)) ∶ 𝚷 A B ⦂ max l l'

  UIP :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ e ∶ 𝐈𝐝 a b ⦂ l)
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : Γ ⊢ b ∶ A ⦂ l)
    → -------------------------
    Γ ⊢ e ＝ 𝐫𝐞𝐟𝐥 ∶ 𝐈𝐝 a b ⦂ l

  --------------------------------------------------
  -- The judgements Γ ⊢ A ⦂ l and Γ ⊢ A ∶ 𝐔 l ⦂ 1+ l
  -- are propositionally equivalent
  --------------------------------------------------
  Tm→Ty :
    {l : Lvl}
    {A : Tm}
    (q : Γ ⊢ A ∶ 𝐔 l ⦂ 1+ l)
    → ----------------------
    Γ ⊢ A ⦂ l

  Ty→Tm :
    {l : Lvl}
    {A : Ty}
    (q : Γ ⊢ A ⦂ l)
    → ----------------
    Γ ⊢ A ∶ 𝐔 l ⦂ 1+ l

  --------------------------------------------------------------
  -- The judgements Γ ⊢ A ＝ A' ⦂ l and Γ ⊢ A ＝ A' ∶ 𝐔 l ⦂ 1+ l
  -- are propositionally equivalent
  --------------------------------------------------------------
  =Ty→Tm :
    {l : Lvl}
    {A A' : Ty}
    (q : Γ ⊢ A ＝ A' ⦂ l)
    → ----------------------
    Γ ⊢ A ＝ A' ∶ 𝐔 l ⦂ 1+ l

  =Tm→Ty :
    {l : Lvl}
    {A A' : Tm}
    (q : Γ ⊢ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
    → ----------------------------
    Γ ⊢ A ＝ A' ⦂ l

----------------------------------------------------------------------
-- Size of provable judgements
----------------------------------------------------------------------
sizeOk : ∀{Γ} → Ok Γ → ℕ
sizeJg : ∀{Γ J} → Γ ⊢ J → ℕ

sizeOk ◇     = 0
sizeOk (∷ q) = 1+ (sizeJg q)

sizeJg (⊢𝐔 q) = 1+ (sizeOk q)
sizeJg (⊢𝚷 q _) = 1+ (sizeJg q)
sizeJg (⊢𝐈𝐝 q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (⊢𝐍𝐚𝐭 q) = 1+ (sizeOk q)
sizeJg (⊢conv q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (⊢𝐯 q _) = 1+ (sizeOk q)
sizeJg (⊢𝛌 q _) = 1+ (sizeJg q)
sizeJg (⊢∙ q₀ q₁ q₂ _) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
sizeJg (⊢𝐫𝐞𝐟𝐥 q) = 1+ (sizeJg q)
sizeJg (⊢𝐳𝐞𝐫𝐨 q) = 1+ (sizeOk q)
sizeJg (⊢𝐬𝐮𝐜𝐜 q) = 1+ (sizeJg q)
sizeJg (⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ _ _) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
sizeJg (TyRefl q) = 1+ (sizeJg q)
sizeJg (TySymm q) = 1+ (sizeJg q)
sizeJg (TyTrans q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (𝚷Cong q₀ q₁ _) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (𝐈𝐝Cong q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (TmRefl q) = 1+ (sizeJg q)
sizeJg (TmSymm q) = 1+ (sizeJg q)
sizeJg (TmTrans q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (＝conv q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (⊢Reflect q₀ q₁ q₂) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
sizeJg (𝛌Cong q _) = 1+ (sizeJg q)
sizeJg (∙Cong q₀ q₁ q₂ _) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
sizeJg (𝐬𝐮𝐜𝐜Cong q) = 1+ (sizeJg q)
sizeJg (𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ _ _) =
  1+ (max⁴ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂) (sizeJg q₃))
sizeJg (𝚷Beta q₀ q₁ _) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (𝐍𝐚𝐭Beta₀ q₀ q₁ _ _) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ _ _) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
sizeJg (𝚷Eta q₀ q₁) = 1+ (max (sizeJg q₀) (sizeJg q₁))
sizeJg (UIP q₀ q₁ q₂) =
  1+ (max³ (sizeJg q₀) (sizeJg q₁) (sizeJg q₂))
-- We make the constructors Ty→Tm, Tm→Ty, =Tm→Ty, =Ty→Tm
-- non-size-changing for semantic reasons
sizeJg (Ty→Tm q) = sizeJg q
sizeJg (Tm→Ty q) = sizeJg q
sizeJg (=Ty→Tm q) = sizeJg q
sizeJg (=Tm→Ty q) = sizeJg q

instance
  hasSizeOk : ∀{Γ} → hasSize (Ok Γ)
  size ⦃ hasSizeOk ⦄ = sizeOk
  hasSizeJg : ∀{Γ J} → hasSize (Γ ⊢ J)
  size ⦃ hasSizeJg ⦄ = sizeJg

{-# DISPLAY sizeOk = size #-}
{-# DISPLAY sizeJg = size #-}

Ok+ :
  {Γ : Cx}
  {l : Lvl}
  {A : Ty}
  {x : 𝔸}
  (q : Ok Γ)
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  ∃[ s ] (size q ≡ 1+ s)

Ok+ (∷ q) p = (_ , refl)

Jg+ :
  {Γ : Cx}
  {J : Jg}
  (q : Γ ⊢ J)
  → --------------------
  ∃[ s ] (size q ≡ 1+ s)

Jg+ (⊢𝐔 _) = (_ , refl)
Jg+ (⊢𝚷 _ _) = (_ , refl)
Jg+ (⊢𝐈𝐝 _ _) = (_ , refl)
Jg+ (⊢𝐍𝐚𝐭 _) = (_ , refl)
Jg+ (⊢conv _ _) = (_ , refl)
Jg+ (⊢𝐯 _ _) = (_ , refl)

Jg+ (⊢𝛌 _ _) = (_ , refl)
Jg+ (⊢∙ _ _ _ _) = (_ , refl)
Jg+ (⊢𝐫𝐞𝐟𝐥 _) = (_ , refl)
Jg+ (⊢𝐳𝐞𝐫𝐨 _) = (_ , refl)
Jg+ (⊢𝐬𝐮𝐜𝐜 _) = (_ , refl)
Jg+ (⊢𝐧𝐫𝐞𝐜 _ _ _ _ _) = (_ , refl)
Jg+ (TyRefl _) = (_ , refl)
Jg+ (TySymm _) = (_ , refl)
Jg+ (TyTrans _ _) = (_ , refl)
Jg+ (𝚷Cong _ _ _) = (_ , refl)
Jg+ (𝐈𝐝Cong _ _) = (_ , refl)
Jg+ (TmRefl _) = (_ , refl)
Jg+ (TmSymm _) = (_ , refl)
Jg+ (TmTrans _ _) = (_ , refl)
Jg+ (＝conv _ _) = (_ , refl)
Jg+ (⊢Reflect _ _ _) = (_ , refl)
Jg+ (𝛌Cong _ _) = (_ , refl)
Jg+ (∙Cong _ _ _ _) = (_ , refl)
Jg+ (𝐬𝐮𝐜𝐜Cong _) = (_ , refl)
Jg+ (𝐧𝐫𝐞𝐜Cong _ _ _ _ _ _) = (_ , refl)
Jg+ (𝚷Beta _ _ _) = (_ , refl)
Jg+ (𝐍𝐚𝐭Beta₀ _ _ _ _) = (_ , refl)
Jg+ (𝐍𝐚𝐭Beta₊ _ _ _ _ _) = (_ , refl)
Jg+ (𝚷Eta _ _) = (_ , refl)
Jg+ (UIP _ _ _) = (_ , refl)
Jg+ (Tm→Ty q) = Jg+ q
Jg+ (Ty→Tm q) = Jg+ q
Jg+ (=Ty→Tm q) = Jg+ q
Jg+ (=Tm→Ty q) = Jg+ q

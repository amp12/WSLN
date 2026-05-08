module MLTTcuml.TypeSystem where

open import Notation
open import Product

open import WSLN

open import MLTTcuml.Syntax
open import MLTTcuml.Judgement

----------------------------------------------------------------------
-- Provable judgements in context
----------------------------------------------------------------------
module MLTT where
  infix 3 _⊢_
  data Ok : Cx → Set
  data _⊢_ (Γ : Cx) : Jg → Set

  data Ok where
    -----------------------------
    -- Well-formed contexts: Ok Γ
    -----------------------------
    ◇ : Ok ◇
    ∷ :
      {Γ : Cx}
      {A : Ty}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q : Γ ⊢ A ty)
      → -------------
      Ok (Γ ⸴ x ∶ A)

  data _⊢_  Γ where
    ------------------------------
    -- Well-formed types: Γ ⊢ A ty
    -------------------------------
    ⊢𝚷ty :
      {A : Ty}
      {B : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      (q₁ : x # B)
      → ---------------------------
      Γ ⊢ 𝚷 A B ty

    ⊢𝐈𝐝ty :
      {A : Ty}
      {a a' : Tm}
      (q₀ : Γ ⊢ a ∶ A)
      (q₁ : Γ ⊢ a' ∶ A)
      → ---------------
      Γ ⊢ 𝐈𝐝 A a a' ty

    ⊢𝐔 :
      (q : Ok Γ)
      → --------
      Γ ⊢ 𝐔 ty

    ⊢𝐄𝐥 :
      -- Russell style universe:
      -- no syntactic distinction between
      -- an expression of type 𝐔 and a type
      {A : Tm}
      (q : Γ ⊢ A ∶ 𝐔)
      → -------------
      Γ ⊢ A ty

    ----------------------------------
    -- Type conversion: Γ ⊢ A ＝ A' ty
    ----------------------------------
    TyRefl :
      {A : Ty}
      (q : Γ ⊢ A ty)
      → -------------
      Γ ⊢ A ＝ A ty

    TySymm :
      {A A' : Ty}
      (q : Γ ⊢ A ＝ A' ty)
      → -------------------
      Γ ⊢ A' ＝ A ty

    TyTrans :
      {A A' A'' : Ty}
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⊢ A' ＝ A'' ty)
      → ---------------------
      Γ ⊢ A ＝ A'' ty

    𝚷TyCong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢
        B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ty)
      (q₂ : x # (B , B'))
      → -----------------------
      Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ty

    𝐈𝐝TyCong :
      {A A' : Ty}
      {a a' b b' : Tm}
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⊢ a ＝ a' ∶ A)
      (q₂ : Γ ⊢ b ＝ b' ∶ A)
      → ----------------------------
      Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ty

    ＝𝐄𝐥 :
      {A A' : Tm}
      (q : Γ ⊢ A ＝ A' ∶ 𝐔)
      → -------------------
      Γ ⊢ A ＝ A' ty

    -------------------------------
    -- Well-formed terms: Γ ⊢ a ∶ A
    -------------------------------
    ⊢𝐯 :
      {A : Ty}
      {x : 𝔸}
      (q₀ : Ok Γ)
      (q₁ : (x , A) isIn Γ)
      → -------------------
      Γ ⊢ 𝐯 x ∶ A

    ⊢conv :
      {a : Tm}
      {A A' : Ty}
      (q₀ : Γ ⊢ a ∶ A)
      (q₁ : Γ ⊢ A ＝ A' ty)
      → -------------------
      Γ ⊢ a ∶ A'

    ⊢𝚷 :
      {A : Tm}
      {B : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ∶ 𝐔)
      (q₁ : (Γ ⸴ x ∶ A) ⊢ B ⟨ x ⟩ ∶ 𝐔)
      (q₂ : x # B)
      → ------------------------------
      Γ ⊢ 𝚷 A B ∶ 𝐔

    ⊢𝛌 :
      {A : Ty}
      {B : Ty[ 1 ]}
      {b : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₁ : x # (B , b))
      → -----------------------------------
      Γ ⊢ 𝛌 A b ∶ 𝚷 A B

    ⊢∙ :
      {A : Ty}
      {B : Ty[ 1 ]}
      {a b : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ b ∶ 𝚷 A B)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      (q₃ : x # B)
      → ---------------------------
      Γ ⊢ b ∙[ A , B ] a ∶ B ⟨ a ⟩

    ⊢𝐈𝐝 :
      {A a a' : Tm}
      (q₀ : Γ ⊢ A ∶ 𝐔)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ a' ∶ A)
      → ---------------
      Γ ⊢ 𝐈𝐝 A a a' ∶ 𝐔

    ⊢𝐫𝐞𝐟𝐥 :
      {A : Ty}
      {a : Tm}
      (q : Γ ⊢ a ∶ A)
      → -------------------
      Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a

    ⊢𝐉 :
      {A : Ty}
      {C : Ty[ 2 ]}
      {a b c e : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢ C ⟨ x ⸴ y ⟩ ty)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ b ∶ A)
      (q₃ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b)
      (q₅ : x # C)
      (q₆ : y # C)
      → --------------------------------------------------
      Γ ⊢ 𝐉 C a b c e ∶ C ⟨ b ⸴ e ⟩

    ⊢𝐍𝐚𝐭 :
      (q : Ok Γ)
      → ---------
      Γ ⊢ 𝐍𝐚𝐭 ∶ 𝐔

    ⊢𝐳𝐞𝐫𝐨 :
      (q : Ok Γ)
      → ------------
      Γ ⊢ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭

    ⊢𝐬𝐮𝐜𝐜 :
      {a : Tm}
      (q : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      → ---------------
      Γ ⊢ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭

    ⊢𝐧𝐫𝐞𝐜 :
      {C : Ty[ 1 ]}
      {c₀ a : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      (q₃ : x # (C , c₊))
      (q₄ : y # c₊)
      → --------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩

    -----------------------------------
    -- Term conversion: Γ ⊢ a ＝ a' ∶ A
    -----------------------------------
    TmRefl :
      {A : Ty}
      {a : Tm}
      (q : Γ ⊢ a ∶ A)
      → -------------
      Γ ⊢ a ＝ a ∶ A

    TmSymm :
      {A : Ty}
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ A)
      → ------------------
      Γ ⊢ a' ＝ a ∶ A

    TmTrans :
      {A : Ty}
      {a a' a'' : Tm}
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ a' ＝ a'' ∶ A)
      → ---------------------
      Γ ⊢ a ＝ a'' ∶ A

    ＝conv :
      {A A' : Ty}
      {a a' : Tm}
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ A ＝ A' ty)
      → --------------------
      Γ ⊢ a ＝ a' ∶ A'

    𝚷TmCong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ∶ 𝐔)
      (q₁ : Γ ⸴ x ∶ A ⊢
        B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶ 𝐔)
      (q₂ : x # (B , B'))
      → ------------------------
      Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ∶ 𝐔

    𝛌Cong :
      {A A' : Ty}
      {B : Ty[ 1 ]}
      {b b' : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢
        b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₂ : x # (B , b , b'))
      → ------------------------------
      Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B

    ∙Cong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {a a' b b' : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ty)
      (q₂ : Γ ⊢ b ＝ b' ∶ 𝚷 A B)
      (q₃ : Γ ⊢ a ＝ a' ∶ A)
      (q₄ : x # (B , B'))
      → ------------------------------------------------
      Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B ⟨ a ⟩

    𝐈𝐝TmCong :
      {A A' : Ty}
      {a a' b b' : Tm}
      (q₀ : Γ ⊢ A ＝ A' ∶ 𝐔)
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ b ＝ b' ∶ A)
      → -----------------------------
      Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ∶ 𝐔

    𝐫𝐞𝐟𝐥Cong :
      {A : Ty}
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ A)
      → ------------------------------
      Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a

    𝐉Cong  :
      {A : Ty}
      {C C' : Ty[ 2 ]}
      {a a' b b' c c' e e' : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢
        C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ty)
      (q₁ : Γ ⊢ a ＝ a' ∶ A)
      (q₂ : Γ ⊢ b ＝ b' ∶ A)
      (q₃ : Γ ⊢ c ＝ c' ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₄ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b)
      (q₅ : x # (C , C'))
      (q₆ : y # (C , C'))
      → -----------------------------------------------
      Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C ⟨ b ⸴ e ⟩

    𝐬𝐮𝐜𝐜Cong :
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭)
      → -------------------------
      Γ ⊢ 𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭

    𝐧𝐫𝐞𝐜Cong :
      {C C' : Ty[ 1 ]}
      {c₀ c₀' a a'  : Tm}
      {c₊ c₊' : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ty)
      (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₂ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩ ⊢
        c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭)
      (q₄ : x # (C , C' , c₊ , c₊'))
      (q₅ : y # (c₊ , c₊'))
      → ------------------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩

    𝚷Beta :
      {A : Ty}
      {a : Tm}
      {B : Ty[ 1 ]}
      {b : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : x # (B , b))
      → -----------------------------------------
      Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩

    𝐈𝐝Beta :
      {A : Ty}
      {C : Ty[ 2 ]}
      {a c : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₁ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢
        C ⟨ x ⸴ y ⟩ ty)
      (q₀ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₃ : x # C)
      (q₄ : y # C)
      → --------------------------------------------
      Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩

    𝐍𝐚𝐭Beta₀ :
      {C : Ty[ 1 ]}
      {c₀ : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : x # (C , c₊))
      (q₃ : y # c₊)
      → --------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩

    𝐍𝐚𝐭Beta₊ :
      {C : Ty[ 1 ]}
      {c₀ a : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      (q₃ : x # (C , c₊))
      (q₄ : y # c₊)
      → --------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
      c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩

    𝚷Eta :
      {A : Ty}
      {B : Ty[ 1 ]}
      {b : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ b ∶ 𝚷 A B)
      (q₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      → --------------------------------------------
      Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B
-- end module MLTT

----------------------------------------------------------------------
-- An equivalent type system augmented with helper hypotheses
-- that aid proofs by structural induction
----------------------------------------------------------------------
module MLTT⁺ where
  infix 3 _⊢_
  data Ok : Cx → Set
  data _⊢_ (Γ : Cx) : Jg → Set

  data Ok where
    ◇ : Ok ◇
    ∷ :
      {Γ : Cx}
      {A : Ty}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q : Γ ⊢ A ty)
      -- helper hypothesis
      (h : Ok Γ)
      → -------------
      Ok (Γ ⸴ x ∶ A)

  data _⊢_  Γ where
    ⊢𝚷ty :
      {A : Ty}
      {B : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      (q₁ : x # B)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → ---------------------------
      Γ ⊢ 𝚷 A B ty

    ⊢𝐈𝐝ty :
      {A : Ty}
      {a b : Tm}
      (q₀ : Γ ⊢ a ∶ A)
      (q₁ : Γ ⊢ b ∶ A)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → ------------------
      Γ ⊢ 𝐈𝐝 A a b ty

    ⊢𝐔 :
      (q : Ok Γ)
      → --------
      Γ ⊢ 𝐔 ty

    ⊢𝐄𝐥 :
      {A : Tm}
      (q : Γ ⊢ A ∶ 𝐔)
      → -------------
      Γ ⊢ A ty

    TyRefl :
      {A : Ty}
      (q : Γ ⊢ A ty)
      → -------------
      Γ ⊢ A ＝ A ty

    TySymm :
      {A A' : Ty}
      (q : Γ ⊢ A ＝ A' ty)
      → -------------------
      Γ ⊢ A' ＝ A ty

    TyTrans :
      {A A' A'' : Ty}
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⊢ A' ＝ A'' ty)
      → ---------------------
      Γ ⊢ A ＝ A'' ty

    𝚷TyCong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢
      B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ty)
      (q₂ : x # (B , B'))
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → -----------------------
      Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ty

    𝐈𝐝TyCong :
      {A A' : Ty}
      {a a' b b' : Tm}
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⊢ a ＝ a' ∶ A)
      (q₂ : Γ ⊢ b ＝ b' ∶ A)
      → ----------------------------
      Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ty

    ＝𝐄𝐥 :
      {A A' : Tm}
      (q : Γ ⊢ A ＝ A' ∶ 𝐔)
      → -------------------
      Γ ⊢ A ＝ A' ty

    ⊢𝐯 :
      {A : Ty}
      {x : 𝔸}
      (q₀ : Ok Γ)
      (q₁ : (x , A) isIn Γ)
      → -------------------
      Γ ⊢ 𝐯 x ∶ A

    ⊢conv :
      {a : Tm}
      {A A' : Ty}
      (q₀ : Γ ⊢ a ∶ A)
      (q₁ : Γ ⊢ A ＝ A' ty)
      → -------------------
      Γ ⊢ a ∶ A'

    ⊢𝚷 :
      {A : Tm}
      {B : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ∶ 𝐔)
      (q₁ : (Γ ⸴ x ∶ A) ⊢ B ⟨ x ⟩ ∶ 𝐔)
      (q₂ : x # B)
      → ------------------------------
      Γ ⊢ 𝚷 A B ∶ 𝐔

    ⊢𝛌 :
      {A : Ty}
      {B : Ty[ 1 ]}
      {b : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₁ : x # (B , b))
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      → -----------------------------------
      Γ ⊢ 𝛌 A b ∶ 𝚷 A B

    ⊢∙ :
      {A : Ty}
      {B : Ty[ 1 ]}
      {a b : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ b ∶ 𝚷 A B)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      (q₃ : x # B)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → ---------------------------
      Γ ⊢ b ∙[ A , B ] a ∶ B ⟨ a ⟩

    ⊢𝐈𝐝 :
      {A a b : Tm}
      (q₀ : Γ ⊢ A ∶ 𝐔)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ b ∶ A)
      → --------------
      Γ ⊢ 𝐈𝐝 A a b ∶ 𝐔

    ⊢𝐫𝐞𝐟𝐥 :
      {A : Ty}
      {a : Tm}
      (q : Γ ⊢ a ∶ A)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → -------------------
      Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a

    ⊢𝐉 :
      {A : Ty}
      {C : Ty[ 2 ]}
      {a b c e : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢ C ⟨ x ⸴ y ⟩ ty)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ b ∶ A)
      (q₃ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b)
      (q₅ : x # C)
      (q₆ : y # C)
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ 𝐈𝐝 A a (𝐯 x) ty)
      → --------------------------------------------------
      Γ ⊢ 𝐉 C a b c e ∶ C ⟨ b ⸴ e ⟩

    ⊢𝐍𝐚𝐭 :
      (q : Ok Γ)
      → ---------
      Γ ⊢ 𝐍𝐚𝐭 ∶ 𝐔

    ⊢𝐳𝐞𝐫𝐨 :
      (q : Ok Γ)
      → ------------
      Γ ⊢ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭

    ⊢𝐬𝐮𝐜𝐜 :
      {a : Tm}
      (q : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      → ---------------
      Γ ⊢ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭

    ⊢𝐧𝐫𝐞𝐜 :
      {C : Ty[ 1 ]}
      {c₀ a : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      (q₃ : x # (C , c₊))
      (q₄ : y # c₊)
      -- helper hypotheses
      (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ty)
      → --------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩

    TmRefl :
      {A : Ty}
      {a : Tm}
      (q : Γ ⊢ a ∶ A)
      → -------------
      Γ ⊢ a ＝ a ∶ A

    TmSymm :
      {A : Ty}
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ A)
      → ------------------
      Γ ⊢ a' ＝ a ∶ A

    TmTrans :
      {A : Ty}
      {a a' a'' : Tm}
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ a' ＝ a'' ∶ A)
      → ---------------------
      Γ ⊢ a ＝ a'' ∶ A

    ＝conv :
      {A A' : Ty}
      {a a' : Tm}
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ A ＝ A' ty)
      → --------------------
      Γ ⊢ a ＝ a' ∶ A'

    𝚷TmCong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ∶ 𝐔)
      (q₁ : Γ ⸴ x ∶ A ⊢
        B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶ 𝐔)
      (q₂ : x # (B , B'))
      -- helper hypothesis
      (h : Γ ⊢ A ∶ 𝐔)
      → ------------------------
      Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ∶ 𝐔

    𝛌Cong :
      {A A' : Ty}
      {B : Ty[ 1 ]}
      {b b' : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢
        b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₂ : x # (B , b , b'))
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      → ------------------------------
      Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B

    ∙Cong :
      {A A' : Ty}
      {B B' : Ty[ 1 ]}
      {a a' b b' : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ A ＝ A' ty)
      (q₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ty)
      (q₂ : Γ ⊢ b ＝ b' ∶ 𝚷 A B)
      (q₃ : Γ ⊢ a ＝ a' ∶ A)
      (q₄ : x # (B , B'))
      -- helper hypotheses
      (h₀ : Γ ⊢ A  ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      → ------------------------------------------------
      Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B ⟨ a ⟩

    𝐈𝐝TmCong :
      {A A' : Ty}
      {a a' b b' : Tm}
      (q₀ : Γ ⊢ A ＝ A' ∶ 𝐔)
      (q₀ : Γ ⊢ a ＝ a' ∶ A)
      (q₁ : Γ ⊢ b ＝ b' ∶ A)
      → -----------------------------
      Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ∶ 𝐔

    𝐫𝐞𝐟𝐥Cong :
      {A : Ty}
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ A)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → ------------------------------
      Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a

    𝐉Cong  :
      {A : Ty}
      {C C' : Ty[ 2 ]}
      {a a' b b' c c' e e' : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢
        C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ty)
      (q₁ : Γ ⊢ a ＝ a' ∶ A)
      (q₂ : Γ ⊢ b ＝ b' ∶ A)
      (q₃ : Γ ⊢ c ＝ c' ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₄ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b)
      (q₅ : x # (C , C'))
      (q₆ : y # (C , C'))
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ 𝐈𝐝 A a (𝐯 x) ty)
      → -----------------------------------------------
      Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C ⟨ b ⸴ e ⟩

    𝐬𝐮𝐜𝐜Cong :
      {a a' : Tm}
      (q : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭)
      → -------------------------
      Γ ⊢ 𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭

    𝐧𝐫𝐞𝐜Cong :
      {C C' : Ty[ 1 ]}
      {c₀ c₀' a a'  : Tm}
      {c₊ c₊' : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ty)
      (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₂ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩ ⊢
        c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭)
      (q₄ : x # (C , C' , c₊ , c₊'))
      (q₅ : y # (c₊ , c₊'))
      -- helper hypotheses
      (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ty)
      → ------------------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩

    𝚷Beta :
      {A : Ty}
      {a : Tm}
      {B : Ty[ 1 ]}
      {b : Tm[ 1 ]}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : (Γ ⸴ x ∶ A) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : x # (B , b))
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      → -----------------------------------------
      Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩

    𝐈𝐝Beta :
      {A : Ty}
      {C : Ty[ 2 ]}
      {a c : Tm}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢
        C ⟨ x ⸴ y ⟩ ty)
      (q₁ : Γ ⊢ a ∶ A)
      (q₂ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩)
      (q₃ : x # C)
      (q₄ : y # C)
      -- helper hypotheses
      (h₀ : Γ ⊢ A ty)
      (h₁ : Γ ⸴ x ∶ A ⊢ 𝐈𝐝 A a (𝐯 x) ty)
      → -------------------------------------------
      Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩

    𝐍𝐚𝐭Beta₀ :
      {C : Ty[ 1 ]}
      {c₀ : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : x # (C , c₊))
      (q₃ : y # c₊)
      -- helper hypotheses
      (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ty)
      → --------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩

    𝐍𝐚𝐭Beta₊ :
      {C : Ty[ 1 ]}
      {c₀ a : Tm}
      {c₊ : Tm[ 2 ]}
      {x y : 𝔸}
      ⦃ _ : x # Γ ⦄
      ⦃ _ : y # (Γ , x) ⦄
      (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩)
      (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ C ⟨ x ⟩) ⊢
        c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩)
      (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭)
      (q₃ : x # (C , c₊))
      (q₄ : y # c₊)
      -- helper hypothesis
      (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ C ⟨ x ⟩ ty)
      → --------------------------------------
      Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
      c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩

    𝚷Eta :
      {A : Ty}
      {B : Ty[ 1 ]}
      {b : Tm}
      {x : 𝔸}
      ⦃ _ : x # Γ ⦄
      (q₀ : Γ ⊢ b ∶ 𝚷 A B)
      (q₁ : Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty)
      -- helper hypothesis
      (h : Γ ⊢ A ty)
      → --------------------------------------------
      Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B
-- end module MLTT+

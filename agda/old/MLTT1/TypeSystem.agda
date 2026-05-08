module MLTT1.TypeSystem where

open import Identity
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTT1.Syntax
open import MLTT1.Judgement

----------------------------------------------------------------------
-- Provable judgements in context
----------------------------------------------------------------------
infix 3 _⊢_
data Ok : Cx → Set
data _⊢_ (Γ : Cx) : Jg → Set

{- Some rules include helper hypotheses that aid proofs by structural
induction; versions of those rules without these hypotheses are
admissible; see MLTT1.AdmissibleRules. -}

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
    (q : Γ ⊢ A ∶𝐔 l)
    -- helper hypothesis
    (h : Ok Γ)
    → ----------------
    Ok (Γ ⸴ x ∶ A ∶ l)

data _⊢_  Γ where
  -------------------------------
  -- Well-formed terms: Γ ⊢ a ∶ A
  -------------------------------
  ⊢conv :
    {l : Lvl}
    {a : Tm}
    {A A' : Ty}
    (q₀ : Γ ⊢ a ∶ A ∶ l)
    (q₁ : Γ ⊢ A ＝ A' ∶𝐔 l)
    → ---------------------
    Γ ⊢ a ∶ A' ∶ l

  ⊢𝐯 :
    {l : Lvl}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Ok Γ)
    (q₁ : (x , A , l) isIn Γ)
    → -----------------------
    Γ ⊢ 𝐯 x ∶ A ∶ l

  ⊢𝐔 :
    {l : Lvl}
    (q : Ok Γ)
    → ---------------
    Γ ⊢ 𝐔 l ∶𝐔 (1+ l)

  ⊢𝚷 :
    {l l' : Lvl}
    {A : Tm}
    {B : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ∶𝐔 l)
    -- Note the use of concretion:
    -- since B is a unary abstraction
    -- B ⟨ x ⟩ is an expression
    (q₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    -- We need that x is fresh for B
    -- in order to be able to deduce that
    -- the support of B is contained in
    -- the domain of Γ (see MLTT1.WellScoped)
    (q₂ : x # B)
    → ---------------------------------
    Γ ⊢ 𝚷 A B ∶𝐔 (max l l')

  ⊢𝛌 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ∶ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
    (q₁ : x # (B , b))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    → ---------------------------------------------
    Γ ⊢ 𝛌 A b ∶ 𝚷 A B ∶ max l l'

  ⊢∙ :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ∶ max l l')
    (q₁ : Γ ⊢ a ∶ A ∶ l)
    (q₂ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    (q₃ : x # B)
    -- helper hypothesis
    (h : Γ ⊢ A ∶𝐔 l)
    → -------------------------------------
    Γ ⊢ b ∙[ A , B ] a ∶ B ⟨ a ⟩ ∶ l'

  ⊢𝐈𝐝 :
    {l : Lvl}
    {A a b : Tm}
    (q₀ : Γ ⊢ a ∶ A ∶ l)
    (q₁ : Γ ⊢ b ∶ A ∶ l)
    -- helper hypothesis
    (h : Γ ⊢ A ∶𝐔 l)
    → -------------------
    Γ ⊢ 𝐈𝐝 A a b ∶𝐔 l

  ⊢𝐫𝐞𝐟𝐥 :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ∶ l)
    -- helper hypothesis
    (h : Γ ⊢ A ∶𝐔 l)
    → -----------------------
    Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ∶ l

  ⊢𝐉 :
    {l l' : Lvl}
    {A : Ty}
    {C : Ty[ 2 ]}
    {a b c e : Tm}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l ⊢
      C ⟨ x ⸴ y ⟩ ∶𝐔 l')
    (q₁ : Γ ⊢ a ∶ A ∶ l)
    (q₂ : Γ ⊢ b ∶ A ∶ l)
    (q₃ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
    (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b ∶ l)
    (q₅ : x # C)
    (q₆ : y # C)
    --  helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ 𝐈𝐝 A a (𝐯 x) ∶𝐔 l)
    → -------------------------------------------
    Γ ⊢ 𝐉 C a b c e ∶ C ⟨ b ⸴ e ⟩ ∶ l'

  ⊢𝐍𝐚𝐭 :
    (q : Ok Γ)
    → -----------
    Γ ⊢ 𝐍𝐚𝐭 ∶𝐔 0

  ⊢𝐳𝐞𝐫𝐨 :
    (q : Ok Γ)
    → ----------------
    Γ ⊢ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 ∶ 0

  ⊢𝐬𝐮𝐜𝐜 :
    {a : Tm}
    (q : Γ ⊢ a ∶ 𝐍𝐚𝐭 ∶ 0)
    → -------------------
    Γ ⊢ 𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭 ∶ 0

  ⊢𝐧𝐫𝐞𝐜 :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ∶ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    --  helper hypothesis
    (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ∶𝐔 l)
    → -----------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ∶ l

  -----------------------------------
  -- Term conversion: Γ ⊢ a ＝ a' ∶ A
  -----------------------------------
  Refl :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ∶ l)
    → -----------------
    Γ ⊢ a ＝ a ∶ A ∶ l

  Symm :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q : Γ ⊢ a ＝ a' ∶ A ∶ l)
    → -----------------------
    Γ ⊢ a' ＝ a ∶ A ∶ l

  Trans :
    {l : Lvl}
    {A : Ty}
    {a a' a'' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    (q₁ : Γ ⊢ a' ＝ a'' ∶ A ∶ l)
    → -------------------------
    Γ ⊢ a ＝ a'' ∶ A ∶ l

  ＝conv :
    {l : Lvl}
    {A A' : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    (q₁ : Γ ⊢ A ＝ A' ∶𝐔 l)
    → ------------------------
    Γ ⊢ a ＝ a' ∶ A' ∶ l

  𝚷Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ＝ A' ∶𝐔 l)
    (q₁ : Γ ⸴ x ∶ A ∶ l ⊢
      B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶𝐔 l')
    (q₂ : x # (B , B'))
    -- helper hypothesis
    (h : Γ ⊢ A ∶𝐔 l)
    → --------------------------------
    Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ∶𝐔 (max l l')

  𝛌Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B : Ty[ 1 ]}
    {b b' : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ＝ A' ∶𝐔 l)
    (q₁ : Γ ⸴ x ∶ A ∶ l ⊢
      b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
    (q₂ : x # (B , b , b'))
    -- helper hypothesis
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    → -------------------------------------
    Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B ∶ max l l'

  ∙Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {a a' b b' : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ＝ A' ∶𝐔 l)
    (q₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶𝐔 l')
    (q₂ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ∶ max l l')
    (q₃ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    (q₄ : x # (B , B'))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    → -----------------------------------------------------
    Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B ⟨ a ⟩ ∶ l'

  𝐈𝐝Cong :
    {l : Lvl}
    {A A' : Ty}
    {a a' b b' : Tm}
    (q₀ : Γ ⊢ A ＝ A' ∶𝐔 l)
    (q₀ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    (q₁ : Γ ⊢ b ＝ b' ∶ A ∶ l)
    → ------------------------------
    Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ∶𝐔 l

  𝐫𝐞𝐟𝐥Cong :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    -- helper hypthesis
    (q₁ : Γ ⊢ A ∶𝐔 l)
    → ----------------------------------
    Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ∶ l

  𝐉Cong  :
    {l l' : Lvl}
    {A : Ty}
    {C C' : Ty[ 2 ]}
    {a a' b b' c c' e e' : Tm}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l  ⊢
      C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ∶𝐔 l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ∶ l)
    (q₂ : Γ ⊢ b ＝ b' ∶ A ∶ l)
    (q₃ : Γ ⊢ c ＝ c' ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
    (q₄ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b ∶ l)
    (q₅ : x # (C , C'))
    (q₆ : y # (C , C'))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ 𝐈𝐝 A a (𝐯 x) ∶𝐔 l)
    → ----------------------------------------------------
    Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C ⟨ b ⸴ e ⟩ ∶ l'

  𝐬𝐮𝐜𝐜Cong :
    {a a' : Tm}
    (q : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ∶ 0)
    → -----------------------------
    Γ ⊢ 𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭 ∶ 0

  𝐧𝐫𝐞𝐜Cong :
    {l : Lvl}
    {C C' : Ty[ 1 ]}
    {c₀ c₀' a a'  : Tm}
    {c₊ c₊' : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ∶𝐔 l)
    (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
    (q₂ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l ⊢
      c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
    (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ∶ 0)
    (q₄ : x # (C , C' , c₊ , c₊'))
    (q₅ : y # (c₊ , c₊'))
    -- helper hypothesis
    (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ∶𝐔 l)
    → ------------------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩ ∶ l

  𝚷Beta :
    {l l' : Lvl}
    {A : Ty}
    {a : Tm}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ∶ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
    (q₁ : Γ ⊢ a ∶ A ∶ l)
    (q₂ : x # (B , b))
    -- helper hypothesis
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    → ----------------------------------------------
    Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ∶ l'

  𝐈𝐝Beta :
    {l l' : Lvl}
    {A : Ty}
    {C : Ty[ 2 ]}
    {a c : Tm}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l ⊢
      C ⟨ x ⸴ y ⟩ ∶𝐔 l')
    (q₁ : Γ ⊢ a ∶ A ∶ l)
    (q₂ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
    (q₃ : x # C)
    (q₄ : y # C)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ∶𝐔 l)
    (h₁ : Γ ⸴ x ∶ A ∶ l ⊢ 𝐈𝐝 A a (𝐯 x) ∶𝐔 l)
    → -------------------------------------------------
    Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l'

  𝐍𝐚𝐭Beta₀ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
    (q₂ : x # (C , c₊))
    (q₃ : y # c₊)
    -- helper hypothesis
    (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ∶𝐔 l)
    → ------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l

  𝐍𝐚𝐭Beta₊ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    (q₀ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
    (q₁ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
      c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ∶ 0)
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    -- helper hypothesis
    (h : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ∶𝐔 l)
    → ------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ∶ l

  𝚷Eta :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ∶ max l l')
    (q₁ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ∶𝐔 l')
    -- helper hypothesis
    (h : Γ ⊢ A ∶𝐔 l)
    → -------------------------------------------------------
    Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B ∶ max l l'

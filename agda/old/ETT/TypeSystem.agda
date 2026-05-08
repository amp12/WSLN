module ETT.TypeSystem where

open import Prelude

open import WSLN

open import ETT.Syntax
open import ETT.Judgement

----------------------------------------------------------------------
-- Provable judgements in context
----------------------------------------------------------------------
infix 3 _⊢_
data Ok : Cx → Set
data _⊢_ (Γ : Cx) : Jg → Set

{- Some rules include helper hypotheses that aid proofs by structural
induction; versions of those rules without these hypotheses are
admissible; see ETT.AdmissibleRules. -}

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
    -- helper hypothesis
    (h : Ok Γ)
    → ----------------
    Ok (Γ ⸴ x ∶ A ⦂ l)

data _⊢_  Γ where
  --------------------------------
  -- Well-formed types: Γ ⊢ A ⦂ l
  --------------------------------
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
    (q₀ : Γ ⊢ A ⦂ l)
    -- Note the use of concretion:
    -- since B is a unary abstraction
    -- B ⟨ x ⟩ is an expression
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    -- We need that x is fresh for B
    -- in order to be able to deduce that
    -- the support of B is contained in
    -- the domain of Γ (see ETT.WellScoped)
    (q₂ : x # B)
    → -----------------------------------
    Γ ⊢ 𝚷 A B ⦂ max l l'

  ⊢𝐈𝐝 :
    {l : Lvl}
    {A : Ty}
    {a b : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------
    Γ ⊢ 𝐈𝐝 a b ⦂ l

  ⊢𝐍𝐚𝐭 :
    (q : Ok Γ)
    → -----------
    Γ ⊢ 𝐍𝐚𝐭 ⦂ 0

  Tm→Ty :
   {l : Lvl}
   {A : Tm}
   (q : Γ ⊢ A ∶ 𝐔 l ⦂ 1+ l)
   → ----------------------
   Γ ⊢ A ⦂ l

  -----------------------------------
  -- Well-formed terms: Γ ⊢ a ∶ A ⦂ l
  -----------------------------------
  ⊢conv :
    {l : Lvl}
    {a : Tm}
    {A A' : Ty}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    → ---------------------
    Γ ⊢ a ∶ A' ⦂ l

  ⊢𝐯 :
    {l : Lvl}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Ok Γ)
    (q₁ : (x , A , l) isIn Γ)
    → -----------------------
    Γ ⊢ 𝐯 x ∶ A ⦂ l

  Ty→Tm :
    {l : Lvl}
    {A : Ty}
    (q : Γ ⊢ A ⦂ l)
    → ----------------
    Γ ⊢ A ∶ 𝐔 l ⦂ 1+ l

  ⊢𝛌 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # (B , b))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    → ---------------------------------------------
    Γ ⊢ 𝛌 b ∶ 𝚷 A B ⦂ max l l'

  ⊢∙ :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    (q₃ : x # B)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------------------------
    Γ ⊢ b ∙ a ∶ B ⟨ a ⟩ ⦂ l'

  ⊢𝐫𝐞𝐟𝐥 :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
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
    --  helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C ⟨ x ⟩ ⦂ l)
    → -----------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ⦂ l

  ------------------------------------
  -- Type conversion: Γ ⊢ A ＝ A' ⦂ l
  ------------------------------------
  TyRefl :
    {l : Lvl}
    {A : Ty}
    (q : Γ ⊢ A ⦂ l)
    → --------------
    Γ ⊢ A ＝ A ⦂ l

  TySymm :
    {l : Lvl}
    {A A' : Ty}
    (q : Γ ⊢ A ＝ A' ⦂ l)
    → --------------------
    Γ ⊢ A' ＝ A ⦂ l

  TyTrans :
    {l : Lvl}
    {A A' A'' : Ty}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : Γ ⊢ A' ＝ A'' ⦂ l)
    → -----------------------
    Γ ⊢ A ＝ A'' ⦂ l

  𝚷Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : Γ ⸴ x ∶ A ⦂ l ⊢
      B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ⦂ l')
    (q₂ : x # (B , B'))
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -----------------------------
    Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ⦂ max l l'

  𝐈𝐝Cong :
    {l : Lvl}
    {A : Ty}
    {a a' b b' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------------
    Γ ⊢ 𝐈𝐝 a b ＝ 𝐈𝐝 a' b' ⦂ l

  =Tm→Ty :
   {l : Lvl}
   {A A' : Tm}
   (q : Γ ⊢ A ＝ A' ∶ 𝐔 l ⦂ 1+ l)
   → ----------------------------
   Γ ⊢ A ＝ A' ⦂ l

  ---------------------------------------
  -- Term conversion: Γ ⊢ a ＝ a' ∶ A ⦂ l
  ---------------------------------------
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
    → -------------------------
    Γ ⊢ a ＝ a'' ∶ A ⦂ l

  ＝conv :
    {l : Lvl}
    {A A' : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    → ------------------------
    Γ ⊢ a ＝ a' ∶ A' ⦂ l

  =Ty→Tm :
    {l : Lvl}
    {A A' : Ty}
    (q : Γ ⊢ A ＝ A' ⦂ l)
    → ----------------------
    Γ ⊢ A ＝ A' ∶ 𝐔 l ⦂ 1+ l

  ⊢Reflect :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    (q₂ : Γ ⊢ e ∶ 𝐈𝐝 a b ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -----------------------
    Γ ⊢ a ＝ b ∶ A ⦂ l

  𝛌Cong :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b b' : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⸴ x ∶ A ⦂ l ⊢
      b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
    (q₁ : x # (B , b , b'))
    -- helper hypothesis
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    → -------------------------------------
    Γ ⊢ 𝛌 b ＝ 𝛌 b' ∶ 𝚷 A B ⦂ max l l'

  ∙Cong :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a a' b b' : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₂ : x # B)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
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
    (q₀ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ⦂ l)
    (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
    (q₂ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l ⊢
      c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
    (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    (q₄ : x # (C , C' , c₊ , c₊'))
    (q₅ : y # (c₊ , c₊'))
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C ⟨ x ⟩ ⦂ l)
    → ------------------------------------------------------
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
    -- helper hypothesis
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    → -------------------------------------
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
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C ⟨ x ⟩ ⦂ l)
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
    -- helper hypothesis
    (h : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C ⟨ x ⟩ ⦂ l)
    → ------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ⦂ l

  𝚷Eta :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------------------------------
    Γ ⊢ b ＝ 𝛌 (x ．(b ∙ 𝐯 x)) ∶ 𝚷 A B ⦂ max l l'

  UIP :
    {l : Lvl}
    {A : Ty}
    {a b e : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    (q₂ : Γ ⊢ e ∶ 𝐈𝐝 a b ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → ------------------------
    Γ ⊢ e ＝ 𝐫𝐞𝐟𝐥 ∶ 𝐈𝐝 a b ⦂ l

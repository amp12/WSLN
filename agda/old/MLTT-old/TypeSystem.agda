module MLTT.TypeSystem where

open import Prelude
open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement

----------------------------------------------------------------------
-- Provable judgements in context
----------------------------------------------------------------------
infix 1 _⊢_
data Ok : Cx → Set
data _⊢_ (Γ : Cx) : Jg → Set

{- Some rules include helper hypotheses that aid proofs by structural
induction; versions of those rules without these hypotheses are
admissible; see MLTT.AdmissibleRules. -}

data Ok where
  -----------------------------
  -- Well-formed contexts: Ok Γ
  -----------------------------
  ◇ : Ok ◇
  [] :
    {l : Lvl}
    {Γ : Cx}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Γ ⊢ A ⦂ l)
    (q₁ : x # Γ)
    -- helper hypothesis
    (h : Ok Γ)
    → ----------------
    Ok (Γ ⨟ x ∶ A ⦂ l)

data _⊢_  Γ where
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

  ⊢𝐔 :
    {l : Lvl}
    (q : Ok Γ)
    → ---------------
    Γ ⊢ 𝐔 l ⦂ (1+ l)

  ⊢𝚷 :
    {l l' : Lvl}
    {A : Tm}
    {B : Tm[ 1 ]}
    {x : 𝔸}
    (q₀ : Γ ⊢ A ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    (q₂ : x # B)
    → ------------------------------------
    Γ ⊢ 𝚷 A B ⦂ (max l l')

  ⊢𝛌 :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l) ⊢ b [ x ] ∶ B [ x ] ⦂ l')
    (q₁ : x # (B , b))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    → ----------------------------------------------
    Γ ⊢ 𝛌 A b ∶ 𝚷 A B ⦂ max l l'

  ⊢∙ :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    (q₃ : x # B)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → ------------------------------------
    Γ ⊢ b ∙[ A , B ] a ∶ B [ a ] ⦂ l'

  ⊢𝐈𝐝 :
    {l : Lvl}
    {A a b : Tm}
    (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------
    Γ ⊢ 𝐈𝐝 A a b ⦂ l

  ⊢𝐫𝐞𝐟𝐥 :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ⦂ l)
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -----------------------
    Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ⦂ l

  ⊢𝐉 :
    {l l' : Lvl}
    {A : Ty}
    {C : Ty[ 2 ]}
    {a b c e : Tm}
    {x y : 𝔸}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯 x) ⦂ l) ⊢
      C [ x ][ y ] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : Γ ⊢ b ∶ A ⦂ l)
    (q₃ : Γ ⊢ c ∶ C [ a ][ 𝐫𝐞𝐟𝐥 a ] ⦂ l')
    (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b ⦂ l)
    -- could use x # y # C
    -- in place of the next two hypotheses
    (q₅ : x # C)
    (q₆ : y # C)
    --  helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a (𝐯 x) ⦂ l)
    → ------------------------------------------------
    Γ ⊢ 𝐉 C a b c e ∶ C [ b ][ e ] ⦂ l'

  ⊢𝐍𝐚𝐭 :
    (q : Ok Γ)
    → -----------
    Γ ⊢ 𝐍𝐚𝐭 ⦂ 0

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
    (q₀ : Γ ⊢ c₀ ∶ C [ 𝐳𝐞𝐫𝐨 ] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l) ⊢
      c₊ [ x ][ y ] ∶ C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    -- could use x # y # (C , c₊)
    -- in place of the next two hypotheses
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    --  helper hypothesis
    (h : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C [ x ] ⦂ l)
    → ----------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C [ a ] ⦂ l

  ---------------------------------------
  -- Term conversion: Γ ⊢ a ＝ a' ∶ A ⦂ l
  ---------------------------------------
  Refl :
    {l : Lvl}
    {A : Ty}
    {a : Tm}
    (q : Γ ⊢ a ∶ A ⦂ l)
    → -----------------
    Γ ⊢ a ＝ a ∶ A ⦂ l

  Symm :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    → -----------------------
    Γ ⊢ a' ＝ a ∶ A ⦂ l

  Trans :
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

  𝚷Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {x : 𝔸}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢
      B [ x ] ＝ B' [ x ] ⦂ l')
    (q₂ : x # (B , B'))
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → --------------------------------
    Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ⦂ (max l l')

  𝛌Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B : Ty[ 1 ]}
    {b b' : Tm[ 1 ]}
    {x : 𝔸}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢
      b [ x ] ＝ b' [ x ] ∶ B [ x ] ⦂ l')
    (q₂ : x # (B , b , b'))
    -- helper hypothesis
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    → -------------------------------------
    Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B ⦂ max l l'

  ∙Cong :
    {l l' : Lvl}
    {A A' : Ty}
    {B B' : Ty[ 1 ]}
    {a a' b b' : Tm}
    {x : 𝔸}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ＝ B' [ x ] ⦂ l')
    (q₂ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ⦂ max l l')
    (q₃ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₄ : x # (B , B'))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    → -----------------------------------------------------
    Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B [ a ] ⦂ l'

  𝐈𝐝Cong :
    {l : Lvl}
    {A A' : Ty}
    {a a' b b' : Tm}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
    → ------------------------------
    Γ ⊢ 𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ⦂ l

  𝐫𝐞𝐟𝐥Cong :
    {l : Lvl}
    {A : Ty}
    {a a' : Tm}
    (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    -- helper hypthesis
    (q₁ : Γ ⊢ A ⦂ l)
    → ----------------------------------
    Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ⦂ l

  𝐉Cong  :
    {l l' : Lvl}
    {A : Ty}
    {C C' : Ty[ 2 ]}
    {a a' b b' c c' e e' : Tm}
    {x y : 𝔸}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯 x) ⦂ l)  ⊢
      C [ x ][ y ] ＝ C' [ x ][ y ] ⦂ l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₂ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
    (q₃ : Γ ⊢ c ＝ c' ∶ C [ a ][ 𝐫𝐞𝐟𝐥 a ] ⦂ l')
    (q₄ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b ⦂ l)
    -- could use x # y # (C , C')
    -- in place of the next two hypotheses
    (q₅ : x # (C , C'))
    (q₆ : y # (C , C'))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a (𝐯 x) ⦂ l)
    → -----------------------------------------------------
    Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C [ b ][ e ] ⦂ l'

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
    (q₀ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C [ x ] ＝ C' [ x ] ⦂ l)
    (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C [ 𝐳𝐞𝐫𝐨 ] ⦂ l)
    (q₂ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l) ⊢
      c₊ [ x ][ y ] ＝ c₊' [ x ][ y ] ∶ C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l)
    (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
    -- could use x # y # (C , c₊)
    -- in place of the next two hypotheses
    (q₄ : x # (C , C' , c₊ , c₊'))
    (q₅ : y # (c₊ , c₊'))
    -- helper hypothesis
    (h : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C [ x ] ⦂ l)
    → -------------------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C [ a ] ⦂ l

  𝚷Beta :
    {l l' : Lvl}
    {A : Ty}
    {a : Tm}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l) ⊢ b [ x ] ∶ B [ x ] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : x # (B , b))
    -- helper hypothesis
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    → ----------------------------------------------
    Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b [ a ] ∶ B [ a ] ⦂ l'

  𝐈𝐝Beta :
    {l l' : Lvl}
    {A : Ty}
    {C : Ty[ 2 ]}
    {a c : Tm}
    {x y : 𝔸}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯 x) ⦂ l) ⊢
      C [ x ][ y ] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : Γ ⊢ c ∶ C [ a ][ 𝐫𝐞𝐟𝐥 a ] ⦂ l')
    -- could use x # y # C
    -- in place of the next two hypotheses
    (q₃ : x # C)
    (q₄ : y # C)
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a (𝐯 x) ⦂ l)
    → --------------------------------------------------
    Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C [ a ][ 𝐫𝐞𝐟𝐥 a ] ⦂ l'

  𝐍𝐚𝐭Beta₀ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    (q₀ : Γ ⊢ c₀ ∶ C [ 𝐳𝐞𝐫𝐨 ] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l) ⊢
      c₊ [ x ][ y ] ∶ C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l)
    -- could use x # y # (C , c₊)
    -- in place of the next two hypotheses
    (q₂ : x # (C , c₊))
    (q₃ : y # c₊)
    -- helper hypothesis
    (h : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C [ x ] ⦂ l)
    → --------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C [ 𝐳𝐞𝐫𝐨 ] ⦂ l

  𝐍𝐚𝐭Beta₊ :
    {l : Lvl}
    {C : Ty[ 1 ]}
    {c₀ a : Tm}
    {c₊ : Tm[ 2 ]}
    {x y : 𝔸}
    (q₀ : Γ ⊢ c₀ ∶ C [ 𝐳𝐞𝐫𝐨 ] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C [ x ] ⦂ l) ⊢
      c₊ [ x ][ y ] ∶ C [ 𝐬𝐮𝐜𝐜 (𝐯 x) ] ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
    -- could use x # y # (C , c₊)
    -- in place of the next two hypotheses
    (q₃ : x # (C , c₊))
    (q₄ : y # c₊)
    -- helper hypothesis
    (h : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C [ x ] ⦂ l)
    → ---------------------------------------------
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
    c₊ [ a ][ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ] ∶ C [ 𝐬𝐮𝐜𝐜 a ] ⦂ l

  𝚷Eta :
    {l l' : Lvl}
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm}
    {x : 𝔸}
    (q₀ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B [ x ] ⦂ l')
    -- helper hypothesis
    (h : Γ ⊢ A ⦂ l)
    → -------------------------------------------------------
    Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B ⦂ max l l'

----------------------------------------------------------------------
-- Context conversion
----------------------------------------------------------------------
infix 4 ⊢_＝_
data ⊢_＝_ : (Γ Γ' : Cx) → Set where
  ◇ : ⊢ ◇ ＝ ◇
  [] :
    {l : Lvl}
    {Γ Γ' : Cx}
    {A A' : Ty}
    {x : 𝔸}
    (q₀ : ⊢ Γ ＝ Γ')
    (q₁ : Γ ⊢ A ＝ A' ⦂ l)
    (q₂ : x # (Γ ,  Γ'))
    -- helper hypotheses
    (h₀ : Γ ⊢ A ⦂ l)
    (h₁ : Γ' ⊢ A' ⦂ l)
    → --------------------------------------
    ⊢ (Γ ⨟ x ∶ A ⦂ l) ＝ (Γ' ⨟ x ∶ A' ⦂ l)

----------------------------------------------------------------------
-- Well-typed renamings
----------------------------------------------------------------------
infix 4 _⊢ʳ_∶_
data _⊢ʳ_∶_ (Γ' : Cx) : Rn → Cx → Set where
  ◇ :
    {ρ : Rn}
    (q : Ok Γ')
    → ----------
    Γ' ⊢ʳ ρ ∶ ◇
  [] :
    {l : Lvl}
    {Γ : Cx}
    {ρ : Rn}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Γ' ⊢ʳ ρ ∶ Γ)
    (q₁ : Γ ⊢ A ⦂ l)
    (q₂ : (ρ x , ρ * A , l) isIn Γ')
    (q₃ : x # Γ)
    → ------------------------------
    Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A ⦂ l)

----------------------------------------------------------------------
-- Well-typed substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢ_∶_
data _⊢ˢ_∶_ (Γ' : Cx) : Sb → Cx → Set where
  ◇ :
    {σ : Sb}
    (q : Ok Γ')
    → ---------
    Γ' ⊢ˢ σ ∶ ◇
  [] :
    {l : Lvl}
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Γ' ⊢ˢ σ ∶ Γ)
    (q₁ : Γ ⊢ A ⦂ l)
    (q₂ : Γ' ⊢ σ x ∶ σ * A ⦂ l)
    (q₃ : x # Γ)
    → -------------------------
    Γ' ⊢ˢ σ ∶ (Γ ⨟ x ∶ A ⦂ l)

----------------------------------------------------------------------
-- Convertible well-typed substitutions
----------------------------------------------------------------------
infix 4 _⊢ˢ_＝_∶_
data _⊢ˢ_＝_∶_ (Γ' : Cx) : Sb → Sb → Cx → Set where
  ◇ :
    {σ σ' : Sb}
    (q : Ok Γ')
    → ---------------
    Γ' ⊢ˢ σ ＝ σ' ∶ ◇
  [] :
    {l : Lvl}
    {Γ : Cx}
    {σ σ' : Sb}
    {A : Ty}
    {x : 𝔸}
    (q₀ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
    (q₁ : Γ ⊢ A ⦂ l)
    (q₂ : Γ' ⊢ σ x ＝ σ' x ∶ σ * A ⦂ l)
    (q₃ : x # Γ)
    → ---------------------------------
    Γ' ⊢ˢ σ ＝ σ' ∶ (Γ ⨟ x ∶ A ⦂ l)

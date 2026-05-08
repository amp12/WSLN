module ETT.AdmissibleRules where

open import Decidable
open import Empty
open import Equivalence
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import ETT.Syntax
open import ETT.Judgement
open import ETT.TypeSystem
open import ETT.ContextConversion
open import ETT.Ok
open import ETT.WellScoped
open import ETT.Renaming
open import ETT.Substitution
open import ETT.ReflexivityInversion

----------------------------------------------------------------------
-- Well-formed contexts contain well-formed types
----------------------------------------------------------------------
ok→ty :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {x : 𝔸}
  (_ : Ok Γ)
  (_ : (x , A , l) isIn Γ)
  → ----------------------
  Γ ⊢ A ⦂ l

ok→ty (∷ q _)   isInNew      = wkJg _ q q
ok→ty (∷ q₀ q₁) (isInOld q₂) = wkJg _ q₀ (ok→ty q₁ q₂)

----------------------------------------------------------------------
-- Well-typed terms have well-formed types
----------------------------------------------------------------------
⊢∶ty :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  → -----------------
  Γ ⊢ A ⦂ l

⊢∶ty (⊢conv _ q) = ⊢Ty₂ q
⊢∶ty (⊢𝐯 q₀ q₁) = ok→ty q₀ q₁
⊢∶ty (Ty→Tm q) = ⊢𝐔 (⊢ok q)
⊢∶ty (⊢𝛌 _ (q₁ ∉∪ _) h₀ h₁) = ⊢𝚷 h₀ h₁ q₁
⊢∶ty (⊢∙{B = B}{x = x} _ q₁ q₂ q₃ _) = concTy B x q₂ q₁ q₃
⊢∶ty (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐈𝐝 q q h
⊢∶ty (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐍𝐚𝐭 q
⊢∶ty (⊢𝐬𝐮𝐜𝐜 q) = ⊢∶ty q
⊢∶ty (⊢𝐧𝐫𝐞𝐜{C = C}{x = x} _ _ q₂ (q₃ ∉∪ _) _ h) =
  concTy C x h q₂ q₃

----------------------------------------------------------------------
-- Properties of context conversion
----------------------------------------------------------------------

{- Reflexivity (CxRefl) was proved in ETT.ReflexivityInversion. -}

CxSymm :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  ⊢ Γ' ＝ Γ

CxSymm ◇ = ◇
CxSymm (∷ q₀ q₁ h₀ h₁) = ∷
  (CxSymm q₀)
  (＝⊢ (TySymm q₁) (CxSymm q₀))
  h₁
  h₀

CxTrans :
  {Γ Γ' Γ'' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  (_ : ⊢ Γ' ＝ Γ'')
  → ---------------
  ⊢ Γ ＝ Γ''

CxTrans ◇ ◇ = ◇
CxTrans (∷ q₀ q₁ h₀ _) (∷ q₀' q₁' _ h₁') = ∷
  (CxTrans q₀ q₀')
  (TyTrans q₁ (＝⊢ q₁' q₀))
  h₀
  h₁'

----------------------------------------------------------------------
-- Typing rules without helper hypotheses
----------------------------------------------------------------------
⊢𝐈𝐝⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A a b : Tm}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : Γ ⊢ b ∶ A ⦂ l)
  → -----------------
  Γ ⊢ 𝐈𝐝 a b ⦂ l

⊢𝐈𝐝⁻ q₀ q₁ = ⊢𝐈𝐝 q₀ q₁ (⊢∶ty q₀)

⊢𝛌⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
  (_ : x # (B , b))
  → --------------------------------------------
  Γ ⊢ 𝛌 b ∶ 𝚷 A B ⦂ max l l'

⊢𝛌⁻ q₀ q₁ = ⊢𝛌 q₀ q₁ (π₁ (∷⁻¹ q₀)) (⊢∶ty q₀)

⊢∙⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {a b : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
  (_ : Γ ⊢ a ∶ A ⦂ l)
  (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
  (_ : x # B)
  → -----------------------------------
  Γ ⊢ b ∙ a ∶ B ⟨ a ⟩ ⦂ l'

⊢∙⁻ q₀ q₁ q₂ q₃ = ⊢∙ q₀ q₁ q₂ q₃ (π₁ (∷⁻¹ q₂))

⊢𝐫𝐞𝐟𝐥⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ⦂ l)
  → -------------------
  Γ ⊢ 𝐫𝐞𝐟𝐥 ∶ 𝐈𝐝 a a ⦂ l

⊢𝐫𝐞𝐟𝐥⁻ q = ⊢𝐫𝐞𝐟𝐥 q (⊢∶ty q)

⊢𝐧𝐫𝐞𝐜⁻ :
  {l : Lvl}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ a : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
  (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
    c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
  (_ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → -----------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ⦂ l

⊢𝐧𝐫𝐞𝐜⁻ q₀ q₁ q₂ q₃ q₄ =
  ⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ (π₁ (∷⁻¹ q₁))

𝚷Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ＝ A' ⦂ l)
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ⦂ l')
  (_ : x # (B , B'))
  → --------------------------------
  Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ⦂ (max l l')

𝚷Cong⁻ q₀ q₁ q₂ = 𝚷Cong q₀ q₁ q₂ (⊢Ty₁ q₀)

𝐈𝐝Cong⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' b b' : Tm}
  (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (q₁ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
  → ------------------------
  Γ ⊢ 𝐈𝐝 a b ＝ 𝐈𝐝 a' b' ⦂ l

𝐈𝐝Cong⁻ q₀ q₁ = 𝐈𝐝Cong q₀ q₁ (⊢∶ty (⊢ty₁ q₀))

⊢Reflect⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a b e : Tm}
  (q₀ : Γ ⊢ a ∶ A ⦂ l)
  (q₁ : Γ ⊢ b ∶ A ⦂ l)
  (q₂ : Γ ⊢ e ∶ 𝐈𝐝 a b ⦂ l)
  → -----------------------
  Γ ⊢ a ＝ b ∶ A ⦂ l

⊢Reflect⁻ q₀ q₁ q₂ = ⊢Reflect q₀ q₁ q₂ (⊢∶ty q₀)

𝛌Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B : Ty[ 1 ]}
  {b b' : Tm[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⸴ x ∶ A ⦂ l ⊢
    b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
  (_ : x # (B , b , b'))
  → -----------------------------------
  Γ ⊢ 𝛌 b ＝ 𝛌 b' ∶ 𝚷 A B ⦂ max l l'

𝛌Cong⁻ q₀ q₁ = 𝛌Cong q₀ q₁ (π₁ (∷⁻¹ q₀)) (⊢∶ty (⊢ty₁ q₀))

∙Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {a a' b b' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ⦂ max l l')
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  (_ : x # B)
  → -----------------------------------------------------
  Γ ⊢ b ∙ a ＝ b' ∙ a' ∶ B ⟨ a ⟩ ⦂ l'

∙Cong⁻ q₀ q₁ q₂ = ∙Cong q₀ q₁ q₂ (⊢∶ty (⊢ty₁ q₁)) {!!}

-- 𝐫𝐞𝐟𝐥Cong⁻ :
--   {l : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {a a' : Tm}
--   (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
--   → ----------------------------------
--   Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ⦂ l

-- 𝐫𝐞𝐟𝐥Cong⁻ q = 𝐫𝐞𝐟𝐥Cong q (⊢∶ty (⊢ty₁ q))

-- 𝐉Cong⁻  :
--   {l l' : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {C C' : Ty[ 2 ]}
--   {a a' b b' c c' e e' : Tm}
--   {x y : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : y # (Γ , x) ⦄
--   (_ : Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⦂ l ⊢
--     C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ⦂ l')
--   (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
--   (_ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
--   (_ : Γ ⊢ c ＝ c' ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ⦂ l')
--   (_ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b ⦂ l)
--   (_ : x # (C , C'))
--   (_ : y # (C , C'))
--   → ----------------------------------------------------
--   Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C ⟨ b ⸴ e ⟩ ⦂ l'

-- 𝐉Cong⁻ q₀ q₁ q₂ q₃ q₄ q₅ q₆ =
--   𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆ (⊢∶ty (⊢ty₁ q₁)) (π₁ (∷⁻¹ q₀))

-- 𝐧𝐫𝐞𝐜Cong⁻ :
--   {l : Lvl}
--   {Γ : Cx}
--   {C C' : Ty[ 1 ]}
--   {c₀ c₀' a a'  : Tm}
--   {c₊ c₊' : Tm[ 2 ]}
--   {x y : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : y # (Γ , x) ⦄
--   (_ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ⦂ l)
--   (_ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
--   (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
--     c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
--   (_ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)
--   (_ : x # (C , C' , c₊ , c₊'))
--   (_ : y # (c₊ , c₊'))
--   → ----------------------------------------------------
--   Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩ ⦂ l

-- 𝐧𝐫𝐞𝐜Cong⁻ q₀ q₁ q₂ q₃ q₄ q₅ =
--   𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ (⊢ty₁ q₀)

-- 𝚷Beta⁻ :
--   {l l' : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {a : Tm}
--   {B : Ty[ 1 ]}
--   {b : Tm[ 1 ]}
--   {x : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ⦂ l')
--   (_ : Γ ⊢ a ∶ A ⦂ l)
--   (_ : x # (B , b))
--   → ----------------------------------------------
--   Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ⦂ l'

-- 𝚷Beta⁻ q₀ q₁ q₂ = 𝚷Beta q₀ q₁ q₂ (⊢∶ty q₁) (⊢∶ty q₀)

-- 𝐈𝐝Beta⁻ :
--   {l l' : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {C : Ty[ 2 ]}
--   {a c : Tm}
--   {x y : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : y # (Γ , x) ⦄
--   (_ : (Γ ⸴ x ∶ A ⦂ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⦂ l) ⊢
--     C ⟨ x ⸴ y ⟩ ⦂ l')
--   (_ : Γ ⊢ a ∶ A ⦂ l)
--   (_ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ⦂ l')
--   (_ : x # C)
--   (_ : y # C)
--   → -------------------------------------------------
--   Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ⦂ l'

-- 𝐈𝐝Beta⁻ q₀ q₁ q₂ q₃ q₄ =
--   𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄ (⊢∶ty q₁) (π₁ (∷⁻¹ q₀))

-- 𝐍𝐚𝐭Beta₀⁻ :
--   {l : Lvl}
--   {Γ : Cx}
--   {C : Ty[ 1 ]}
--   {c₀ : Tm}
--   {c₊ : Tm[ 2 ]}
--   {x y : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : y # (Γ , x) ⦄
--   (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
--   (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
--     c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
--   (_ : x # (C , c₊))
--   (_ : y # c₊)
--   → ------------------------------------------
--   Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l

-- 𝐍𝐚𝐭Beta₀⁻ q₀ q₁ q₂ q₃ =
--   𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ (π₁ (∷⁻¹ q₁))

-- 𝐍𝐚𝐭Beta₊⁻ :
--   {l : Lvl}
--   {Γ : Cx}
--   {C : Ty[ 1 ]}
--   {c₀ a : Tm}
--   {c₊ : Tm[ 2 ]}
--   {x y : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : y # (Γ , x) ⦄
--   (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ⦂ l)
--   (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⸴ y ∶ C ⟨ x ⟩ ⦂ l) ⊢
--     c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ⦂ l)
--   (_ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
--   (_ : x # (C , c₊))
--   (_ : y # c₊)
--   → ------------------------------------------
--   Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
--   c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ⦂ l

-- 𝐍𝐚𝐭Beta₊⁻ q₀ q₁ q₂ q₃ q₄ =
--   𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ (π₁ (∷⁻¹ q₁))

-- 𝚷Eta⁻ :
--   {l l' : Lvl}
--   {Γ : Cx}
--   {A : Ty}
--   {B : Ty[ 1 ]}
--   {b : Tm}
--   {x : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   (_ : Γ ⊢ b ∶ 𝚷 A B ⦂ max l l')
--   (_ : (Γ ⸴ x ∶ A ⦂ l) ⊢ B ⟨ x ⟩ ⦂ l')
--   → -------------------------------------------------------
--   Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B ⦂ max l l'

-- 𝚷Eta⁻ q₀ q₁ = 𝚷Eta q₀ q₁ (π₁ (∷⁻¹ q₁))

-- Cx∷⁻ :
--   {l : Lvl}
--   {Γ Γ' : Cx}
--   {A A' : Ty}
--   {x : 𝔸}
--   ⦃ _ : x # Γ ⦄
--   ⦃ _ : x # Γ' ⦄
--   (_ : ⊢ Γ ＝ Γ')
--   (_ : Γ ⊢ A ＝ A' ⦂ l)
--   → ------------------------------------
--   ⊢ (Γ ⸴ x ∶ A ⦂ l) ＝ (Γ' ⸴ x ∶ A' ⦂ l)

-- Cx∷⁻ q₀ q₁ =
--   ∷ q₀ q₁ (⊢ty₁ q₁) (＝⊢ (⊢ty₂ q₁) (CxSymm q₀))


-- ----------------------------------------------------------------------
-- -- Typing inversion for Pi-types
-- ----------------------------------------------------------------------
-- ⊢𝚷⁻¹₁ :
--   {Γ : Cx}
--   {l l' l'' : Lvl}
--   {A C : Ty}
--   {B : Ty[ 1 ]}
--   (_ : Γ ⊢ Pi ℓ ℓ' A B ∶ C ꞉ ℓ'')
--   → -----------------------------
--   Γ ⊢ A ꞉ ℓ

-- ⊢Pi⁻¹₁ (Pi p _ _) = p
-- ⊢Pi⁻¹₁ (conv p _) = ⊢Pi⁻¹₁ p

-- ⊢Pi⁻¹₂ :
--   {Γ : Cx}
--   {ℓ ℓ' ℓ'' : 𝕃}
--   {A C : Ty}
--   {B : Ty¹}
--   (_ : Γ ⊢ Pi ℓ ℓ' A B ∶ C ꞉ ℓ'')
--   → ------------------------------------------
--   ∃[ x ] x # B ∧ Γ ∷(x , A , ℓ) ⊢ B [ x ] ꞉ ℓ'

-- ⊢Pi⁻¹₂ (Pi _ p' (_ ∉∪ x#)) = (_ , x# , p')
-- ⊢Pi⁻¹₂ (conv p _) = ⊢Pi⁻¹₂ p

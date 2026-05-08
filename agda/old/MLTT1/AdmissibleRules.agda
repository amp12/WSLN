module MLTT1.AdmissibleRules where

open import Decidable
open import Empty
open import Equivalence
open import Identity
open import Instance
open import Nat
open import Notation
open import Product

open import WSLN

open import MLTT1.Syntax
open import MLTT1.Judgement
open import MLTT1.TypeSystem
open import MLTT1.ContextConversion
open import MLTT1.Ok
open import MLTT1.WellScoped
open import MLTT1.Renaming
open import MLTT1.Substitution
open import MLTT1.ReflexivityInversion

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
  Γ ⊢ A ∶𝐔 l

ok→ty (∷ q _) (isInNew refl) = wkJg _ q q
ok→ty (∷ q₀ q₁) (isInOld q₂) = wkJg _ q₀ (ok→ty q₁ q₂)

----------------------------------------------------------------------
-- Well-typed terms have well-formed types
----------------------------------------------------------------------
⊢∶ty :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ∶ l)
  → -----------------
  Γ ⊢ A ∶𝐔 l

⊢∶ty (⊢conv _ q) = ⊢ty₂ q
⊢∶ty (⊢𝐯 q₀ q₁) = ok→ty q₀ q₁
⊢∶ty (⊢𝐔 q) = ⊢𝐔 q
⊢∶ty (⊢𝚷 q _ _) = ⊢𝐔 (⊢ok q)
⊢∶ty (⊢𝛌 _ (q₁ ∉∪ _) h₀ h₁) = ⊢𝚷 h₀ h₁ q₁
⊢∶ty (⊢∙{B = B}{x = x} _ q₁ q₂ q₃ _) = concTy B x q₂ q₁ q₃
⊢∶ty (⊢𝐈𝐝 _ _ h) = ⊢∶ty h
⊢∶ty (⊢𝐫𝐞𝐟𝐥 q h) = ⊢𝐈𝐝 q q h
⊢∶ty{Γ = Γ} (⊢𝐉{l}{l'}{A}{C}{a}{b}{e = e}{x}{y}
  q₀ q₁ q₂ q₃ q₄ q₅ q₆ h₀ h₁)
  with (x#a ∉∪ x#A) ← ⊢# q₁ it =
  concTy² C x y q₀ q₂ q₄' q₅ q₆
  where
  q₄' : Γ ⊢ e ∶ (x ≔ b) * 𝐈𝐝 A a (𝐯 x) ∶ l
  q₄' rewrite ssbFresh x b A x#A
      | ssbFresh x b a x#a
      | updateEq{ι}{b} x = q₄
⊢∶ty (⊢𝐍𝐚𝐭 q) = ⊢𝐔 q
⊢∶ty (⊢𝐳𝐞𝐫𝐨 q) = ⊢𝐍𝐚𝐭 q
⊢∶ty (⊢𝐬𝐮𝐜𝐜 q) = ⊢∶ty q
⊢∶ty (⊢𝐧𝐫𝐞𝐜{C = C}{x = x} _ _ q₂ (q₃ ∉∪ _) _ h) =
  concTy C x h q₂ q₃

----------------------------------------------------------------------
-- Properties of context conversion
----------------------------------------------------------------------

{- Reflexivity (CxRefl) was proved in MLTT.ReflexivityInversion. -}

CxSymm :
  {Γ Γ' : Cx}
  (_ : ⊢ Γ ＝ Γ')
  → -------------
  ⊢ Γ' ＝ Γ

CxSymm ◇ = ◇
CxSymm (∷ q₀ q₁ h₀ h₁) = ∷
  (CxSymm q₀)
  (＝⊢ (Symm q₁) (CxSymm q₀))
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
  (Trans q₁ (＝⊢ q₁' q₀))
  h₀
  h₁'

----------------------------------------------------------------------
-- Typing rules without helper hypotheses
----------------------------------------------------------------------
⊢𝛌⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
  (_ : x # (B , b))
  → --------------------------------------------
  Γ ⊢ 𝛌 A b ∶ 𝚷 A B ∶ max l l'

⊢𝛌⁻ q₀ q₁ = ⊢𝛌 q₀ q₁ (π₁ (∷⁻¹ q₀)) (⊢∶ty q₀)

⊢∙⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {a b : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ b ∶ 𝚷 A B ∶ max l l')
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ⟨ x ⟩ ∶𝐔 l')
  (_ : x # B)
  → -----------------------------------
  Γ ⊢ b ∙[ A , B ] a ∶ B ⟨ a ⟩ ∶ l'

⊢∙⁻ q₀ q₁ q₂ q₃ = ⊢∙ q₀ q₁ q₂ q₃ (π₁ (∷⁻¹ q₂))

⊢𝐈𝐝⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A a b : Tm}
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : Γ ⊢ b ∶ A ∶ l)
  → ------------------
  Γ ⊢ 𝐈𝐝 A a b ∶𝐔 l

⊢𝐈𝐝⁻ q₀ q₁ = ⊢𝐈𝐝 q₀ q₁ (⊢∶ty q₀)

⊢𝐫𝐞𝐟𝐥⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  (_ : Γ ⊢ a ∶ A ∶ l)
  → -----------------------
  Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ∶ l

⊢𝐫𝐞𝐟𝐥⁻ q = ⊢𝐫𝐞𝐟𝐥 q (⊢∶ty q)

⊢𝐉⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {C : Ty[ 2 ]}
  {a b c e : Tm}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l) ⊢
    C ⟨ x ⸴ y ⟩ ∶𝐔 l')
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : Γ ⊢ b ∶ A ∶ l)
  (_ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
  (_ : Γ ⊢ e ∶ 𝐈𝐝 A a b ∶ l)
  (_ : x # C)
  (_ : y # C)
  → -------------------------------------------
  Γ ⊢ 𝐉 C a b c e ∶ C ⟨ b ⸴ e ⟩ ∶ l'

⊢𝐉⁻ q₀ q₁ q₂ q₃ q₄ q₅ q₆ =
  ⊢𝐉 q₀ q₁ q₂ q₃ q₄ q₅ q₆ (⊢∶ty q₁) (π₁ (∷⁻¹ q₀))

⊢𝐧𝐫𝐞𝐜⁻ :
  {l : Lvl}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ a : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
  (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
    c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
  (_ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ∶ 0)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → -----------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ∶ C ⟨ a ⟩ ∶ l

⊢𝐧𝐫𝐞𝐜⁻ q₀ q₁ q₂ q₃ q₄ =
  ⊢𝐧𝐫𝐞𝐜 q₀ q₁ q₂ q₃ q₄ (π₁ (∷⁻¹ q₁))

𝚷Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ＝ A' ∶𝐔 l)
  (_ : Γ ⸴ x ∶ A ∶ l ⊢
    B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶𝐔 l')
  (_ : x # (B , B'))
  → --------------------------------
  Γ ⊢ 𝚷 A B ＝ 𝚷 A' B' ∶𝐔 (max l l')

𝚷Cong⁻ q₀ q₁ q₂ = 𝚷Cong q₀ q₁ q₂ (⊢ty₁ q₀)

𝛌Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B : Ty[ 1 ]}
  {b b' : Tm[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ＝ A' ∶𝐔 l)
  (_ : Γ ⸴ x ∶ A ∶ l ⊢
    b ⟨ x ⟩ ＝ b' ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
  (_ : x # (B , b , b'))
  → -------------------------------------
  Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 A B ∶ max l l'

𝛌Cong⁻ q₀ q₁ q₂ =
  𝛌Cong q₀ q₁ q₂ (⊢ty₁ q₀) (⊢∶ty (⊢ty₁ q₁))

∙Cong⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A A' : Ty}
  {B B' : Ty[ 1 ]}
  {a a' b b' : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ A ＝ A' ∶𝐔 l)
  (_ : Γ ⸴ x ∶ A ∶ l ⊢ B ⟨ x ⟩ ＝ B' ⟨ x ⟩ ∶𝐔 l')
  (_ : Γ ⊢ b ＝ b' ∶ 𝚷 A B ∶ max l l')
  (_ : Γ ⊢ a ＝ a' ∶ A ∶ l)
  (_ : x # (B , B'))
  → -----------------------------------------------------
  Γ ⊢ b ∙[ A , B ] a ＝ b' ∙[ A' , B' ] a' ∶ B ⟨ a ⟩ ∶ l'

∙Cong⁻ q₀ q₁ q₂ q₃ q₄ =
  ∙Cong q₀ q₁ q₂ q₃ q₄ (⊢ty₁ q₀) (⊢ty₁ q₁)

𝐫𝐞𝐟𝐥Cong⁻ :
  {l : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (_ : Γ ⊢ a ＝ a' ∶ A ∶ l)
  → ----------------------------------
  Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ∶ l

𝐫𝐞𝐟𝐥Cong⁻ q = 𝐫𝐞𝐟𝐥Cong q (⊢∶ty (⊢ty₁ q))

𝐉Cong⁻  :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {C C' : Ty[ 2 ]}
  {a a' b b' c c' e e' : Tm}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l ⊢
    C ⟨ x ⸴ y ⟩ ＝ C' ⟨ x ⸴ y ⟩ ∶𝐔 l')
  (_ : Γ ⊢ a ＝ a' ∶ A ∶ l)
  (_ : Γ ⊢ b ＝ b' ∶ A ∶ l)
  (_ : Γ ⊢ c ＝ c' ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
  (_ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b ∶ l)
  (_ : x # (C , C'))
  (_ : y # (C , C'))
  → ----------------------------------------------------
  Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C ⟨ b ⸴ e ⟩ ∶ l'

𝐉Cong⁻ q₀ q₁ q₂ q₃ q₄ q₅ q₆ =
  𝐉Cong q₀ q₁ q₂ q₃ q₄ q₅ q₆ (⊢∶ty (⊢ty₁ q₁)) (π₁ (∷⁻¹ q₀))

𝐧𝐫𝐞𝐜Cong⁻ :
  {l : Lvl}
  {Γ : Cx}
  {C C' : Ty[ 1 ]}
  {c₀ c₀' a a'  : Tm}
  {c₊ c₊' : Tm[ 2 ]}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⊢ C ⟨ x ⟩ ＝ C' ⟨ x ⟩ ∶𝐔 l)
  (_ : Γ ⊢ c₀ ＝ c₀' ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
  (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
    c₊ ⟨ x ⸴ y ⟩ ＝ c₊' ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
  (_ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ∶ 0)
  (_ : x # (C , C' , c₊ , c₊'))
  (_ : y # (c₊ , c₊'))
  → ----------------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ＝ 𝐧𝐫𝐞𝐜 C' c₀' c₊' a' ∶ C ⟨ a ⟩ ∶ l

𝐧𝐫𝐞𝐜Cong⁻ q₀ q₁ q₂ q₃ q₄ q₅ =
  𝐧𝐫𝐞𝐜Cong q₀ q₁ q₂ q₃ q₄ q₅ (⊢ty₁ q₀)

𝚷Beta⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {a : Tm}
  {B : Ty[ 1 ]}
  {b : Tm[ 1 ]}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ b ⟨ x ⟩ ∶ B ⟨ x ⟩ ∶ l')
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : x # (B , b))
  → ----------------------------------------------
  Γ ⊢ 𝛌 A b ∙[ A , B ] a ＝ b ⟨ a ⟩ ∶ B ⟨ a ⟩ ∶ l'

𝚷Beta⁻ q₀ q₁ q₂ = 𝚷Beta q₀ q₁ q₂ (⊢∶ty q₁) (⊢∶ty q₀)

𝐈𝐝Beta⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {C : Ty[ 2 ]}
  {a c : Tm}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : (Γ ⸴ x ∶ A ∶ l ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ∶ l) ⊢
    C ⟨ x ⸴ y ⟩ ∶𝐔 l')
  (_ : Γ ⊢ a ∶ A ∶ l)
  (_ : Γ ⊢ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l')
  (_ : x # C)
  (_ : y # C)
  → -------------------------------------------------
  Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C ⟨ a ⸴ 𝐫𝐞𝐟𝐥 a ⟩ ∶ l'

𝐈𝐝Beta⁻ q₀ q₁ q₂ q₃ q₄ =
  𝐈𝐝Beta q₀ q₁ q₂ q₃ q₄ (⊢∶ty q₁) (π₁ (∷⁻¹ q₀))

𝐍𝐚𝐭Beta₀⁻ :
  {l : Lvl}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
  (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
    c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → ------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l

𝐍𝐚𝐭Beta₀⁻ q₀ q₁ q₂ q₃ =
  𝐍𝐚𝐭Beta₀ q₀ q₁ q₂ q₃ (π₁ (∷⁻¹ q₁))

𝐍𝐚𝐭Beta₊⁻ :
  {l : Lvl}
  {Γ : Cx}
  {C : Ty[ 1 ]}
  {c₀ a : Tm}
  {c₊ : Tm[ 2 ]}
  {x y : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : y # (Γ , x) ⦄
  (_ : Γ ⊢ c₀ ∶ C ⟨ 𝐳𝐞𝐫𝐨 ⟩ ∶ l)
  (_ : (Γ ⸴ x ∶ 𝐍𝐚𝐭 ∶ 0 ⸴ y ∶ C ⟨ x ⟩ ∶ l) ⊢
    c₊ ⟨ x ⸴ y ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 (𝐯 x) ⟩ ∶ l)
  (_ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ∶ 0)
  (_ : x # (C , c₊))
  (_ : y # c₊)
  → ------------------------------------------
  Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ c₊ (𝐬𝐮𝐜𝐜 a) ＝
  c₊ ⟨ a ⸴ 𝐧𝐫𝐞𝐜 C c₀ c₊ a ⟩ ∶ C ⟨ 𝐬𝐮𝐜𝐜 a ⟩ ∶ l

𝐍𝐚𝐭Beta₊⁻ q₀ q₁ q₂ q₃ q₄ =
  𝐍𝐚𝐭Beta₊ q₀ q₁ q₂ q₃ q₄ (π₁ (∷⁻¹ q₁))

𝚷Eta⁻ :
  {l l' : Lvl}
  {Γ : Cx}
  {A : Ty}
  {B : Ty[ 1 ]}
  {b : Tm}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  (_ : Γ ⊢ b ∶ 𝚷 A B ∶ max l l')
  (_ : (Γ ⸴ x ∶ A ∶ l) ⊢ B ⟨ x ⟩ ∶𝐔 l')
  → -------------------------------------------------------
  Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A , B ] 𝐯 x)) ∶ 𝚷 A B ∶ max l l'

𝚷Eta⁻ q₀ q₁ = 𝚷Eta q₀ q₁ (π₁ (∷⁻¹ q₁))

Cx∷⁻ :
  {l : Lvl}
  {Γ Γ' : Cx}
  {A A' : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x # Γ' ⦄
  (_ : ⊢ Γ ＝ Γ')
  (_ : Γ ⊢ A ＝ A' ∶𝐔 l)
  → ------------------------------------
  ⊢ (Γ ⸴ x ∶ A ∶ l) ＝ (Γ' ⸴ x ∶ A' ∶ l)

Cx∷⁻ q₀ q₁ =
  ∷ q₀ q₁ (⊢ty₁ q₁) (＝⊢ (⊢ty₂ q₁) (CxSymm q₀))

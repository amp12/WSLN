module MLTT.StandardModel.ExpressionSemantics where

open import Decidable
open import Empty
open import Function
open import Identity
open import Instance
open import Level
open import Nat
open import Notation
open import Product
open import Unit

open import WSLN

open import MLTT.Syntax
open import MLTT.Judgement
open import MLTT.TypeSystem
open import MLTT.ContextConversion
open import MLTT.Ok
open import MLTT.WellScoped
open import MLTT.Renaming
open import MLTT.Substitution
open import MLTT.ReflexivityInversion
open import MLTT.AdmissibleRules

open import MLTT.StandardModel.CwF

----------------------------------------------------------------------
-- Semantics of contexts, types and terms
----------------------------------------------------------------------
infix 5 ⟦_ok⟧=_ ⟦_⊢_ty⟧=_⊩_ ⟦_⊢_vr⟧=_⊩_∋_ ⟦_⊢_tm⟧=_⊩_∋_
data ⟦_ok⟧=_ : Cx → 𝒞𝓍 → Set₂
data ⟦_⊢_ty⟧=_⊩_ (Γ : Cx) : Ty → (C : 𝒞𝓍) → 𝒯𝓎 C → Set₂
data ⟦_⊢_vr⟧=_⊩_∋_ : Cx → 𝔸 → (C : 𝒞𝓍)(T : 𝒯𝓎 C) → 𝒯𝓂 C T → Set₂
data ⟦_⊢_tm⟧=_⊩_∋_ (Γ : Cx) : Tm → (C : 𝒞𝓍)(T : 𝒯𝓎 C) → 𝒯𝓂 C T → Set₂

data ⟦_ok⟧=_ where
  ⟦◇⟧ : ⟦ ◇ ok⟧= 𝟙

  ⟦∷⟧ :
    {Γ : Cx}
    {x : 𝔸}
    {A : Ty}
    ⦃ _ : x ∉ dom Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    → -----------------------
    ⟦ Γ ⸴ x ∶ A ok⟧= C ⋉ T

data ⟦_⊢_ty⟧=_⊩_ Γ where
  ⟦𝚷⟧ :
    {A : Ty}
    {B : Ty[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {T' : 𝒯𝓎 (C ⋉ T)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₂ : ⟦ Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty⟧= C ⋉ T ⊩ T')
    (q₃ : x # B)
    → ------------------------------------------
    ⟦ Γ ⊢ 𝚷 A B ty⟧= C ⊩ 𝒫𝒾 T T'

  ⟦𝐈𝐝⟧ :
    {A : Ty}
    {a a' : Tm}
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {t t' : 𝒯𝓂 C T}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₂ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
    (q₃ : ⟦ Γ ⊢ a' tm⟧= C ⊩ T ∋ t')
    → --------------------------------
    ⟦ Γ ⊢ 𝐈𝐝 A a a' ty⟧= C ⊩ ℐ𝒹 T t t'

  ⟦𝐔⟧ :
    {C : 𝒞𝓍}
    (q : ⟦ Γ ok⟧= C)
    → ----------------
    ⟦ Γ ⊢ 𝐔 ty⟧= C ⊩ 𝒰

  ⟦𝐄𝐥⟧ :
    {A : Tm}
    {C : 𝒞𝓍}
    {t : 𝒯𝓂 C 𝒰}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A tm⟧= C ⊩ 𝒰 ∋ t)
    → ---------------------------
    ⟦ Γ ⊢ A ty⟧= C ⊩ ℰ𝓁 t

data ⟦_⊢_vr⟧=_⊩_∋_ where
  ⟦new⟧ :
    {Γ : Cx}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    → --------------------------------------
    ⟦ Γ ⸴ x ∶ A ⊢ x vr⟧= C ⋉ T ⊩ T ○ 𝓅₁ ∋ 𝓅₂

  ⟦old⟧ :
    {Γ : Cx}
    {A' : Ty}
    {x x' : 𝔸}
    ⦃ _ : x' # Γ ⦄
    {C : 𝒞𝓍}
    {T T' : 𝒯𝓎 C}
    {t : 𝒯𝓂 C T}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₀ : ⟦ Γ ⊢ x vr⟧= C ⊩ T ∋ t)
    (q₁ : ⟦ Γ ⊢ A' ty⟧= C ⊩ T')
    → ---------------------------------------------
    ⟦ Γ ⸴ x' ∶ A' ⊢ x vr⟧= C ⋉ T' ⊩ T ○ 𝓅₁ ∋ t ○ 𝓅₁

data ⟦_⊢_tm⟧=_⊩_∋_ Γ where
  ⟦𝐯⟧ :
    {x : 𝔸}
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {t : 𝒯𝓂 C T}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ x vr⟧= C ⊩ T ∋ t)
    → --------------------------
    ⟦ Γ ⊢ 𝐯 x tm⟧= C ⊩ T ∋ t

  ⟦𝚷⟧ :
    {A : Tm}
    {B : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓂 C 𝒰}
    {T' : 𝒯𝓂 (C ⋉ ℰ𝓁 T) 𝒰}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A tm⟧= C ⊩ 𝒰 ∋ T)
    (q₂ : ⟦ Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ tm⟧=
      C ⋉ ℰ𝓁 T ⊩ 𝒰 ∋ T')
    (q₃ : x # B)
    → -------------------------------
    ⟦ Γ ⊢ 𝚷 A B tm⟧= C ⊩ 𝒰 ∋ 𝒫𝒾₀ T T'

  ⟦𝛌⟧ :
    {A : Ty}
    {B : Ty[ 1 ]}
    {b : Tm[ 1 ]}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {T' : 𝒯𝓎 (C ⋉ T)}
    {t : 𝒯𝓂 (C ⋉ T) T'}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₂ : ⟦ Γ ⸴ x ∶ A ⊢ b ⟨ x ⟩ tm⟧= C ⋉ T ⊩ T' ∋ t)
    (q₃ : x # b)
    → ----------------------------------------------
    ⟦ Γ ⊢ 𝛌 A b tm⟧= C ⊩ 𝒫𝒾 T T' ∋ 𝓁𝒶𝓂 t

  ⟦∙⟧ :
    {A : Ty}
    {B : Ty[ 1 ]}
    {a b : Tm}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {T' : 𝒯𝓎 (C ⋉ T)}
    {t' : 𝒯𝓂 C (𝒫𝒾 T T')}
    {t : 𝒯𝓂 C T}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₂ : ⟦ Γ ⸴ x ∶ A ⊢ B ⟨ x ⟩ ty⟧= C ⋉ T ⊩ T')
    (q₃ : ⟦ Γ ⊢ b tm⟧= C ⊩ 𝒫𝒾 T T' ∋ t')
    (q₄ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
    (q₅ : x # B)
    → -------------------------------------------------
    ⟦ Γ ⊢ b ∙[ A , B ] a tm⟧= C ⊩ T' ○[ t ] ∋  𝒶𝓅𝓅 t' t

  ⟦𝐈𝐝⟧ :
    {A a a' : Tm}
    {C : 𝒞𝓍}
    {T : 𝒯𝓂 C 𝒰}
    {t t' : 𝒯𝓂 C (ℰ𝓁 T)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A tm⟧= C ⊩ 𝒰 ∋ T)
    (q₂ : ⟦ Γ ⊢ a tm⟧= C ⊩ ℰ𝓁 T ∋ t)
    (q₃ : ⟦ Γ ⊢ a' tm⟧= C ⊩ ℰ𝓁 T ∋ t')
    → -------------------------------------
    ⟦ Γ ⊢ 𝐈𝐝 A a a' tm⟧= C ⊩ 𝒰 ∋ ℐ𝒹₀ T t t'

  ⟦𝐫𝐞𝐟𝐥⟧ :
    {A : Ty}
    {a : Tm}
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {t : 𝒯𝓂 C T}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
    → -------------------------------------
    ⟦ Γ ⊢ 𝐫𝐞𝐟𝐥 a tm⟧= C ⊩ ℐ𝒹 T t t ∋ 𝓇ℯ𝒻𝓁 t

  ⟦𝐉⟧ :
    {A : Ty}
    {B : Ty[ 2 ]}
    {a a' b e : Tm}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 C}
    {t t' : 𝒯𝓂 C T}
    {T' : 𝒯𝓎 (C ⋉ T ⋉ ℐ𝒹 (T ○ 𝓅₁) (t ○ 𝓅₁) 𝓅₂)}
    {t₁ : 𝒯𝓂 C (T' ○[ t ⸴ 𝓇ℯ𝒻𝓁 t ])}
    {t₂ : 𝒯𝓂 C (ℐ𝒹 T t t')}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₂ : ⟦ Γ ⸴ x ∶ A ⸴ y ∶ 𝐈𝐝 A a (𝐯 x) ⊢ B ⟨ x ⸴ y ⟩ ty⟧=
       C ⋉ T ⋉ ℐ𝒹 (T ○ 𝓅₁) (t ○ 𝓅₁) 𝓅₂ ⊩ T')
    (q₃ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
    (q₄ : ⟦ Γ ⊢ a' tm⟧= C ⊩ T ∋ t')
    (q₅ : ⟦ Γ ⊢ b tm⟧= C ⊩ T' ○[ t ⸴ 𝓇ℯ𝒻𝓁 t ] ∋ t₁)
    (q₆ : ⟦ Γ ⊢ e tm⟧= C ⊩ ℐ𝒹 T t t' ∋ t₂)
    (q₇ : x # B)
    (q₈ : y # B)
    → ------------------------------------------------------
    ⟦ Γ ⊢ 𝐉 B a a' b e tm⟧= C ⊩ T' ○[ t' ⸴ t₂ ] ∋ 𝒥 T' t₁ t₂

  ⟦𝐍𝐚𝐭⟧ :
    {C : 𝒞𝓍}
    (q : ⟦ Γ ok⟧= C)
    → ------------------------
    ⟦ Γ ⊢ 𝐍𝐚𝐭 tm⟧= C ⊩ 𝒰 ∋ 𝒩𝒶𝓉

  ⟦𝐳𝐞𝐫𝐨⟧ :
    {C : 𝒞𝓍}
    (q : ⟦ Γ ok⟧= C)
    → -------------------------------
    ⟦ Γ ⊢ 𝐳𝐞𝐫𝐨 tm⟧= C ⊩ ℰ𝓁 𝒩𝒶𝓉 ∋ 𝓏ℯ𝓇ℴ


  ⟦𝐬𝐮𝐜𝐜⟧ :
    {a : Tm}
    {C : 𝒞𝓍}
    {t : 𝒯𝓂 C (ℰ𝓁 𝒩𝒶𝓉)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ ⊢ a tm⟧= C ⊩ ℰ𝓁 𝒩𝒶𝓉 ∋ t)
    → -----------------------------------
    ⟦ Γ ⊢ 𝐬𝐮𝐜𝐜 a tm⟧= C ⊩ ℰ𝓁 𝒩𝒶𝓉 ∋ 𝓈𝓊𝒸𝒸 t

  ⟦𝐧𝐫𝐞𝐜⟧ :
    {B : Ty[ 1 ]}
    {b₀ a : Tm}
    {b₊ : Tm[ 2 ]}
    {x y : 𝔸}
    ⦃ _ : x # Γ ⦄
    ⦃ _ : y # (Γ , x) ⦄
    {C : 𝒞𝓍}
    {T : 𝒯𝓎 (C ⋉ ℰ𝓁 𝒩𝒶𝓉)}
    {t₀ : 𝒯𝓂 C (T ○[ 𝓏ℯ𝓇ℴ ])}
    {t₊ : 𝒯𝓂 (C ⋉ ℰ𝓁 𝒩𝒶𝓉 ⋉ T) (T ○ (⟪ 𝓅₁ , 𝓈𝓊𝒸𝒸 𝓅₂ ⟫ ∘ 𝓅₁))}
    {t : 𝒯𝓂 C (ℰ𝓁 𝒩𝒶𝓉)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦  Γ ⸴ x ∶ 𝐍𝐚𝐭 ⊢ B ⟨ x ⟩ ty⟧= C ⋉ ℰ𝓁 𝒩𝒶𝓉 ⊩ T)
    (q₂ : ⟦ Γ ⊢ b₀ tm⟧= C ⊩ T ○[ 𝓏ℯ𝓇ℴ ] ∋ t₀)
    (q₃ : ⟦ Γ ⸴ x ∶ 𝐍𝐚𝐭 ⸴ y ∶ B ⟨ x ⟩ ⊢ b₊ ⟨ x ⸴ y ⟩ tm⟧=
      C ⋉ ℰ𝓁 𝒩𝒶𝓉 ⋉ T ⊩ T ○ (⟪ 𝓅₁ , 𝓈𝓊𝒸𝒸 𝓅₂ ⟫ ∘ 𝓅₁) ∋ t₊)
    (q₄ : ⟦ Γ ⊢ a tm⟧= C ⊩ ℰ𝓁 𝒩𝒶𝓉 ∋ t)
    (q₅ : x # (B , b₊))
    (q₆ : y # b₊)
    → -----------------------------------------------------
    ⟦ Γ ⊢ 𝐧𝐫𝐞𝐜 B b₀ b₊ a tm⟧= C ⊩ T ○[ t ] ∋ 𝓃𝓇ℯ𝒸 T t₀ t₊ t

module MLTT.StandardModel.Renaming where

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
open import MLTT.StandardModel.ExpressionSemantics

----------------------------------------------------------------------
-- Semantics of renaming
----------------------------------------------------------------------
infix 5 ⟦_⊢_∶_rn⟧=_⟶_∋_
data ⟦_⊢_∶_rn⟧=_⟶_∋_ (Γ' : Cx) :
  (_ : Rn)
  (_ : Cx)
  (C' C : 𝒞𝓍)
  (_ : C' → C)
  → ----------
  Set₂
  where
  ⟦◇⟧ :
    {ρ : Rn}
    {C' : 𝒞𝓍}
    (q : ⟦ Γ' ok⟧= C')
    → -----------------------------------
    ⟦ Γ' ⊢ ρ ∶ ◇ rn⟧= C' ⟶ 𝟙 ∋ (λ _ → tt)
  ⟦∷⟧ :
    {Γ : Cx}
    {ρ : Rn}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C C' : 𝒞𝓍}
    {T :  𝒯𝓎 C}
    {f : C' → C}
    {t' : 𝒯𝓂 C' (T ○ f)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ' ok⟧= C')
    (q₂ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
    (q₃ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₄ : ⟦ Γ' ⊢ ρ x vr⟧= C' ⊩ T ○ f ∋ t')
    → -------------------------------------------------
    ⟦ Γ' ⊢ ρ ∶ (Γ ⸴ x ∶ A) rn⟧= C' ⟶ C ⋉ T ∋ ⟪ f , t' ⟫

-- Inversion
⟦∷⟧⁻¹ :
  {Γ Γ' : Cx}
  {ρ : Rn}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ ⦄
  {C' D : 𝒞𝓍}
  {f' : C' → D}
  (_ : ⟦ Γ' ⊢ ρ ∶ (Γ ⸴ x ∶ A) rn⟧= C' ⟶ D ∋ f')
  → -------------------------------------------
  ∑[ C ∈ 𝒞𝓍 ]
  ∑[ T ∈ 𝒯𝓎 C ]
  ∑[ f ∈ (C' → C) ]
  ∑[ t' ∈ 𝒯𝓂 C' (T ○ f) ]
  (⟦ Γ ok⟧= C)
  ×
  (⟦ Γ' ok⟧= C')
  ×
  (⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  ×
  (⟦ Γ ⊢ A ty⟧= C ⊩ T)
  ×
  (⟦ Γ' ⊢ ρ x vr⟧= C' ⊩ T ○ f ∋ t')
  ×
  ∑[ e ∈ D ≡ C ⋉ T ]
  (subst (λ D' → (C' → D')) e f' ≡ ⟪ f , t' ⟫)

⟦∷⟧⁻¹ (⟦∷⟧{C = C}{T = T}{f}{t'} q₀ q₁ q₂ q₃ q₄) =
  (C , T , f , t' , q₀ , q₁ , q₂ , q₃ , q₄ , refl , refl)

-- Well-formed contexts
⟦rnOk⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  → --------------------------------
  ⟦ Γ ok⟧= C

⟦rnOk⟧ (⟦◇⟧ q) = ⟦◇⟧
⟦rnOk⟧ (⟦∷⟧ q _ _ q' _) = ⟦∷⟧ q q'

⟦okRn⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  → --------------------------------
  ⟦ Γ' ok⟧= C'

⟦okRn⟧ (⟦◇⟧ q) = q
⟦okRn⟧ (⟦∷⟧ _ q _ _ _) = q

-- Weakening renamings
⟦wkRn⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {x : 𝔸}
  ⦃ _ : x # Γ' ⦄
  {C C' : 𝒞𝓍}
  {T' :  𝒯𝓎 C'}
  {f : C' → C}
  (_ : ⟦ Γ' ok⟧= C')
  (_ : ⟦ Γ' ⊢ A ty⟧= C' ⊩ T')
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  → --------------------------------------------
  ⟦ Γ' ⸴ x ∶ A ⊢ ρ ∶ Γ rn⟧= C' ⋉ T' ⟶ C ∋ f ○ 𝓅₁

⟦wkRn⟧ q q' (⟦◇⟧ _) = ⟦◇⟧ (⟦∷⟧ q q')
⟦wkRn⟧ q q' (⟦∷⟧ q₀ q₁ q₂ q₃ q₄) =
  ⟦∷⟧ q₀ (⟦∷⟧ q q') (⟦wkRn⟧ q q' q₂) q₃ (⟦old⟧ q q₄ q')

-- Extensionality
⟦rnExt⟧ :
  {ρ ρ' : Rn}
  {Γ Γ' : Cx}
  {C C' : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  (_ : ∀ x → x ∈ dom Γ → ρ x ≡ ρ' x)
  → --------------------------------
  ⟦ Γ' ⊢ ρ' ∶ Γ rn⟧= C' ⟶ C ∋ f

⟦rnExt⟧ (⟦◇⟧ q) _ = ⟦◇⟧ q
⟦rnExt⟧{Γ' = Γ'} (⟦∷⟧{x = x}{C' = C'}{T}{f}{t'} q₀ q₁ q₂ q₃ q₄) e =
  ⟦∷⟧ q₀ q₁ (⟦rnExt⟧ q₂ (λ x r → e x (∈∪₁ r))) q₃
    (subst (λ y → ⟦ Γ' ⊢ y vr⟧= C' ⊩ T ○ f ∋ t') (e x (∈∪₂ ∈｛｝)) q₄)

-- Lifting renamings
⟦liftRn⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  {C C' : 𝒞𝓍}
  {T :  𝒯𝓎 C}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
  (_ : ⟦ Γ' ⊢ ρ * A ty⟧= C' ⊩ T ○ f)
  → -----------------------------------------------
  ⟦ Γ' ⸴ x' ∶ ρ * A ⊢ (x := x')ρ ∶ (Γ ⸴ x ∶ A) rn⟧=
    C' ⋉ (T ○ f) ⟶ C ⋉ T ∋ f ⋉′ T

⟦liftRn⟧{ρ}{Γ}{Γ'}{A}{x}{x'}{C}{C'}{T}{f} p q₀ q₁ = ⟦∷⟧
  (⟦rnOk⟧ p)
  (⟦∷⟧ (⟦okRn⟧ p) q₁)
  (⟦wkRn⟧ (⟦okRn⟧ p) q₁ p')
  q₀
  q
  where
  e : ∀ y → y ∈ dom Γ → ρ y ≡ (x := x')ρ y
  e y  y∈Γ with x ≐ y
  ... | no _ = refl
  ... | equ = Øelim (∉→¬∈ it y∈Γ)

  p' : ⟦ Γ' ⊢ (x := x')ρ ∶ Γ rn⟧= C' ⟶ C ∋ f
  p' = ⟦rnExt⟧ p e

  q : ⟦ Γ' ⸴ x' ∶ ρ * A ⊢ (x := x')ρ x vr⟧=
    C' ⋉ (T ○ f) ⊩ T ○ f ○ 𝓅₁ ∋ 𝓅₂
  q = subst (λ y → ⟦ Γ' ⸴ x' ∶ ρ * A ⊢ y vr⟧=
    C' ⋉ (T ○ f) ⊩ T ○ f ○ 𝓅₁ ∋ 𝓅₂)
      (symm (:=Eq{f = ρ}{x'} x))
      (⟦new⟧ (⟦okRn⟧ p) q₁)

----------------------------------------------------------------------
-- Determinacy and semantics of renaming expressions
----------------------------------------------------------------------
⟦svCx⟧ :
  {Γ : Cx}
  {C' C : 𝒞𝓍}
  (_ : ⟦ Γ ok⟧= C)
  (_ : ⟦ Γ ok⟧= C')
  → ---------------
  C ≡ C'

⟦svTy⟧ :
  {Γ : Cx}
  {A : Ty}
  {C : 𝒞𝓍}
  {T T' : 𝒯𝓎 C}
  (_ : ⟦ Γ ok⟧= C)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T')
  → -----------------------
  T ≡ T'

⟦svTm⟧ :
  {Γ : Cx}
  {a : Tm}
  {C : 𝒞𝓍}
  {T T' : 𝒯𝓎 C}
  {t : 𝒯𝓂 C T}
  {t' :  𝒯𝓂 C T'}
  (_ : ⟦ Γ ok⟧= C)
  (_ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
  (_ : ⟦ Γ ⊢ a tm⟧= C ⊩ T' ∋ t')
  → ----------------------------
  (T , t) ≡ (T' , t')

⟦rnVr⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {x : 𝔸}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  {T : 𝒯𝓎 C}
  {t : 𝒯𝓂 C T}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ x vr⟧= C ⊩ T ∋ t)
  → ---------------------------------
  ⟦ Γ' ⊢ ρ x vr⟧= C' ⊩ T ○ f ∋ t ○ f

⟦rnTy⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {A : Ty}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  {T : 𝒯𝓎 C}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
  → --------------------------------
  ⟦ Γ' ⊢ ρ * A ty⟧= C' ⊩ T ○ f

⟦rnTm⟧ :
  {ρ : Rn}
  {Γ Γ' : Cx}
  {a : Tm}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  {T : 𝒯𝓎 C}
  {t : 𝒯𝓂 C T}
  (_ : ⟦ Γ' ⊢ ρ ∶ Γ rn⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
  → ----------------------------------
  ⟦ Γ' ⊢ ρ * a tm⟧= C' ⊩ T ○ f ∋ t ○ f

⟦svCx⟧ ⟦◇⟧ ⟦◇⟧ = refl

⟦svCx⟧ (⟦∷⟧ q₀ q₁) (⟦∷⟧ q₀' q₁')
  with refl ← ⟦svCx⟧ q₀ q₀'
  with refl ← ⟦svTy⟧ q₀ q₁ q₁' = refl

⟦svTy⟧ p (⟦𝚷⟧ q₀ q₁ q₂ q₃) (⟦𝚷⟧ q₀' q₁' q₂' q₃')
  with refl ← ⟦svTy⟧ q₀ q₁ q₁' = {!!}

⟦svTy⟧ p (⟦𝚷⟧ q₀ q₁ q₂ q₃) (⟦𝐄𝐥⟧ q₀' q₁') = {!!}

⟦svTy⟧ p (⟦𝐈𝐝⟧ q₀ q q₂ q₃) q' = {!!}

⟦svTy⟧ p (⟦𝐔⟧ q) q' = {!!}

⟦svTy⟧ p (⟦𝐄𝐥⟧ q₀ q₁) q' = {!!}

⟦svTm⟧ p q q' = {!!}

⟦rnVr⟧ p q = {!!}

⟦rnTy⟧ p q  = {!!}

⟦rnTm⟧ p q  = {!!}













-- ⟦rnTy⟧{ρ}{Γ' = Γ'}{C' = C'}{f = f} p
--   (⟦𝚷⟧{A = A}{B}{x}{T = T}{T'} q₀ q₁ q₂ q₃) = ?
--   -- ⟦𝚷⟧{x = x'}
--   --   (⟦rnTy⟧ p q₀)
--   --   (subst (λ B' → ⟦ Γ' ⸴ x' ∶ ρ * A ⊢ B' ty⟧=
--   --      C' ⋉ (T ○ f) ⊩ (T' ○ f ⋉′ T))
--   --      (rnUpdate⟨⟩ ρ x x' B q₂)
--   --      (⟦rnTy⟧ (⟦liftRn⟧ p q₀ (⟦rnTy⟧ p q₀)) q₁))
--   --   x'#
--   -- where
--   -- S = supp (ρ * B , Γ')
--   -- x' = new S
--   -- x'# = ∉∪₁ (new∉ S)
--   -- x'#Γ' = ∉∪₂ (new∉ S)
--   -- instance
--   --   _ : x' # Γ'
--   --   _ = x'#Γ'

-- ⟦rnTy⟧ p (⟦𝐈𝐝⟧ q₀ q₁ q₂ q₃) = ⟦𝐈𝐝⟧
--   ?
--   (⟦rnTy⟧ p q₁)
--   (⟦rnTm⟧ p q₂)
--   (⟦rnTm⟧ p q₃)
-- ⟦rnTy⟧ p (⟦𝐔⟧ _) = ⟦𝐔⟧ (⟦okRn⟧ p)
-- ⟦rnTy⟧ p (⟦𝐄𝐥⟧ q) = ⟦𝐄𝐥⟧ (⟦rnTm⟧ p q)
-- ⟦rnTm⟧ p (⟦𝐯⟧ q) = ⟦𝐯⟧ (⟦rnVr⟧ p q)
-- ⟦rnTm⟧ p (⟦𝚷⟧ q₀ q₁ q₃) = {!!}
-- ⟦rnTm⟧ p (⟦𝛌⟧ q₀ q q₂) = {!!}
-- ⟦rnTm⟧ p (⟦∙⟧ q₀ q₁ q q₂ q₄) = {!!}
-- ⟦rnTm⟧ p (⟦𝐈𝐝⟧ q₀ q₁ q₂) = {!!}
-- ⟦rnTm⟧ p (⟦𝐫𝐞𝐟𝐥⟧ q) = {!!}
-- ⟦rnTm⟧ p (⟦𝐉⟧ q₀ q₁ q q₂ q₄ q₅ q₆b q₇) = {!!}
-- ⟦rnTm⟧ p (⟦𝐍𝐚𝐭⟧ q) = {!!}
-- ⟦rnTm⟧ p (⟦𝐳𝐞𝐫𝐨⟧ q) = {!!}
-- ⟦rnTm⟧ p (⟦𝐬𝐮𝐜𝐜⟧ q) = {!!}
-- ⟦rnTm⟧ p (⟦𝐧𝐫𝐞𝐜⟧ q₀ q q₁ q₂ q₄ q₅) = {!!}

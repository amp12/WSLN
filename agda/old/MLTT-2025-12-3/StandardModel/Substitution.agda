module MLTT.StandardModel.Substitution where

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
open import MLTT.StandardModel.Renaming

----------------------------------------------------------------------
-- Semantics of substitution
----------------------------------------------------------------------
infix 5 ⟦_⊢_∶_sb⟧=_⟶_∋_
data ⟦_⊢_∶_sb⟧=_⟶_∋_ (Γ' : Cx) :
  (_ : Sb)
  (_ : Cx)
  (C' C : 𝒞𝓍)
  (_ : C' → C)
  → ----------
  Set₂
  where
  ⟦◇⟧ :
    {σ : Sb}
    {C' : 𝒞𝓍}
    (q : ⟦ Γ' ok⟧= C')
    → -----------------------------------
    ⟦ Γ' ⊢ σ ∶ ◇ sb⟧= C' ⟶ 𝟙 ∋ (λ _ → tt)
  ⟦∷⟧ :
    {Γ : Cx}
    {σ : Sb}
    {A : Ty}
    {x : 𝔸}
    ⦃ _ : x # Γ ⦄
    {C C' : 𝒞𝓍}
    {T :  𝒯𝓎 C}
    {f : C' → C}
    {t' : 𝒯𝓂 C' (T ○ f)}
    (q₀ : ⟦ Γ ok⟧= C)
    (q₁ : ⟦ Γ' ok⟧= C')
    (q₂ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
    (q₃ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
    (q₄ : ⟦ Γ' ⊢ σ x tm⟧= C' ⊩ T ○ f ∋ t')
    → -------------------------------------------------
    ⟦ Γ' ⊢ σ ∶ (Γ ⸴ x ∶ A) sb⟧= C' ⟶ C ⋉ T ∋ ⟪ f , t' ⟫

-- Well-formed contexts
⟦sbOk⟧ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  → --------------------------------
  ⟦ Γ ok⟧= C

⟦sbOk⟧ (⟦◇⟧ q) = ⟦◇⟧
⟦sbOk⟧ (⟦∷⟧ q _ _ q' _) = ⟦∷⟧ q q'

⟦okSb⟧ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  → --------------------------------
  ⟦ Γ' ok⟧= C'

⟦okSb⟧ (⟦◇⟧ q) = q
⟦okSb⟧ (⟦∷⟧ _ q _ _ _) = q

-- Extensionality
⟦sbExt⟧ :
  {σ σ' : Sb}
  {Γ Γ' : Cx}
  {C C' : 𝒞𝓍}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  (_ : ∀ x → x ∈ dom Γ → σ x ≡ σ' x)
  → --------------------------------
  ⟦ Γ' ⊢ σ' ∶ Γ sb⟧= C' ⟶ C ∋ f

⟦sbExt⟧ (⟦◇⟧ q) _ = ⟦◇⟧ q
⟦sbExt⟧{Γ' = Γ'} (⟦∷⟧{x = x}{C' = C'}{T}{f}{t'} q₀ q₁ q₂ q₃ q₄) e =
  ⟦∷⟧ q₀ q₁ (⟦sbExt⟧ q₂ (λ x r → e x (∈∪₁ r))) q₃
    (subst (λ b → ⟦ Γ' ⊢ b tm⟧= C' ⊩ T ○ f ∋ t') (e x (∈∪₂ ∈｛｝)) q₄)

-- Lifting substitutions
⟦liftSb⟧ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {x x' : 𝔸}
  ⦃ _ : x # Γ ⦄
  ⦃ _ : x' # Γ' ⦄
  {C C' : 𝒞𝓍}
  {T :  𝒯𝓎 C}
  {f : C' → C}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
  (_ : ⟦ Γ' ⊢ σ * A ty⟧= C' ⊩ T ○ f)
  → -------------------------------------------------
  ⟦ Γ' ⸴ x' ∶ σ * A ⊢ (x := 𝐯 x')σ ∶ (Γ ⸴ x ∶ A) sb⟧=
    C' ⋉ (T ○ f) ⟶ C ⋉ T ∋ f ⋉′ T

⟦liftSb⟧ p q₀ q₁ = ⟦∷⟧
  (⟦sbOk⟧ p)
  (⟦∷⟧ (⟦okSb⟧ p) q₁)
  {!!}
  {!!}
  {!!}

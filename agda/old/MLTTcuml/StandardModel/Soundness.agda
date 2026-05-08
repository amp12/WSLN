module MLTT.StandardModel.Soundness where

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
open import MLTT.StandardModel.Substitution







⟦sbTy⟧ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {A : Ty}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  {T : 𝒯𝓎 C}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ A ty⟧= C ⊩ T)
  → --------------------------------
  ⟦ Γ' ⊢ σ * A ty⟧= C' ⊩ T ○ f

⟦sbTm⟧ :
  {σ : Sb}
  {Γ Γ' : Cx}
  {a : Tm}
  {C' C : 𝒞𝓍}
  {f : C' → C}
  {T : 𝒯𝓎 C}
  {t : 𝒯𝓂 C T}
  (_ : ⟦ Γ' ⊢ σ ∶ Γ sb⟧= C' ⟶ C ∋ f)
  (_ : ⟦ Γ ⊢ a tm⟧= C ⊩ T ∋ t)
  → ----------------------------------
  ⟦ Γ' ⊢ σ * a tm⟧= C' ⊩ T ○ f ∋ t ○ f

⟦sbTy⟧ {σ}{Γ' = Γ'}{C' = C'}{f = f} p
  (⟦𝚷⟧{A = A}{B}{x}{T = T}{T'} q₀ q₁ q₂)
  with (x' , x'# ∉∪ x'#Γ') ← fresh (σ * B , Γ') =
  ⟦𝚷⟧{x = x'}
    (⟦sbTy⟧ p q₀)
    (subst (λ B' → ⟦ Γ' ⸴ x' ∶ σ * A ⊢ B' ty⟧=
       C' ⋉ (T ○ f) ⊩ (T' ○ f ⋉′ T))
       (sbUpdate⟨⟩ σ x (𝐯 x') B q₂)
       (⟦sbTy⟧ (⟦liftSb⟧ p q₀ (⟦sbTy⟧ p q₀)) q₁))
    x'#
  where
  instance
    _ : x' # Γ'
    _ = x'#Γ'

⟦sbTy⟧ p (⟦𝐈𝐝⟧ q₀ q₁ q₂) = {!!}
⟦sbTy⟧ p (⟦𝐔⟧ q) = {!!}
⟦sbTy⟧ p (⟦𝐄𝐥⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝐯⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝚷⟧ q₀ q₁ q₃) = {!!}
⟦sbTm⟧ p (⟦𝛌⟧ q₀ q q₂) = {!!}
⟦sbTm⟧ p (⟦∙⟧ q₀ q₁ q q₂ q₄) = {!!}
⟦sbTm⟧ p (⟦𝐈𝐝⟧ q₀ q₁ q₂) = {!!}
⟦sbTm⟧ p (⟦𝐫𝐞𝐟𝐥⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝐉⟧ q₀ q₁ q q₂ q₄ q₅) = {!!}
⟦sbTm⟧ p (⟦𝐍𝐚𝐭⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝐳𝐞𝐫𝐨⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝐬𝐮𝐜𝐜⟧ q) = {!!}
⟦sbTm⟧ p (⟦𝐧𝐫𝐞𝐜⟧ q₀ q q₁ q₂ q₄ q₅) = {!!}

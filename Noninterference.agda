module Noninterference where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; subst; cong; sym)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import Erasure

open import TypeSafety
open import BigStep
open import BigStepErased
open import BigStepPreservation
open import BigStepSimulation
open import BigStepErasedDeterministic

{- Lemma -}
bool-low-erase-eq : ∀ {Σ₁ Σ₂ V₁ V₂}
  → [] ; Σ₁ ; l low ; low ⊢ V₁ ⦂ ` Bool of l low
  → [] ; Σ₂ ; l low ; low ⊢ V₂ ⦂ ` Bool of l low
  → Value V₁ → Value V₂
  → erase V₁ ≡ erase V₂
    ----------------------------------------
  → V₁ ≡ V₂
bool-low-erase-eq ⊢V₁ ⊢V₂ v₁ v₂ eq =
  case canonical-const ⊢V₁ v₁ of λ where
  (Const-base l≼l) →
    case canonical-const ⊢V₂ v₂ of λ where
    (Const-base l≼l) →
      case eq of λ where refl → refl

noninterference : ∀ {μ₁ μ₂ M V₁ V₂} {b₁ b₂ : rep Bool}
  → ` Bool of l high ∷ [] ; ∅ ; l low ; low ⊢ M ⦂ ` Bool of l low
  → ∅ ∣ low ⊢ M [ $ b₁ of high ] ⇓ V₁ ∣ μ₁
  → ∅ ∣ low ⊢ M [ $ b₂ of high ] ⇓ V₂ ∣ μ₂
    ---------------------------------------------
  → V₁ ≡ V₂
noninterference {M = M} {V₁} {V₂} {b₁} {b₂} ⊢M M[b₁]⇓V₁ M[b₂]⇓V₂ =
  let ϵM[●]⇓ϵV₁ = subst (λ □ → _ ∣ _ ⊢ □ ⇓ₑ _ ∣ _) (substitution-erase M ($ b₁ of high))
                          (sim (substitution-pres ⊢M ⊢const) ⊢μ-nil ≾-refl M[b₁]⇓V₁)
      ϵM[●]⇓ϵV₂ = subst (λ □ → _ ∣ _ ⊢ □ ⇓ₑ _ ∣ _) (substitution-erase M ($ b₂ of high))
                          (sim (substitution-pres ⊢M ⊢const) ⊢μ-nil ≾-refl M[b₂]⇓V₂)
      ⟨ ϵV₁≡ϵV₂ , ϵμ₁≡ϵμ₂ ⟩ = ⇓ₑ-deterministic ϵM[●]⇓ϵV₁ ϵM[●]⇓ϵV₂ in
  let ⟨ _ , _ , ⊢V₁ , _ ⟩ = ⇓-preserve (substitution-pres ⊢M ⊢const) ⊢μ-nil ≾-refl M[b₁]⇓V₁ in
  let ⟨ _ , _ , ⊢V₂ , _ ⟩ = ⇓-preserve (substitution-pres ⊢M ⊢const) ⊢μ-nil ≾-refl M[b₂]⇓V₂ in
    bool-low-erase-eq ⊢V₁ ⊢V₂ (⇓-value M[b₁]⇓V₁) (⇓-value M[b₂]⇓V₂) ϵV₁≡ϵV₂

module Dyn.Noninterference where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; subst; cong; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.Types using (Base; Bool; rep)
open import Dyn.Syntax
open import Dyn.Values
open import Dyn.Erasure
open import Dyn.BigStep
open import Dyn.BigStepErased
open import Dyn.BigStepSimulation
open import Dyn.BigStepErasedDeterministic
open import Dyn.HeapSecure using (∅-sec)


noninterference : ∀ {μ₁ μ₂ M} {b₁ b₂ b₃ b₄ : rep Bool}
  → ∅ ∣ low ⊢ M [ $ b₁ of high ] ⇓ $ b₃ of low ∣ μ₁
  → ∅ ∣ low ⊢ M [ $ b₂ of high ] ⇓ $ b₄ of low ∣ μ₂
    ---------------------------------------------
  → b₃ ≡ b₄
noninterference {M = M} {b₁} {b₂} {b₃} {b₄} M[b₁]⇓b₃ M[b₂]⇓b₄ =
  let ϵM[●]⇓ϵb₃ = subst (λ □ → _ ∣ _ ⊢ □ ⇓ₑ _ ∣ _) (substitution-erase M ($ b₁ of high))
                          (sim ∅-sec M[b₁]⇓b₃)
      ϵM[●]⇓ϵb₄ = subst (λ □ → _ ∣ _ ⊢ □ ⇓ₑ _ ∣ _) (substitution-erase M ($ b₂ of high))
                          (sim ∅-sec M[b₂]⇓b₄) in
      case ⇓ₑ-deterministic ϵM[●]⇓ϵb₃ ϵM[●]⇓ϵb₄ of λ where
      ⟨ refl , _ ⟩ → refl

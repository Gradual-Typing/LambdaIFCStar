module BigStepErasedDeterministic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC

open import BigStepErased

⇓ₑ-deterministic : ∀ {M μ μ₁ μ₂ pc} {V₁ V₂}
  → μ ∣ pc ⊢ M ⇓ₑ V₁ ∣ μ₁
  → μ ∣ pc ⊢ M ⇓ₑ V₂ ∣ μ₂
    -------------------------------------
  → V₁ ≡ V₂ × μ₁ ≡ μ₂
⇓ₑ-deterministic (⇓ₑ-val _) (⇓ₑ-val _) = ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-app L⇓ƛN M⇓V N[V]⇓W) (⇓ₑ-app L⇓ƛN† M⇓V† N[V]⇓W†) =
  case ⇓ₑ-deterministic L⇓ƛN L⇓ƛN† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ →
      case ⇓ₑ-deterministic N[V]⇓W N[V]⇓W† of λ where
      ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-app L⇓ƛN _ _) (⇓ₑ-app-● L⇓● _) =
  contradiction (⇓ₑ-deterministic L⇓ƛN L⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-app-● L⇓● _) (⇓ₑ-app L⇓ƛN _ _) =
  contradiction (⇓ₑ-deterministic L⇓● L⇓ƛN) (λ ())
⇓ₑ-deterministic (⇓ₑ-app-● L⇓● M⇓V) (⇓ₑ-app-● L⇓●† M⇓V†) =
  case ⇓ₑ-deterministic L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-if-true L⇓true M⇓V) (⇓ₑ-if-true L⇓true† M⇓V†) =
  case ⇓ₑ-deterministic L⇓true L⇓true† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-if-true L⇓true _) (⇓ₑ-if-false L⇓false _) =
  contradiction (⇓ₑ-deterministic L⇓true L⇓false) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-true L⇓true _) (⇓ₑ-if-● L⇓●) =
  contradiction (⇓ₑ-deterministic L⇓true L⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-false L⇓false N⇓V) (⇓ₑ-if-false L⇓false† N⇓V†) =
  case ⇓ₑ-deterministic L⇓false L⇓false† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic N⇓V N⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-if-false L⇓false _) (⇓ₑ-if-true L⇓true _) =
  contradiction (⇓ₑ-deterministic L⇓false L⇓true) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-false L⇓false _) (⇓ₑ-if-● L⇓●) =
  contradiction (⇓ₑ-deterministic L⇓false L⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-● L⇓●) (⇓ₑ-if-true L⇓true _) =
  contradiction (⇓ₑ-deterministic L⇓● L⇓true ) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-● L⇓●) (⇓ₑ-if-false L⇓false _) =
  contradiction (⇓ₑ-deterministic L⇓● L⇓false) (λ ())
⇓ₑ-deterministic (⇓ₑ-if-● L⇓●) (⇓ₑ-if-● L⇓●†) =
  case ⇓ₑ-deterministic L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-let M⇓V N[V]⇓W) (⇓ₑ-let M⇓V† N[V]⇓W†) =
  case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic N[V]⇓W N[V]⇓W† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-ref? M⇓V fresh _) (⇓ₑ-ref? M⇓V† fresh† _) =
  case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case trans fresh (sym fresh†) of λ where
      refl → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-ref?-● M⇓V) (⇓ₑ-ref?-● M⇓V†) =
  case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-ref M⇓V fresh) (⇓ₑ-ref M⇓V† fresh†) =
  case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case trans fresh (sym fresh†) of λ where
      refl → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-ref-● M⇓V) (⇓ₑ-ref-● M⇓V†) =
  case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-deref M⇓a eq) (⇓ₑ-deref M⇓a† eq†) =
  case ⇓ₑ-deterministic M⇓a M⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case trans (sym eq) eq† of λ where
    refl → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-deref M⇓a _) (⇓ₑ-deref-● M⇓●) =
  contradiction (⇓ₑ-deterministic M⇓a M⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-deref-● M⇓●) (⇓ₑ-deref M⇓a _) =
  contradiction (⇓ₑ-deterministic M⇓● M⇓a) (λ ())
⇓ₑ-deterministic (⇓ₑ-deref-● M⇓●) (⇓ₑ-deref-● M⇓●†) =
  case ⇓ₑ-deterministic M⇓● M⇓●† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-assign? L⇓a M⇓V _) (⇓ₑ-assign? L⇓a† M⇓V† _) =
  case ⇓ₑ-deterministic L⇓a L⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-assign? L⇓a _ _) (⇓ₑ-assign?-● L⇓● _) =
  contradiction (⇓ₑ-deterministic L⇓a L⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-assign?-● L⇓● _) (⇓ₑ-assign? L⇓a _ _) =
  contradiction (⇓ₑ-deterministic L⇓● L⇓a) (λ ())
⇓ₑ-deterministic (⇓ₑ-assign?-● L⇓● M⇓V) (⇓ₑ-assign?-● L⇓●† M⇓V†) =
  case ⇓ₑ-deterministic L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-assign L⇓a M⇓V) (⇓ₑ-assign L⇓a† M⇓V†) =
  case ⇓ₑ-deterministic L⇓a L⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
⇓ₑ-deterministic (⇓ₑ-assign L⇓a _) (⇓ₑ-assign-● L⇓● _) =
  contradiction (⇓ₑ-deterministic L⇓a L⇓●) (λ ())
⇓ₑ-deterministic (⇓ₑ-assign-● L⇓● _) (⇓ₑ-assign L⇓a _) =
  contradiction (⇓ₑ-deterministic L⇓● L⇓a) (λ ())
⇓ₑ-deterministic (⇓ₑ-assign-● L⇓● M⇓V) (⇓ₑ-assign-● L⇓●† M⇓V†) =
  case ⇓ₑ-deterministic L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case ⇓ₑ-deterministic M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩

{- Evaluation contexts -}

module CC2.Frame where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function using (case_of_)

open import Common.Types
open import Common.BlameLabels
open import CC2.CCStatics


data Frame : Set where

  app?□ : Term → BlameLabel → Frame
  app✓□ : Term → Frame
  app✓_□ : (V : Term) → Value V → Frame

  ref✓⟦_⟧□ : StaticLabel → Frame

  !□ : Frame

  assign?□ : Term → BlameLabel → Frame
  assign✓□ : Term → Frame
  assign✓_□ : (V : Term) → Value V → Frame

  let□_ : Term → Frame

  if□ : Type → Term → Term → Frame
  if⋆□ : Type → Term → Term → Frame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → Frame




plug : Term → Frame → Term
plug L (app?□ M p)           = app? L M p
plug L (app✓□ M)            = app✓ L M
plug M ((app✓ V □) v)       = app✓ V M
plug M (ref✓⟦ ℓ ⟧□)         = ref✓⟦ ℓ ⟧ M
plug M !□                    = ! M
plug L (assign?□ M p)        = assign? L M p
plug L (assign✓□ M)         = assign✓ L M
plug M ((assign✓ V □) v)    = assign✓ V M
plug M (let□ N)              = `let M N
plug L (if□ A M N)           = if L A M N
plug L (if⋆□ A M N)          = if⋆ L A M N
plug M □⟨ c ⟩                = M ⟨ c ⟩

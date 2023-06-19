{- Evaluation contexts -}

module CC2.Frame where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function using (case_of_)

open import CC2.Statics


data Frame : Set where

  -- app  L M A B ℓ
  app□   : (M : Term) → (A B : Type) → StaticLabel → Frame
  app_□  : (V : Term) → Value V → (A B : Type) → StaticLabel → Frame
  -- app! L M A B g
  app!□  : (M : Term) → (A B : Type) → Label → Frame
  app!_□ : (V : Term) → Value V → (A B : Type) → Label → Frame

  -- ref⟦ ℓ ⟧ M
  ref⟦_⟧□ : StaticLabel → Frame
  -- ref?⟦ ℓ ⟧ M p
  ref?⟦_⟧□ : StaticLabel → BlameLabel → Frame

  -- ! M A g
  !□ : Type → Label → Frame

  -- assign L M T ℓ̂ ℓ
  assign□   : (M : Term) → RawType → (ℓ̂ ℓ : StaticLabel) → Frame
  assign_□  : (V : Term) → Value V → RawType → (ℓ̂ ℓ : StaticLabel) → Frame
  -- assign? L M T ĝ g p
  assign?□  : (M : Term) → RawType → (ĝ g : Label) → BlameLabel → Frame
  assign?_□ : (V : Term) → Value V → RawType → (ĝ g : Label) → BlameLabel → Frame

  -- let M A N
  let□ : Type → Term → Frame

  -- if  L A ℓ M N
  if□  : Type → StaticLabel → (M N : Term) → Frame
  -- if! L A g M N
  if!□ : Type → Label → (M N : Term) → Frame

  -- M ⟨ c ⟩
  □⟨_⟩ : ∀ {A B} → (c : Cast A ⇒ B) → Frame


plug : Term → Frame → Term
plug L (app□ M A B ℓ)          = app  L M A B ℓ
plug M (app V □ v A B ℓ)       = app  V M A B ℓ
plug L (app!□ M A B g)         = app! L M A B g
plug M (app! V □ v A B g)      = app! V M A B g
plug M (ref⟦ ℓ ⟧□)             = ref⟦ ℓ ⟧ M
plug M (ref?⟦ ℓ ⟧□ p)          = ref?⟦ ℓ ⟧ M p
plug M (!□ A g)                = ! M A g
plug L (assign□ M T ℓ̂ ℓ)       = assign L M T ℓ̂ ℓ
plug M (assign V □ v T ℓ̂ ℓ)    = assign V M T ℓ̂ ℓ
plug L (assign?□ M T ĝ g p)    = assign? L M T ĝ g p
plug M (assign? V □ v T ĝ g p) = assign? V M T ĝ g p
plug M (let□ A N)              = `let M A N
plug L (if□  A ℓ M N)          = if  L A ℓ M N
plug L (if!□ A g M N)          = if! L A g M N
plug M □⟨ c ⟩                  = M ⟨ c ⟩

{- Evaluation contexts -}

module CC2.Frame where

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function using (case_of_)

open import CC2.Statics


data Frame : Set where

  -- app  L M A B ℓ
  app□   : (M : Term) → (A B : Type) → StaticLabel → Frame
  app_□  : (V : Term) → Value V → (A B : Type) → StaticLabel → Frame
  -- app⋆ L M A T
  app⋆□  : (M : Term) → (A : Type) → (T : RawType) → Frame
  app⋆_□ : (V : Term) → Value V → (A : Type) → (T : RawType) → Frame

  -- ref⟦ ℓ ⟧ M
  ref⟦_⟧□ : StaticLabel → Frame
  -- ref?⟦ ℓ ⟧ M p
  ref?⟦_⟧□ : StaticLabel → BlameLabel → Frame

  -- ! M A ℓ
  !□ : Type → StaticLabel → Frame
  -- !⋆ M T
  !⋆□ : RawType → Frame

  -- assign  L M T ℓ̂ ℓ
  assign□   : (M : Term) → RawType → (ℓ̂ ℓ : StaticLabel) → Frame
  assign_□  : (V : Term) → Value V → RawType → (ℓ̂ ℓ : StaticLabel) → Frame
  -- assign? L M T ĝ p
  assign?□  : (M : Term) → RawType → (ĝ : Label) → BlameLabel → Frame
  assign?_□ : (V : Term) → Value V → RawType → (ĝ : Label) → BlameLabel → Frame

  -- let M A N
  let□ : Type → Term → Frame

  -- if  L A ℓ M N
  if□  : Type → StaticLabel → (M N : Term) → Frame
  -- if⋆ L T M N
  if⋆□ : RawType → (M N : Term) → Frame

  -- M ⟨ c ⟩
  □⟨_⟩ : ∀ {A B} → (c : Cast A ⇒ B) → Frame


plug : Term → Frame → Term
plug L (app□ M A B ℓ)          = app  L M A B ℓ
plug M (app V □ v A B ℓ)       = app  V M A B ℓ
plug L (app⋆□ M A T)           = app⋆ L M A T
plug M (app⋆ V □ v A T)        = app⋆ V M A T
plug M (ref⟦ ℓ ⟧□)             = ref⟦ ℓ ⟧ M
plug M (ref?⟦ ℓ ⟧□ p)          = ref?⟦ ℓ ⟧ M p
plug M (!□ A ℓ)                = ! M A ℓ
plug M (!⋆□ T)                 = !⋆ M T
plug L (assign□ M T ℓ̂ ℓ)       = assign L M T ℓ̂ ℓ
plug M (assign V □ v T ℓ̂ ℓ)    = assign V M T ℓ̂ ℓ
plug L (assign?□ M    T ĝ p)   = assign? L M T ĝ p
plug M (assign? V □ v T ĝ p)   = assign? V M T ĝ p
plug M (let□ A N)              = `let M A N
plug L (if□  A ℓ M N)          = if  L A ℓ M N
plug L (if⋆□ T M N)            = if⋆ L T M N
plug M □⟨ c ⟩                  = M ⟨ c ⟩


plug-not-● : ∀ {M} → (F : Frame) → ¬ (plug M F ≡ ●)
plug-not-● (app□ M A B x) ()
plug-not-● (app V □ x A B x₁) ()
plug-not-● (app⋆□ M A B) ()
plug-not-● (app⋆ V □ x A B) ()
plug-not-● ref⟦ ℓ ⟧□ ()
plug-not-● (ref?⟦ ℓ ⟧□ x₁) ()
plug-not-● (!□ x x₁) ()
plug-not-● (!⋆□ x) ()
plug-not-● (assign□ M x ℓ̂ ℓ) ()
plug-not-● (assign V □ x x₁ ℓ̂ ℓ) ()
plug-not-● (assign?□ M x ĝ x₁) ()
plug-not-● (assign? V □ x x₁ ĝ x₂) ()
plug-not-● (let□ x x₁) ()
plug-not-● (if□ x x₁ M N) ()
plug-not-● (if⋆□ x M N) ()
plug-not-● □⟨ c ⟩ ()

plug-not-bl : ∀ {M p} → (F : Frame) → ¬ (plug M F ≡ blame p)
plug-not-bl (app□ M A B x) ()
plug-not-bl (app V □ x A B x₁) ()
plug-not-bl (app⋆□ M A B) ()
plug-not-bl (app⋆ V □ x A B) ()
plug-not-bl ref⟦ ℓ ⟧□ ()
plug-not-bl (ref?⟦ ℓ ⟧□ x₁) ()
plug-not-bl (!□ x x₁) ()
plug-not-bl (!⋆□ x) ()
plug-not-bl (assign□ M x ℓ̂ ℓ) ()
plug-not-bl (assign V □ x x₁ ℓ̂ ℓ) ()
plug-not-bl (assign?□ M x ĝ x₁) ()
plug-not-bl (assign? V □ x x₁ ĝ x₂) ()
plug-not-bl (let□ x x₁) ()
plug-not-bl (if□ x x₁ M N) ()
plug-not-bl (if⋆□ x M N) ()
plug-not-bl □⟨ c ⟩ ()

plug-not-raw : ∀ {M} → (F : Frame) → ¬ RawValue (plug M F)
plug-not-raw (app□ M A B x) ()
plug-not-raw (app V □ x A B x₁) ()
plug-not-raw (app⋆□ M A B) ()
plug-not-raw (app⋆ V □ x A B) ()
plug-not-raw ref⟦ ℓ ⟧□ ()
plug-not-raw (ref?⟦ ℓ ⟧□ x₁) ()
plug-not-raw (!□ x x₁) ()
plug-not-raw (!⋆□ x) ()
plug-not-raw (assign□ M x ℓ̂ ℓ) ()
plug-not-raw (assign V □ x x₁ ℓ̂ ℓ) ()
plug-not-raw (assign?□ M x ĝ x₁) ()
plug-not-raw (assign? V □ x x₁ ĝ x₂) ()
plug-not-raw (let□ x x₁) ()
plug-not-raw (if□ x x₁ M N) ()
plug-not-raw (if⋆□ x M N) ()
plug-not-raw □⟨ c ⟩ ()

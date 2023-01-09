{- The precision relation of CC is decidable -}

module CCExpSub.PrecisionDecidable where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Common.Utils
open import Common.Types
open import Memory.HeapContext
open import CCExpSub.Statics
open import CCExpSub.Precision
open import CCExpSub.Uniqueness

open import CCExpSub.PrecisionDecidable.Const


cc-⊑? : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′} M M′
  → Γ  ; Σ  ; gc  ; pc  ⊢ M  ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    ---------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′)

cc-⊑?-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′ B M M′} {c : Cast A ⇒ B}
  → Γ  ; Σ  ; gc  ; pc  ⊢ M ⟨ c ⟩ ⦂ B
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    ----------------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⟨ c ⟩ ⊑ M′)
cc-⊑?-cast {gc = gc} {gc′} {pc} {pc′} {A} {A′} {B} {M} {M′} (⊢cast ⊢M) ⊢const =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? {gc = gc} {gc′} {pc} {pc′} M M′ ⊢M ⊢const of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ gc′ , pc′ , ⊢const ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′ ⟩ _) →
        case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ ⊢const of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′ ⟩ _) →
      case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ ⊢const of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {gc = gc} {gc′} {pc} {pc′} {A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢addr eq) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? {gc = gc} {gc′} {pc} {pc′} M M′ ⊢M (⊢addr eq) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ gc′ , pc′ , ⊢addr eq ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′ ⟩ _) →
        case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ (⊢addr eq) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′ ⟩ _) →
      case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ (⊢addr eq) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {gc = gc} {gc′} {pc} {pc′} {A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢var ∋x) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? {gc = gc} {gc′} {pc} {pc′} M M′ ⊢M (⊢var ∋x) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ gc′ , pc′ , ⊢var ∋x ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′ ⟩ _) →
        case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ (⊢var ∋x) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′ ⟩ _) →
      case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′ (⊢var ∋x) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {gc = gc} {gc′} {pc} {pc′} {A} {A′} {B} (⊢cast ⊢M) (⊢lam ⊢N′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? {gc = gc} {gc′} {pc} {pc′} _ _ ⊢M (⊢lam ⊢N′) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ gc′ , pc′ , ⊢lam ⊢N′ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′† (⊢lam ⊢N′) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness {gc† = gc′} {pc† = pc′} ⊢M′† (⊢lam ⊢N′) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢app ⊢L′ ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? M M′ ⊢M (⊢app ⊢L′ ⊢M′) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢app ⊢L′ ⊢M′ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢app ⊢L′ ⊢M′) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢app ⊢L′ ⊢M′) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢if ⊢L′ ⊢M′ ⊢N′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? _ _ ⊢M (⊢if ⊢L′ ⊢M′ ⊢N′) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢if ⊢L′ ⊢M′ ⊢N′ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢if ⊢L′ ⊢M′ ⊢N′) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢if ⊢L′ ⊢M′ ⊢N′) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢let ⊢M′ ⊢N′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? _ _ ⊢M (⊢let ⊢M′ ⊢N′) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢let ⊢M′ ⊢N′ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢let ⊢M′ ⊢N′) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢let ⊢M′ ⊢N′) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢ref ⊢M′ pc′≼ℓ) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? _ _ ⊢M (⊢ref ⊢M′ pc′≼ℓ) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢ref ⊢M′ pc′≼ℓ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢ref ⊢M′ pc′≼ℓ) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢ref ⊢M′ pc′≼ℓ) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢ref? ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? _ _ ⊢M (⊢ref? ⊢M′) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢ref? ⊢M′ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢ref? ⊢M′) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢ref? ⊢M′) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast {A = A} {A′} {B} {M} {M′} (⊢cast ⊢M) (⊢ref✓ ⊢M′ pc≼ℓ) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? _ _ ⊢M (⊢ref✓ ⊢M′ pc≼ℓ) of λ where
      (yes M⊑M′) → yes (⊑-castₗ A⊑A′ B⊑A′ ⟨ _ , _ , ⊢ref✓ ⊢M′ pc≼ℓ ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castₗ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) →
      no λ { (⊑-castₗ _ B⊑A′ ⟨ _ , _ , ⊢M′† ⟩ _) →
        case uniqueness ⊢M′† (⊢ref✓ ⊢M′ pc≼ℓ) of λ where
        refl → contradiction B⊑A′ B⋤A′ }
  (no  A⋤A′) →
    no λ { (⊑-castₗ A⊑A′ _ ⟨ _ , _ , ⊢M′† ⟩ _) →
      case uniqueness ⊢M′† (⊢ref✓ ⊢M′ pc≼ℓ) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-cast (⊢cast ⊢M) (⊢deref ⊢M′) = {!!}
cc-⊑?-cast (⊢cast ⊢M) (⊢assign ⊢M′ ⊢M′₁ x) = {!!}
cc-⊑?-cast (⊢cast ⊢M) (⊢assign? ⊢M′ x) = {!!}
cc-⊑?-cast (⊢cast ⊢M) (⊢assign✓ ⊢M′ ⊢M′₁ x) = {!!}
cc-⊑?-cast (⊢cast ⊢M) (⊢prot ⊢M′) = {!!}
cc-⊑?-cast (⊢cast {A = A} {B} ⊢M) (⊢cast {A = A′} {B′} ⊢M′) =
  case B ⊑? B′ of λ where
  (yes B⊑B′) →
    case A ⊑? A′ of λ where
    (yes A⊑A′) →
      case cc-⊑? _ _ ⊢M ⊢M′ of λ where
      (yes M⊑M′) → yes (⊑-cast A⊑A′ B⊑B′ M⊑M′)
      (no  M⋤M′) → {!!}
    (no  A⋤A′) → {!!}
  (no  B⋤B′) →
    no λ {
      (⊑-cast A⊑A′ B⊑B′ M⊑M′)    → contradiction B⊑B′ B⋤B′ ;
      (⊑-castₗ _ B⊑B′ ⟨ _ , _ , ⊢M† ⟩ _) →
        case cast-wt-inv ⊢M† of λ { ⟨ refl , _ ⟩ → contradiction B⊑B′ B⋤B′ } ;
      (⊑-castᵣ _ B⊑B′ ⟨ _ , _ , ⊢M† ⟩ _) →
        case cast-wt-inv ⊢M† of λ { ⟨ refl , _ ⟩ → contradiction B⊑B′ B⋤B′ } }
cc-⊑?-cast (⊢cast ⊢M) (⊢cast-pc ⊢M′ x) = {!!}
cc-⊑?-cast (⊢cast ⊢M) (⊢sub ⊢M′) = {!!}
cc-⊑?-cast (⊢cast ⊢M) ⊢err = {!!}
cc-⊑?-cast ⊢M (⊢sub-pc ⊢M′ x) = cc-⊑?-cast ⊢M ⊢M′
cc-⊑?-cast (⊢sub-pc ⊢M gc<:gc′) ⊢M′ = cc-⊑?-cast ⊢M ⊢M′

cc-⊑?-app : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′ L M M′}
  → Γ  ; Σ  ; gc  ; pc  ⊢ L · M ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    ----------------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L · M ⊑ M′)
cc-⊑?-app (⊢app ⊢L ⊢M) ⊢const            = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢addr _)         = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢var _)          = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢lam _)          = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢app ⊢L′ ⊢M′)    =
  case cc-⊑? _ _ ⊢L ⊢L′ of λ where
  (yes L⊑L′) →
    case cc-⊑? _ _ ⊢M ⊢M′ of λ where
    (yes M⊑M′) → yes (⊑-app L⊑L′ M⊑M′)
    (no  M⋤M′) → no (λ { (⊑-app _ M⊑M′) → contradiction M⊑M′ M⋤M′ })
  (no  L⋤L′) → no (λ { (⊑-app L⊑L′ _) → contradiction L⊑L′ L⋤L′ })
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢if _ _ _)       = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢let _ _)        = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢ref _ _)        = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢ref? _)         = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢ref✓ _ _)      = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢deref _)        = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢assign _ _ _)   = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢assign? _ _)    = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢assign✓ _ _ _) = no λ ()
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢prot _)         = no λ ()
cc-⊑?-app {A = A} (⊢app ⊢L ⊢M) (⊢cast {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑?-app (⊢app ⊢L ⊢M) ⊢M′ of λ where
      (yes M⊑M′) →
        yes (⊑-castᵣ A⊑A′ A⊑B′ ⟨ _ , _ , ⊢app ⊢L ⊢M ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castᵣ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  A⋤B′) →
      no λ { (⊑-castᵣ _ A⊑B′ ⟨ _ , _ , ⊢M† ⟩ _) →
        case uniqueness ⊢M† (⊢app ⊢L ⊢M) of λ where
        refl → contradiction A⊑B′ A⋤B′ }
  (no  A⋤A′) →
    no λ { (⊑-castᵣ A⊑A′ _ ⟨ _ , _ , ⊢M† ⟩ _) →
      case uniqueness ⊢M† (⊢app ⊢L ⊢M) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢cast-pc {g = g} ⊢M′ _) =
  case cc-⊑?-app (⊢app ⊢L ⊢M) ⊢M′ of λ where
  (yes M⊑M′) → yes (⊑-cast-pcᵣ M⊑M′)
  (no  M⋤M′) → no (λ { (⊑-cast-pcᵣ M⊑M′) → contradiction M⊑M′ M⋤M′ })
cc-⊑?-app {A = A} (⊢app ⊢L ⊢M) (⊢sub {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑?-app (⊢app ⊢L ⊢M) ⊢M′ of λ where
      (yes M⊑M′) →
        yes (⊑-subᵣ A⊑A′ A⊑B′ ⟨ _ , _ , ⊢app ⊢L ⊢M ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-subᵣ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  A⋤B′) →
      no λ { (⊑-subᵣ _ A⊑B′ ⟨ _ , _ , ⊢M† ⟩ _) →
        case uniqueness ⊢M† (⊢app ⊢L ⊢M) of λ where
        refl → contradiction A⊑B′ A⋤B′ }
  (no  A⋤A′) →
    no λ { (⊑-subᵣ A⊑A′ _ ⟨ _ , _ , ⊢M† ⟩ _) →
      case uniqueness ⊢M† (⊢app ⊢L ⊢M) of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-app (⊢app ⊢L ⊢M) (⊢sub-pc ⊢M′ x) = cc-⊑?-app (⊢app ⊢L ⊢M) ⊢M′
cc-⊑?-app {A = A} (⊢app ⊢L ⊢M) (⊢err {A = A′}) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) → yes (⊑-err ⟨ _ , _ , ⊢app ⊢L ⊢M ⟩ A⊑A′)
  (no  A⋤A′) →
    no (λ { (⊑-err ⟨ _ , _ , ⊢M† ⟩ A⊑A′) →
      case uniqueness ⊢M† (⊢app ⊢L ⊢M) of λ where
      refl → contradiction A⊑A′ A⋤A′ })
cc-⊑?-app (⊢sub-pc ⊢M gc<:gc′) ⊢M′ = cc-⊑?-app ⊢M ⊢M′


cc-⊑? (` x) M′ ⊢M ⊢M′ = {!!}
cc-⊑? ($ k of ℓ) M ⊢M ⊢M′ = cc-⊑?-const ⊢M ⊢M′
cc-⊑? (addr a of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ƛ⟦ pc ⟧ A ˙ N of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L · M) M′ ⊢M ⊢M′ = cc-⊑?-app ⊢M ⊢M′
cc-⊑? (if L A M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (`let M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref?⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref✓⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (! M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L := M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=? M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=✓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (M ⟨ c ⟩) M′ ⊢M ⊢M′ =
  case cast-wt-inv ⊢M of λ where
  ⟨ refl , _ ⟩ → cc-⊑?-cast ⊢M ⊢M′
cc-⊑? (M ↟⟨ c ⟩) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (prot ℓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (cast-pc g M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (error A e) M′ ⊢M ⊢M′ = {!!}
cc-⊑? ● M′ ⊢M ⊢M′ = {!!}

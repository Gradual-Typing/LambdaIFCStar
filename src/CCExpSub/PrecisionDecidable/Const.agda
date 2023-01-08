module CCExpSub.PrecisionDecidable.Const where

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


cc-⊑?-const : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′ M′ ι} {k : rep ι} {ℓ}
  → Γ ; Σ ; gc ; pc ⊢ $ k of ℓ ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    ----------------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ $ k of ℓ ⊑ M′)
cc-⊑?-const (⊢const {ι = ι} {k} {ℓ}) (⊢const {ι = ι′} {k′} {ℓ′}) =
  case (` ι) ≡ᵣ? (` ι′) of λ where
  (yes refl) →
    case const-eq? k k′ of λ where
    (yes refl) →
      case ℓ =? ℓ′ of λ where
      (yes refl) → yes ⊑-const
      (no  ℓ≢ℓ)  → no λ { ⊑-const → contradiction refl ℓ≢ℓ }
    (no  k≢k)    → no λ { ⊑-const → contradiction refl k≢k }
  (no  ι≢ι)      → no λ { ⊑-const → contradiction refl ι≢ι }
cc-⊑?-const ⊢const (⊢addr _)         = no λ ()
cc-⊑?-const ⊢const (⊢var _)          = no λ ()
cc-⊑?-const ⊢const (⊢lam _)          = no λ ()
cc-⊑?-const ⊢const (⊢app _ _)        = no λ ()
cc-⊑?-const ⊢const (⊢if _ _ _)       = no λ ()
cc-⊑?-const ⊢const (⊢let _ _)        = no λ ()
cc-⊑?-const ⊢const (⊢ref _ _)        = no λ ()
cc-⊑?-const ⊢const (⊢ref? _)         = no λ ()
cc-⊑?-const ⊢const (⊢ref✓ _ _)      = no λ ()
cc-⊑?-const ⊢const (⊢deref _)        = no λ ()
cc-⊑?-const ⊢const (⊢assign _ _ _)   = no λ ()
cc-⊑?-const ⊢const (⊢assign? _ _)    = no λ ()
cc-⊑?-const ⊢const (⊢assign✓ _ _ _) = no λ ()
cc-⊑?-const ⊢const (⊢prot _)         = no λ ()
cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} {A = A} ⊢const (⊢cast {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} ⊢const ⊢M′ of λ where
      (yes M⊑M′) →
        yes (⊑-castᵣ A⊑A′ A⊑B′ ⟨ gc , pc , ⊢const ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castᵣ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  A⋤B′) →
      no λ { (⊑-castᵣ _ A⊑B′ ⟨ _ , _ , ⊢M ⟩ _) →
        case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
        refl → contradiction A⊑B′ A⋤B′ }
  (no  A⋤A′) →
    no λ { (⊑-castᵣ A⊑A′ _ ⟨ _ , _ , ⊢M ⟩ _) →
      case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} ⊢const (⊢cast-pc {g = g} ⊢M′ _) =
  case cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {g} {pc} ⊢const ⊢M′ of λ where
  (yes M⊑M′) → yes (⊑-cast-pcᵣ M⊑M′)
  (no  M⋤M′) → no (λ { (⊑-cast-pcᵣ M⊑M′) → contradiction M⊑M′ M⋤M′ })
cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} {A = A} ⊢const (⊢sub {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑?-const {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} ⊢const ⊢M′ of λ where
      (yes M⊑M′) →
        yes (⊑-subᵣ A⊑A′ A⊑B′ ⟨ gc , pc , ⊢const ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-subᵣ _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  A⋤B′) →
      no λ { (⊑-subᵣ _ A⊑B′ ⟨ _ , _ , ⊢M ⟩ _) →
        case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
        refl → contradiction A⊑B′ A⋤B′ }
  (no  A⋤A′) →
    no λ { (⊑-subᵣ A⊑A′ _ ⟨ _ , _ , ⊢M ⟩ _) →
      case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
      refl → contradiction A⊑A′ A⋤A′ }
cc-⊑?-const {gc = gc} {pc = pc} ⊢const (⊢sub-pc ⊢M′ x) = cc-⊑?-const {gc = gc} {pc = pc} ⊢const ⊢M′
cc-⊑?-const {gc = gc} {pc = pc} {A = A} ⊢const (⊢err {A = A′}) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) → yes (⊑-err ⟨ gc , pc , ⊢const ⟩ A⊑A′)
  (no  A⋤A′) →
    no (λ { (⊑-err ⟨ _ , _ , ⊢M ⟩ A⊑A′) →
      case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
      refl → contradiction A⊑A′ A⋤A′ })
cc-⊑?-const (⊢sub-pc ⊢M gc<:gc′) ⊢M′ = cc-⊑?-const ⊢M ⊢M′

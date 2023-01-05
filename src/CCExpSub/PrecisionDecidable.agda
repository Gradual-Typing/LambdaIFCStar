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


const-eq? : ∀ {ι} → (k₁ k₂ : rep ι) → Dec (k₁ ≡ k₂)
const-eq? {Bool} false false = yes refl
const-eq? {Bool} false true  = no λ ()
const-eq? {Bool} true false  = no λ ()
const-eq? {Bool} true true   = yes refl
const-eq? {Unit} tt tt       = yes refl

addr-eq? : ∀ (a₁ a₂ : Addr) → Dec (a₁ ≡ a₂)
addr-eq? (a⟦ ℓ̂₁ ⟧ n₁) (a⟦ ℓ̂₂ ⟧ n₂) =
  case ℓ̂₁ =? ℓ̂₂ of λ where
  (yes refl) →
    case n₁ ≟ n₂ of λ where
    (yes refl) → yes refl
    (no  neq)  → no λ { refl → contradiction refl neq }
  (no  neq)  → no λ { refl → contradiction refl neq }

cc-⊑? : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′ M M′}
  → Γ  ; Σ  ; gc  ; pc  ⊢ M  ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    ---------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′)
cc-⊑? {M = $ k of ℓ} {$ k′ of ℓ′} (⊢const {ι = ι}) (⊢const {ι = ι′}) =
  case (` ι) ≡ᵣ? (` ι′) of λ where
  (yes refl) →
    case const-eq? k k′ of λ where
    (yes refl) →
      case ℓ =? ℓ′ of λ where
      (yes refl) → yes ⊑-const
      (no  ℓ≢ℓ)  → no λ { ⊑-const → contradiction refl ℓ≢ℓ }
    (no  k≢k)    → no λ { ⊑-const → contradiction refl k≢k }
  (no  ι≢ι)      → no λ { ⊑-const → contradiction refl ι≢ι }
cc-⊑? ⊢const (⊢addr x) = no λ ()
cc-⊑? ⊢const (⊢var x) = no λ ()
cc-⊑? ⊢const (⊢lam x) = no λ ()
cc-⊑? ⊢const (⊢app _ _) = no λ ()
cc-⊑? ⊢const (⊢if _ _ _) = no λ ()
cc-⊑? ⊢const (⊢let _ _) = no λ ()
cc-⊑? ⊢const (⊢ref _ _) = no λ ()
cc-⊑? ⊢const (⊢ref? _) = no λ ()
cc-⊑? ⊢const (⊢ref✓ _ _) = no λ ()
cc-⊑? ⊢const (⊢deref _) = no λ ()
cc-⊑? ⊢const (⊢assign _ _ _) = no λ ()
cc-⊑? ⊢const (⊢assign? _ _) = no λ ()
cc-⊑? ⊢const (⊢assign✓ _ _ _) = no λ ()
cc-⊑? ⊢const (⊢prot _) = no λ ()
cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} {A = A} ⊢const (⊢cast {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} ⊢const ⊢M′ of λ where
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
cc-⊑? ⊢const (⊢cast-pc ⊢M′ x) = {!!}
cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} {A = A} ⊢const (⊢sub {A = A′} {B′} ⊢M′) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case A ⊑? B′ of λ where
    (yes A⊑B′) →
      case cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} ⊢const ⊢M′ of λ where
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
cc-⊑? {gc = gc} {pc = pc} {A = A} ⊢const (⊢err {A = A′}) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) → yes (⊑-err ⟨ gc , pc , ⊢const ⟩ A⊑A′)
  (no  A⋤A′) →
    no (λ { (⊑-err ⟨ _ , _ , ⊢M ⟩ A⊑A′) →
      case uniqueness {gc† = gc} {pc† = pc} ⊢M ⊢const of λ where
      refl → contradiction A⊑A′ A⋤A′ })
cc-⊑? (⊢addr x) ⊢M′ = {!!}
cc-⊑? (⊢var x) ⊢M′ = {!!}
cc-⊑? (⊢lam x) ⊢M′ = {!!}
cc-⊑? (⊢app ⊢M ⊢M₁) ⊢M′ = {!!}
cc-⊑? (⊢if ⊢M x x₁) ⊢M′ = {!!}
cc-⊑? (⊢let ⊢M x) ⊢M′ = {!!}
cc-⊑? (⊢ref ⊢M x) ⊢M′ = {!!}
cc-⊑? (⊢ref? ⊢M) ⊢M′ = {!!}
cc-⊑? (⊢ref✓ ⊢M x) ⊢M′ = {!!}
cc-⊑? (⊢deref ⊢M) ⊢M′ = {!!}
cc-⊑? (⊢assign ⊢M ⊢M₁ x) ⊢M′ = {!!}
cc-⊑? (⊢assign? ⊢M x) ⊢M′ = {!!}
cc-⊑? (⊢assign✓ ⊢M ⊢M₁ x) ⊢M′ = {!!}
cc-⊑? (⊢prot ⊢M) ⊢M′ = {!!}
cc-⊑? (⊢cast ⊢M) ⊢M′ = {!!}
cc-⊑? (⊢cast-pc ⊢M x) ⊢M′ = {!!}
cc-⊑? (⊢sub ⊢M) ⊢M′ = {!!}
cc-⊑? ⊢err ⊢M′ = {!!}
cc-⊑? (⊢sub-pc ⊢M _) ⊢M′ = cc-⊑? ⊢M ⊢M′
cc-⊑? ⊢M (⊢sub-pc ⊢M′ _) = cc-⊑? ⊢M ⊢M′

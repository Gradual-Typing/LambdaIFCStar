module PrecisionDecidable where

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

open import Utils
open import Types
open import HeapContext
open import TypeBasedCast
open import CC
open import CCPrecision

open import CCEqDecidable


cc-⊑? : ∀ {Γ Γ′ Σ Σ′} M M′ → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′)
cc-⊑? (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) = {!!}
cc-⊑? (M ⟨ c ⟩) M′ = {!!}
cc-⊑? M (M′ ⟨ c′ ⟩) = {!!}
cc-⊑? (op-const {ι} k ℓ ⦅ nil ⦆) (op-const {ι′} k′ ℓ′ ⦅ nil ⦆) =
  case (` ι) ≡ᵣ? (` ι′) of λ where
  (yes refl) →
    case const-eq? k k′ of λ where
    (yes refl) →
      case ℓ =? ℓ′ of λ where
      (yes refl) → yes ⊑-const
      (no  ℓ≢ℓ)  → no λ { ⊑-const → contradiction refl ℓ≢ℓ }
    (no  k≢k)  → no λ { ⊑-const → contradiction refl k≢k }
  (no  ι≢ι)  → no λ { ⊑-const → contradiction refl ι≢ι }
cc-⊑? (` x) (` x′) =
  case x ≟ x′ of λ where
  (yes refl) → yes ⊑-var
  (no  x≢x)  → no λ { ⊑-var → contradiction refl x≢x }
cc-⊑? (addr a of ℓ) (addr a′ of ℓ′) =
  case addr-eq? a a′ of λ where
  (yes refl) →
    case ℓ =? ℓ′ of λ where
    (yes refl) → yes ⊑-addr
    (no  ℓ≢ℓ)  → no λ { ⊑-addr → contradiction refl ℓ≢ℓ }
  (no  a≢a)  → no λ { ⊑-addr → contradiction refl a≢a }
cc-⊑? {Γ} {Γ′} {Σ} {Σ′} (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) (ƛ⟦ ℓᶜ′ ⟧ A′ ˙ N′ of ℓ′) =
  case ⟨ ℓᶜ =? ℓᶜ′ , ℓ =? ℓ′ ⟩ of λ where
    ⟨ yes refl , yes refl ⟩ →
      case A ⊑? A′ of λ where
      (yes A⊑A′) →
        case cc-⊑? {A ∷ Γ} {A′ ∷ Γ′} {Σ} {Σ′} N N′ of λ where
        (yes N⊑N′) → yes (⊑-lam A⊑A′ N⊑N′)
        (no  N⋤N′) → no λ { (⊑-lam _ N⊑N′) → contradiction N⊑N′ N⋤N′ }
      (no  A⋤A′) → no λ { (⊑-lam A⊑A′ _) → contradiction A⊑A′ A⋤A′ }
    ⟨ no ℓᶜ≢ℓᶜ , _      ⟩ → no λ { (⊑-lam _ _) → contradiction refl ℓᶜ≢ℓᶜ }
    ⟨ _        , no ℓ≢ℓ ⟩ → no λ { (⊑-lam _ _) → contradiction refl ℓ≢ℓ }


M′ = ƛ⟦ low ⟧ ` Bool of l high ˙ ` 0 of low
M  = ƛ⟦ low ⟧ ` Bool of ⋆      ˙ ` 0 of low

res = cc-⊑? {[]} {[]} {∅} {∅} M M′

_ : ∃[ ƛ⊑ƛ′ ] (res ≡ yes ƛ⊑ƛ′)
_ = ⟨ _ , refl ⟩

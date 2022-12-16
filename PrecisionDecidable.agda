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


cc-⊑? : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′ A A′} M M′
  → Γ  ; Σ  ; gc  ; pc  ⊢ M  ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    -----------------------------------
  → Dec (Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′)
cc-⊑? (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) (⊢cast ⊢M) (⊢cast ⊢M′) = {!!}
cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} {A′ = A′} (M ⟨ cast A B _ _ ⟩) (` x) (⊢cast ⊢M) (⊢var ∋x) =
  case A ⊑? A′ of λ where
  (yes A⊑A′) →
    case B ⊑? A′ of λ where
    (yes B⊑A′) →
      case cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {pc} {pc′} M (` x) ⊢M (⊢var ∋x) of λ where
      (yes M⊑M′) → yes (⊑-castl A⊑A′ B⊑A′ ⟨ gc′ , pc′ , ⊢var ∋x ⟩ M⊑M′)
      (no  M⋤M′) → no λ { (⊑-castl _ _ _ M⊑M′) → contradiction M⊑M′ M⋤M′ }
    (no  B⋤A′) → {!!}
  (no  A⋤A′) → no λ { (⊑-castl A⊑A′ _ _ _) → contradiction A⊑A′ {!A⋤A′!} }
cc-⊑? (M ⟨ c ⟩) ($ k of ℓ) (⊢cast ⊢M) ⊢const = {!!}
cc-⊑? (M ⟨ c ⟩) (addr a of ℓ) (⊢cast ⊢M) (⊢addr _) = {!!}
cc-⊑? M (M′ ⟨ c′ ⟩) ⊢M (⊢cast ⊢M′)  = {!!}
cc-⊑? M (error e) ⊢M ⊢err = yes ⊑-err
cc-⊑? (op-const {ι} k ℓ ⦅ nil ⦆) (op-const {ι′} k′ ℓ′ ⦅ nil ⦆) ⊢M ⊢M′ =
  case (` ι) ≡ᵣ? (` ι′) of λ where
  (yes refl) →
    case const-eq? k k′ of λ where
    (yes refl) →
      case ℓ =? ℓ′ of λ where
      (yes refl) → yes ⊑-const
      (no  ℓ≢ℓ)  → no λ { ⊑-const → contradiction refl ℓ≢ℓ }
    (no  k≢k)  → no λ { ⊑-const → contradiction refl k≢k }
  (no  ι≢ι)  → no λ { ⊑-const → contradiction refl ι≢ι }
cc-⊑? ($ k of ℓ) M ⊢M ⊢M′ = {!!}
cc-⊑? (` x) (` x′) ⊢M ⊢M′ =
  case x ≟ x′ of λ where
  (yes refl) → yes ⊑-var
  (no  x≢x)  → no λ { ⊑-var → contradiction refl x≢x }
cc-⊑? (` x) M ⊢M ⊢M′ = {!!}
cc-⊑? (addr a of ℓ) (addr a′ of ℓ′) (⊢addr _) (⊢addr _) =
  case addr-eq? a a′ of λ where
  (yes refl) →
    case ℓ =? ℓ′ of λ where
    (yes refl) → yes ⊑-addr
    (no  ℓ≢ℓ)  → no λ { ⊑-addr → contradiction refl ℓ≢ℓ }
  (no  a≢a)  → no λ { ⊑-addr → contradiction refl a≢a }
cc-⊑? (addr a of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? {Γ} {Γ′} {Σ} {Σ′} {pc = pc} {pc′} (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) (ƛ⟦ ℓᶜ′ ⟧ A′ ˙ N′ of ℓ′) (⊢lam ⊢N) (⊢lam ⊢N′) =
  case ⟨ ℓᶜ =? ℓᶜ′ , ℓ =? ℓ′ ⟩ of λ where
    ⟨ yes refl , yes refl ⟩ →
      case A ⊑? A′ of λ where
      (yes A⊑A′) →
        case cc-⊑? {A ∷ Γ} {A′ ∷ Γ′} {Σ} {Σ′} {pc = pc} {pc′} N N′ ⊢N ⊢N′ of λ where
        (yes N⊑N′) → yes (⊑-lam A⊑A′ N⊑N′)
        (no  N⋤N′) → no λ { (⊑-lam _ N⊑N′) → contradiction N⊑N′ N⋤N′ }
      (no  A⋤A′) → no λ { (⊑-lam A⊑A′ _) → contradiction A⊑A′ A⋤A′ }
    ⟨ no ℓᶜ≢ℓᶜ , _      ⟩ → no λ { (⊑-lam _ _) → contradiction refl ℓᶜ≢ℓᶜ }
    ⟨ _        , no ℓ≢ℓ ⟩ → no λ { (⊑-lam _ _) → contradiction refl ℓ≢ℓ }
cc-⊑? (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L · M) (L′ · M′) ⊢M ⊢M′ = {!!}
cc-⊑? (L · M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (if L A M N) (if L′ A′ M′ N′) ⊢M ⊢M′ = {!!}
cc-⊑? (if L A M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (`let M N) (`let M′ N′) ⊢M ⊢M′ = {!!}
cc-⊑? (`let M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref⟦ ℓ ⟧ M) (ref⟦ ℓ′ ⟧ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (ref⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref?⟦ ℓ ⟧ M) (ref?⟦ ℓ′ ⟧ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (ref?⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref✓⟦ ℓ ⟧ M) (ref✓⟦ ℓ′ ⟧ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (ref✓⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (! M) (! M′) ⊢M ⊢M′ = {!!}
cc-⊑? (! M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L := M) (L′ := M′) ⊢M ⊢M′ = {!!}
cc-⊑? (L := M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=? M) (L′ :=? M′) ⊢M ⊢M′ = {!!}
cc-⊑? (L :=? M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=✓ M) (L′ :=✓ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (L :=✓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (prot ℓ M) (prot ℓ′ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (prot ℓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (cast-pc g M) (cast-pc g′ M′) ⊢M ⊢M′ = {!!}
cc-⊑? (cast-pc g M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (error e) M′ ⊢M ⊢M′ = {!!}
cc-⊑? M M′ (⊢sub ⊢M A<:B) ⊢M′ = cc-⊑? M M′ ⊢M ⊢M′
cc-⊑? M M′ ⊢M (⊢sub ⊢M′ A<:B) = cc-⊑? M M′ ⊢M ⊢M′
cc-⊑? M M′ (⊢sub-pc ⊢M _) ⊢M′ = cc-⊑? M M′ ⊢M ⊢M′
cc-⊑? M M′ ⊢M (⊢sub-pc ⊢M′ gc<:gc′) = {!!}


-- M′ = ƛ⟦ low ⟧ ` Bool of l high ˙ ` 0 of low
-- M  = ƛ⟦ low ⟧ ` Bool of ⋆      ˙ ` 0 of low

-- res = cc-⊑? {[]} {[]} {∅} {∅} M M′ {!!} {!!}

-- _ : ∃[ ƛ⊑ƛ′ ] (res ≡ yes ƛ⊑ƛ′)
-- _ = ⟨ _ , refl ⟩

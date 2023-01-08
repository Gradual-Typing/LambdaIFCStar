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
cc-⊑? (` x) M′ ⊢M ⊢M′ = {!!}
cc-⊑? ($ k of ℓ) M ⊢M ⊢M′ = cc-⊑?-const ⊢M ⊢M′
cc-⊑? (addr a of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ƛ⟦ pc ⟧ A ˙ N of ℓ) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L · M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (if L A M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (`let M N) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref?⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (ref✓⟦ ℓ ⟧ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (! M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L := M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=? M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (L :=✓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (M ⟨ c ⟩) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (M ↟⟨ c ⟩) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (prot ℓ M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (cast-pc g M) M′ ⊢M ⊢M′ = {!!}
cc-⊑? (error A e) M′ ⊢M ⊢M′ = {!!}
cc-⊑? ● M′ ⊢M ⊢M′ = {!!}

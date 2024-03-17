module Dyn.Erasure where

open import Data.Nat
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Dyn.Syntax
open import Dyn.Values
open import Memory.Heap Term Value


{- **** Term erasure **** -}
erase : Term → Term
erase (` x) = ` x
erase ($ k of ℓ) =
  case ℓ of λ where
  low  → $ k of low
  high → ●
erase (addr a⟦ ℓ̂ ⟧ n of ℓ) =
  case ⟨ ℓ , ℓ̂ ⟩ of λ where
  ⟨ low , low ⟩ → addr (a⟦ low ⟧ n) of low
  _             → ●
erase (ƛ N of ℓ) =
  case ℓ of λ where
  low  → ƛ (erase N) of low
  high → ●
erase (L · M) = erase L · erase M
erase (if L M N) = if (erase L) (erase M) (erase N)
erase (ref?⟦ ℓ ⟧ M) = ref?⟦ ℓ ⟧ erase M
erase (! M) = ! erase M
erase (L :=? M) = erase L :=? erase M
erase _ = ●

erase-val-value : ∀ {V} (v : Value V) → Value (erase V)
erase-val-value (V-addr {a⟦ ℓ₁ ⟧ n} {low}) with ℓ₁
... | low  = V-addr
... | high = V-●
erase-val-value (V-addr {a⟦ ℓ₁ ⟧ n} {high}) = V-●
erase-val-value (V-ƛ {ℓ = ℓ}) with ℓ
... | low  = V-ƛ
... | high = V-●
erase-val-value (V-const {ℓ = ℓ}) with ℓ
... | low  = V-const
... | high = V-●
erase-val-value V-● = V-●

erase-stamp-high : ∀ {V} (v : Value V) → erase (stamp-val V v high) ≡ ●
erase-stamp-high (V-const {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-addr {a⟦ ℓ₁ ⟧ n} {ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-ƛ {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high V-● = refl


{- **** Heap erasure **** -}
erase-μᴸ : HalfHeap → HalfHeap
erase-μᴸ [] = []
erase-μᴸ (⟨ n , V & v ⟩ ∷ μᴸ) = ⟨ n , erase V & erase-val-value v ⟩ ∷ erase-μᴸ μᴸ

erase-μ : Heap → HalfHeap
erase-μ ⟨ μᴸ , μᴴ ⟩ = erase-μᴸ μᴸ

erase-μᴸ-length : ∀ μᴸ → length μᴸ ≡ length (erase-μᴸ μᴸ)
erase-μᴸ-length [] = refl
erase-μᴸ-length (⟨ n , V & v ⟩ ∷ μᴸ) = cong suc (erase-μᴸ-length μᴸ)

erase-μ-lookup-low : ∀ {μᴸ μᴴ n V v}
  → lookup-μ ⟨ μᴸ , μᴴ ⟩ (a⟦ low ⟧ n) ≡ just (V & v)
    ------------------------------------------------------------------------
  → find _≟_ (erase-μ ⟨ μᴸ , μᴴ ⟩) n ≡ just (erase V & erase-val-value v)
erase-μ-lookup-low {⟨ n₁ , V₁ & v₁ ⟩ ∷ μᴸ} {μᴴ} {n} {V} {v}
  with n ≟ n₁
... | yes refl = λ { refl → refl }
... | no _ = λ eq → erase-μ-lookup-low {μᴸ} {μᴴ} {v = v} eq

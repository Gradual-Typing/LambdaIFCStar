module Dyn.Values where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.Types using (Base; rep)
open import Dyn.Syntax


data Value : Term → Set where
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {N ℓ} → Value (ƛ N of ℓ)
  V-● : Value ●

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val ($ k of ℓ₁)    V-const ℓ₂ = $ k of (ℓ₁ ⋎ ℓ₂)
stamp-val (addr a of ℓ₁) V-addr  ℓ₂ = addr a of (ℓ₁ ⋎ ℓ₂)
stamp-val (ƛ N of ℓ₁)    V-ƛ     ℓ₂ = ƛ N of (ℓ₁ ⋎ ℓ₂)
stamp-val ● V-● _ = ●

stamp-val-value : ∀ {V ℓ} (v : Value V) → Value (stamp-val V v ℓ)
stamp-val-value V-addr = V-addr
stamp-val-value V-ƛ = V-ƛ
stamp-val-value V-const = V-const
stamp-val-value V-● = V-●

stamp-val-low : ∀ {V} (v : Value V) → stamp-val V v low ≡ V
stamp-val-low (V-addr {ℓ = ℓ}) with ℓ
... | low  = refl
... | high = refl
stamp-val-low (V-ƛ {ℓ = ℓ}) with ℓ
... | low  = refl
... | high = refl
stamp-val-low (V-const {ℓ = ℓ}) with ℓ
... | low  = refl
... | high = refl
stamp-val-low V-● = refl

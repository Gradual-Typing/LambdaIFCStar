module CC2.Values where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.Coercions
open import Memory.HeapContext
open import CC2.Syntax
open import CC2.Typing


data Err : Term → Set where
  E-blame : ∀ {p} → Err (blame p)


data RawValue : Term → Set where
  V-addr  : ∀ {n} → RawValue (addr n)
  V-ƛ     : ∀ {N} → RawValue (ƛ N)
  V-const : ∀ {ι} {k : rep ι} → RawValue ($ k)

data Value : Term → Set where
  V-raw   : ∀ {V} → RawValue V → Value V
  V-cast  : ∀ {A B V} {c : Cast A ⇒ B}
    → RawValue V → Irreducible c → Value (V ⟨ c ⟩)
  V-●    : Value ●


data Result : Term → Set where
  success : ∀ {V} → Value V → Result V
  fail    : ∀ {p}            → Result (blame p)


canonical⋆ : ∀ {Γ Σ gc ℓv V T}
  → Value V
  → Γ ; Σ ; gc ; ℓv ⊢ V ⇐ T of ⋆
  → ∃[ A ] Σ[ c ∈ Cast A ⇒ T of ⋆ ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Irreducible c) × (Γ ; Σ ; gc ; ℓv ⊢ W ⇐ A)
canonical⋆ (V-raw V-addr) ()
canonical⋆ (V-raw V-ƛ) ()
canonical⋆ (V-raw V-const) ()
canonical⋆ (V-cast {V = W} {c} w i) (⊢cast ⊢W) = ⟨ _ , c , _ , refl , i , ⊢W ⟩


⊢value-pc : ∀ {Γ Σ gc gc′ ℓv ℓv′ V A}
  → Γ ; Σ ; gc  ; ℓv ⊢ V ⇐ A
  → Value V
  → Γ ; Σ ; gc′ ; ℓv′ ⊢ V ⇐ A
⊢value-pc (⊢addr eq) (V-raw V-addr) = ⊢addr eq
⊢value-pc (⊢lam ⊢N) (V-raw V-ƛ) = ⊢lam ⊢N
⊢value-pc ⊢const (V-raw V-const) = ⊢const
⊢value-pc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-pc ⊢V (V-raw v))

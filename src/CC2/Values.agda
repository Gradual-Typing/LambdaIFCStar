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


stamp-val : ∀ V → Value V → (A : Type) → StaticLabel → Term
stamp-val V (V-raw v)             _ low  = V
stamp-val V (V-raw v) (T of l high) high = V
stamp-val V (V-raw v) (T of l low ) high =
  V ⟨ cast (coerceᵣ-id T) (id (l low) ⨾ ↑) ⟩
stamp-val (V ⟨ c ⟩) (V-cast v i) A ℓ = V ⟨ stamp-ir c i ℓ ⟩
-- impossible, suppose ⊢ V ⇐ A
stamp-val V v A ℓ = ●

stamp-val-wt : ∀ {Σ gc ℓv A V ℓ}
  → (v : Value V)
  → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
    -------------------------------------------------------------
  → [] ; Σ ; gc ; ℓv ⊢ stamp-val V v A ℓ ⇐ stamp A (l ℓ)
stamp-val-wt {A = A} {ℓ = low} (V-raw V-addr) ⊢V rewrite stamp-low A = ⊢V
stamp-val-wt {ℓ = high} (V-raw V-addr) (⊢addr {ℓ = low} eq) =
  ⊢cast (⊢addr eq)
stamp-val-wt {ℓ = high} (V-raw V-addr) (⊢addr {ℓ = high} eq) = ⊢addr eq
stamp-val-wt {A = A} {ℓ = low} (V-raw V-ƛ) ⊢V rewrite stamp-low A = ⊢V
stamp-val-wt {ℓ = high} (V-raw V-ƛ) (⊢lam {ℓ = low} ⊢N) =
  ⊢cast (⊢lam ⊢N)
stamp-val-wt {ℓ = high} (V-raw V-ƛ) (⊢lam {ℓ = high} ⊢N) = ⊢lam ⊢N
stamp-val-wt {A = A} {ℓ = low} (V-raw V-const) ⊢V rewrite stamp-low A = ⊢V
stamp-val-wt {ℓ = high} (V-raw V-const) (⊢const {ℓ = low}) =
  ⊢cast ⊢const
stamp-val-wt {ℓ = high} (V-raw V-const) (⊢const {ℓ = high}) = ⊢const
stamp-val-wt {A = A} {V} {ℓ} (V-cast v i) (⊢cast ⊢V) = ⊢cast ⊢V


-- Stamping a value gets a value
stamp-val-value : ∀ {Σ gc ℓv A V ℓ}
  → (v : Value V)
  → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
  → Value (stamp-val V v A ℓ)
stamp-val-value {ℓ = low} (V-raw V-addr) ⊢V = V-raw V-addr
stamp-val-value {ℓ = high} (V-raw V-addr) (⊢addr {ℓ = low} _) =
  V-cast V-addr (ir-ref (up id))
stamp-val-value {ℓ = high} (V-raw V-addr) (⊢addr {ℓ = high} _) = V-raw V-addr
stamp-val-value {ℓ = low} (V-raw V-ƛ) ⊢V = V-raw V-ƛ
stamp-val-value {ℓ = high} (V-raw V-ƛ) (⊢lam {ℓ = low} _) =
  V-cast V-ƛ (ir-fun (up id))
stamp-val-value {ℓ = high} (V-raw V-ƛ) (⊢lam {ℓ = high} _) = V-raw V-ƛ
stamp-val-value {ℓ = low} (V-raw V-const) ⊢V = V-raw V-const
stamp-val-value {ℓ = high} (V-raw V-const) (⊢const {ℓ = low}) =
  V-cast V-const (ir-base (up id) (λ ()))
stamp-val-value {ℓ = high} (V-raw V-const) (⊢const {ℓ = high}) = V-raw V-const
stamp-val-value (V-cast v i) ⊢V = V-cast v (stamp-ir-irreducible i)


stamp-val-low : ∀ {Σ gc ℓv A V}
  → (v : Value V)
  → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
  → stamp-val V v A low ≡ V
stamp-val-low (V-raw V-addr) ⊢V = refl
stamp-val-low (V-raw V-ƛ) ⊢V = refl
stamp-val-low (V-raw V-const) ⊢V = refl
stamp-val-low (V-cast v (ir-base (id {l low}) x₁)) ⊢V = refl
stamp-val-low (V-cast v (ir-base (id {l high}) x₁)) ⊢V = refl
stamp-val-low (V-cast v (ir-base (inj id) x₁)) ⊢V = refl
stamp-val-low (V-cast v (ir-base (inj (up id)) x₁)) ⊢V = refl
stamp-val-low (V-cast v (ir-base (up id) x₁)) ⊢V = refl
stamp-val-low (V-cast v (ir-ref (id {l low}))) ⊢V = refl
stamp-val-low (V-cast v (ir-ref (id {l high}))) ⊢V = refl
stamp-val-low (V-cast v (ir-ref (inj id))) ⊢V = refl
stamp-val-low (V-cast v (ir-ref (inj (up id)))) ⊢V = refl
stamp-val-low (V-cast v (ir-ref (up id))) ⊢V = refl
stamp-val-low (V-cast v (ir-fun (id {l low}))) ⊢V = refl
stamp-val-low (V-cast v (ir-fun (id {l high}))) ⊢V = refl
stamp-val-low (V-cast v (ir-fun (inj id))) ⊢V = refl
stamp-val-low (V-cast v (ir-fun (inj (up id)))) ⊢V = refl
stamp-val-low (V-cast v (ir-fun (up id))) ⊢V = refl


⊢value-pc : ∀ {Γ Σ gc gc′ ℓv ℓv′ V A}
  → Γ ; Σ ; gc  ; ℓv ⊢ V ⇐ A
  → Value V
  → Γ ; Σ ; gc′ ; ℓv′ ⊢ V ⇐ A
⊢value-pc (⊢addr eq) (V-raw V-addr) = ⊢addr eq
⊢value-pc (⊢lam ⊢N) (V-raw V-ƛ) = ⊢lam ⊢N
⊢value-pc ⊢const (V-raw V-const) = ⊢const
⊢value-pc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-pc ⊢V (V-raw v))

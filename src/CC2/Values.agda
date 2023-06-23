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
  E-error : ∀ {p} → Err (blame p)


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


{- I don't think we need the value canonical form lemmas anymore -}
-- data Fun : Term → HeapContext → Type → Set where
--   Fun-ƛ : ∀ {Σ g A B N ℓ}
--     → (∀ {ℓv} → A ∷ [] ; Σ ; g ; ℓv ⊢ N ⇐ B)
--       ----------------------------------------------------- Lambda
--     → Fun (ƛ N) Σ (⟦ g ⟧ A ⇒ B of l ℓ)

--   Fun-proxy : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ g₁ g₂ N}
--                 {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
--     → Fun (ƛ N) Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
--     → Irreducible c
--       ----------------------------------------------------- Function Proxy
--     → Fun ((ƛ N) ⟨ c ⟩) Σ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)

-- -- Sanity checks
-- fun-is-value : ∀ {Σ V gc A B g}
--   → Fun V Σ (⟦ gc ⟧ A ⇒ B of g)
--   → Value V
-- fun-is-value (Fun-ƛ _) = V-raw V-ƛ
-- fun-is-value (Fun-proxy (Fun-ƛ ⊢N) i) = V-cast V-ƛ i

-- -- Canonical form of value of function type
-- canonical-fun : ∀ {Σ gc gc′ pc A B g V}
--   → [] ; Σ ; gc ; pc ⊢ V ⇐ ⟦ gc′ ⟧ A ⇒ B of g
--   → Value V
--   → Fun V Σ (⟦ gc′ ⟧ A ⇒ B of g)
-- canonical-fun (⊢lam ⊢N) (V-raw V-ƛ) = Fun-ƛ ⊢N
-- canonical-fun (⊢cast (⊢lam ⊢N)) (V-cast V-ƛ i) =
--   Fun-proxy (Fun-ƛ ⊢N) i


canonical⋆ : ∀ {Γ Σ gc ℓv V T}
  → Value V
  → Γ ; Σ ; gc ; ℓv ⊢ V ⇐ T of ⋆
  → ∃[ A ] Σ[ c ∈ Cast A ⇒ T of ⋆ ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Irreducible c) × (Γ ; Σ ; gc ; ℓv ⊢ W ⇐ A)
canonical⋆ (V-raw V-addr) ()
canonical⋆ (V-raw V-ƛ) ()
canonical⋆ (V-raw V-const) ()
canonical⋆ (V-cast {V = W} {c} w i) (⊢cast ⊢W) = ⟨ _ , c , _ , refl , i , ⊢W ⟩


stamp-val : ∀ {Σ gc ℓv A} V → Value V → [] ; Σ ; gc ; ℓv ⊢ V ⇐ A → StaticLabel → Term
stamp-val (addr n) (V-raw V-addr) ⊢V low = addr n
stamp-val (addr n) (V-raw V-addr) (⊢addr {T = T} {low} {ℓ̂} x) high =
  addr n ⟨ cast (coerceᵣ-id (Ref (T of l ℓ̂))) (id (l low) ⨾ ↑) ⟩
stamp-val (addr n) (V-raw V-addr) (⊢addr {ℓ = high} x) high = addr n
stamp-val (ƛ N) (V-raw V-ƛ) ⊢V low = ƛ N
stamp-val (ƛ N) (V-raw V-ƛ) (⊢lam {g = g} {A} {B} {ℓ = low} ⊢N) high =
  ƛ N ⟨ cast (coerceᵣ-id (⟦ g ⟧ A ⇒ B)) (id (l low) ⨾ ↑) ⟩
stamp-val (ƛ N) (V-raw V-ƛ) (⊢lam {ℓ = high} ⊢N) high = ƛ N
stamp-val ($ k) (V-raw V-const) ⊢V low = $ k
stamp-val ($ k) (V-raw V-const) (⊢const {ι = ι} {ℓ = low}) high =
  $ k ⟨ cast (id ι) (id (l low) ⨾ ↑) ⟩
stamp-val ($ k) (V-raw V-const) (⊢const {ℓ = high}) high = $ k
stamp-val (V ⟨ c ⟩) (V-cast v i) ⊢V ℓ = V ⟨ stamp-ir c i ℓ ⟩


-- A stamped value is value
stamp-val-value : ∀ {Σ gc ℓv A V ℓ}
  → (v : Value V)
  → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
  → Value (stamp-val V v ⊢V ℓ)
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
  → stamp-val V v ⊢V low ≡ V
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

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
open import LabelCoercionCalculus.Stamping renaming (stamp to stampₗ)


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


-- canonical⋆ : ∀ {Γ Σ gc pc V T}
--   → Γ ; Σ ; gc ; pc ⊢ V ⦂ T of ⋆
--   → Value V
--   → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ]
--        (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ A) × (B <: T of ⋆)
-- canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
--   ⟨ _ , _ , c , W , refl , i , ⊢W , <:-ty <:-⋆ <:ᵣ-refl ⟩
-- canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
--   case canonical⋆ ⊢V v of λ where
--     ⟨ A , B , c , W , refl , i , ⊢W , B<:T′⋆ ⟩ →
--       ⟨ A , B , c , W , refl , i , ⊢W , <:-trans B<:T′⋆ (<:-ty <:-⋆ T′<:T) ⟩
-- canonical⋆ (⊢sub-pc ⊢V gc<:gc′) v =
--   case canonical⋆ ⊢V v of λ where
--     ⟨ A , B , c , W , refl , i , ⊢W , B<:T⋆ ⟩ →
--       ⟨ A , B , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , B<:T⋆ ⟩

-- canonical-ref⋆ : ∀ {Γ Σ gc pc V T g}
--   → Γ ; Σ ; gc ; pc ⊢ V ⦂ Ref (T of ⋆) of g
--   → Value V
--   → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ]
--        (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ A) × (B <: Ref (T of ⋆) of g)
-- canonical-ref⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
--   ⟨ _ , _ , c , W , refl , i , ⊢W , <:-refl ⟩
-- canonical-ref⋆ (⊢sub ⊢V sub) v =
--   case sub of λ where
--     (<:-ty _ (<:-ref (<:-ty <:-⋆ S<:T) (<:-ty <:-⋆ T<:S))) →
--       case canonical-ref⋆ ⊢V v of λ where
--         ⟨ A , B , c , W , refl , i , ⊢W , B<:RefS ⟩ →
--           ⟨ A , B , c , W , refl , i , ⊢W , <:-trans B<:RefS sub ⟩
-- canonical-ref⋆ (⊢sub-pc ⊢V gc<:gc′) v =
--   case canonical-ref⋆ ⊢V v of λ where
--   ⟨ A , B , c , W , refl , i , ⊢W , B<:RefT ⟩ →
--     ⟨ A , B , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , B<:RefT ⟩



stamp-val : ∀ {Σ gc ℓv A} V → Value V → [] ; Σ ; gc ; ℓv ⊢ V ⇐ A → StaticLabel → Term
stamp-val (addr n) (V-raw V-addr) (⊢addr x) low = addr n
stamp-val (addr n) (V-raw V-addr) (⊢addr {T = T} {low} {ℓ̂} x) high =
  addr n ⟨ cast (coerceᵣ-id (Ref (T of l ℓ̂))) (id (l low) ⨾ ↑) ⟩
stamp-val (addr n) (V-raw V-addr) (⊢addr {ℓ = high} x) high = addr n
stamp-val (ƛ N) (V-raw V-ƛ) (⊢lam ⊢N) low = ƛ N
stamp-val (ƛ N) (V-raw V-ƛ) (⊢lam {g = g} {A} {B} {ℓ = low} ⊢N) high =
  ƛ N ⟨ cast (coerceᵣ-id (⟦ g ⟧ A ⇒ B)) (id (l low) ⨾ ↑) ⟩
stamp-val (ƛ N) (V-raw V-ƛ) (⊢lam {ℓ = high} ⊢N) high = ƛ N
stamp-val ($ k) (V-raw V-const) (⊢const) low = $ k
stamp-val ($ k) (V-raw V-const) (⊢const {ι = ι} {ℓ = low}) high =
  $ k ⟨ cast (id ι) (id (l low) ⨾ ↑) ⟩
stamp-val ($ k) (V-raw V-const) (⊢const {ℓ = high}) high = $ k
stamp-val (V ⟨ cast cᵣ c̅ ⟩) (V-cast v (ir-base 𝓋 _)) ⊢V ℓ =
  V ⟨ cast cᵣ (stampₗ c̅ 𝓋 ℓ) ⟩
stamp-val (V ⟨ cast cᵣ c̅ ⟩) (V-cast v (ir-ref 𝓋)) ⊢V ℓ =
  V ⟨ cast cᵣ (stampₗ c̅ 𝓋 ℓ) ⟩
stamp-val (V ⟨ cast cᵣ c̅ ⟩) (V-cast v (ir-fun 𝓋)) ⊢V ℓ =
  V ⟨ cast cᵣ (stampₗ c̅ 𝓋 ℓ) ⟩


-- -- A stamped value is value
-- stamp-val-value : ∀ {V ℓ} (v : Value V) → Value (stamp-val V v ℓ)
-- stamp-val-value V-addr = V-addr
-- stamp-val-value V-ƛ = V-ƛ
-- stamp-val-value V-const = V-const
-- stamp-val-value (V-cast v i) =
--   V-cast (stamp-val-value v) (stamp-inert-inert i)
-- stamp-val-value V-● = V-●

-- stamp-val-low : ∀ {V} (v : Value V) → stamp-val V v low ≡ V
-- stamp-val-low (V-addr {ℓ = ℓ}) with ℓ
-- ... | low  = refl
-- ... | high = refl
-- stamp-val-low (V-ƛ {ℓ = ℓ}) with ℓ
-- ... | low  = refl
-- ... | high = refl
-- stamp-val-low (V-const {ℓ = ℓ}) with ℓ
-- ... | low  = refl
-- ... | high = refl
-- stamp-val-low (V-cast v (I-base-inj (cast (` ι of l ℓ) (` ι of ⋆) p (~-ty ℓ~⋆ ~-ι))))
--   rewrite stamp-val-low v
--   with ℓ   | ℓ~⋆
-- ... | low  | ~⋆ = refl
-- ... | high | ~⋆ = refl
-- stamp-val-low (V-cast v (I-fun (cast (_ of l ℓ₁) (_ of g₂) p (~-ty ℓ₁~g₂ _)) I-label I-label))
--   rewrite stamp-val-low v
--   with ℓ₁  | g₂     | ℓ₁~g₂
-- ... | high | ⋆      | ~⋆ = refl
-- ... | high | l high | l~ = refl
-- ... | low  | ⋆      | ~⋆ = refl
-- ... | low  | l low  | l~ = refl
-- stamp-val-low (V-cast v (I-ref (cast (_ of l ℓ₁) (_ of g₂) p (~-ty ℓ₁~g₂ _)) I-label I-label))
--   rewrite stamp-val-low v
--   with ℓ₁  | g₂     | ℓ₁~g₂
-- ... | high | ⋆      | ~⋆ = refl
-- ... | high | l high | l~ = refl
-- ... | low  | ⋆      | ~⋆ = refl
-- ... | low  | l low  | l~ = refl
-- stamp-val-low V-● = refl

-- ⊢value-pc : ∀ {Γ Σ gc gc′ pc pc′ V A}
--   → Γ ; Σ ; gc  ; pc ⊢ V ⦂ A
--   → Value V
--   → Γ ; Σ ; gc′ ; pc′ ⊢ V ⦂ A
-- ⊢value-pc (⊢addr eq) V-addr = ⊢addr eq
-- ⊢value-pc (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
-- ⊢value-pc ⊢const V-const = ⊢const
-- ⊢value-pc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-pc ⊢V v)
-- ⊢value-pc (⊢sub ⊢V A<:B) v = ⊢sub (⊢value-pc ⊢V v) A<:B
-- ⊢value-pc (⊢sub-pc ⊢V gc<:gc′) v = ⊢value-pc ⊢V v

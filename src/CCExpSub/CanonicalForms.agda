module CCExpSub.CanonicalForms where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.TypeBasedCast
open import Memory.HeapContext
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_
open import CCExpSub.Values

open import CCExpSub.Uniqueness


data Fun : Term → HeapContext → Type → Set where
  Fun-ƛ : ∀ {Σ A B N ℓᶜ ℓ}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
      ----------------------------------------------------- Lambda
    → Fun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) Σ (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ)

  Fun-ƛ↟ : ∀ {Σ A B C N ℓᶜ ℓ} {A→B<:C : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ <: C}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
    → ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ≢ C
      ----------------------------------------------------- Lambda Subtyping
    → Fun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ ↟ A→B<:C) Σ C

  Fun-proxy : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ g₁ g₂ V}
                {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
      ----------------------------------------------------- Function Proxy
    → Fun (V ⟨ c ⟩) Σ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)

  Fun-proxy↟ : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ C g₁ g₂ V}
                  {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
                  {A₂→B₂<:C : ⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂ <: C}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
    → ⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂ ≢ C
      ----------------------------------------------------- Function Proxy Subtyping
    → Fun ((V ⟨ c ⟩) ↟ A₂→B₂<:C) Σ C

-- Sanity check
fun-is-value : ∀ {Σ V gc A B g}
  → Fun V Σ (⟦ gc ⟧ A ⇒ B of g)
  → Value V
fun-is-value (Fun-ƛ       _)         = V-ƛ
fun-is-value (Fun-ƛ↟     _ neq)     = V-ƛ↟ neq
fun-is-value (Fun-proxy   fun i)     = V-cast (fun-is-value fun) i
fun-is-value (Fun-proxy↟ fun i neq) = V-cast↟ (fun-is-value fun) i neq

-- Canonical form of value of function type
canonical-fun : ∀ {Σ gc pc A B g gᶜ V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gᶜ ⟧ A ⇒ B of g
  → Value V
  → Fun V Σ (⟦ gᶜ ⟧ A ⇒ B of g)
canonical-fun (⊢lam ⊢N) V-ƛ = Fun-ƛ ⊢N
canonical-fun (⊢cast ⊢V) (V-cast v (I-fun c i₁ i₂)) =
  Fun-proxy (canonical-fun ⊢V v) (I-fun c i₁ i₂)
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-ƛ↟ neq) =
  case canonical-fun ⊢V V-ƛ of λ where
  (Fun-ƛ ⊢N) → Fun-ƛ↟ ⊢N neq
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-cast↟ v i neq) =
  case i of λ where
  (I-fun _ i₁ i₂) → Fun-proxy↟ (canonical-fun (cast-wt-inv ⊢V) v) i neq
canonical-fun {gc = gc} (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-const↟ neq) =
  case uniqueness ⊢V (⊢const {gc = gc}) of λ where ()
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-addr↟ neq) =
  case canonical-fun ⊢V V-addr of λ ()
canonical-fun (⊢sub-pc ⊢V gc<:gc′) v = canonical-fun ⊢V v

data Reference : Term → HeapContext → Type → Set where
  Ref-addr : ∀ {Σ n T ℓ ℓ̂}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
      ---------------------------------------------------------- Reference
    → Reference (addr a⟦ ℓ̂ ⟧ n of ℓ) Σ (Ref (T of l ℓ̂) of l ℓ)

  Ref-addr↟ : ∀ {Σ A n T ℓ̂ ℓ} {Ref<:A : Ref (T of l ℓ̂) of l ℓ <: A}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
    → Ref (T of l ℓ̂) of l ℓ ≢ A
      ---------------------------------------------------------- Reference Subtyping
    → Reference (addr a⟦ ℓ̂ ⟧ n of ℓ ↟ Ref<:A) Σ A

  Ref-proxy : ∀ {Σ A₁ A₂ g₁ g₂ V} {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
      ------------------------------------------ Reference Proxy
    → Reference (V ⟨ c ⟩) Σ (Ref A₂ of g₂)

  Ref-proxy↟ : ∀ {Σ A₁ A₂ B g₁ g₂ V}
                {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
                {Ref<:B : Ref A₂ of g₂ <: B}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
    → Ref A₂ of g₂ ≢ B
      ------------------------------------------ Reference Proxy Subtyping
    → Reference ((V ⟨ c ⟩) ↟ Ref<:B) Σ B

ref-is-value : ∀ {Σ V A g}
  → Reference V Σ (Ref A of g)
  → Value V
ref-is-value (Ref-addr _)            = V-addr
ref-is-value (Ref-proxy ref i)       = V-cast (ref-is-value ref) i
ref-is-value (Ref-addr↟ _ neq)      = V-addr↟ neq
ref-is-value (Ref-proxy↟ ref i neq) = V-cast↟ (ref-is-value ref) i neq

canonical-ref : ∀ {Σ gc pc A g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
  → Value V
  → Reference V Σ (Ref A of g)
canonical-ref (⊢addr eq) V-addr = Ref-addr eq
canonical-ref (⊢cast ⊢V) (V-cast v (I-ref c i₁ i₂)) =
  Ref-proxy (canonical-ref ⊢V v) (I-ref c i₁ i₂)
canonical-ref (⊢sub ⊢V sub) (V-addr↟ x) = {!!}
canonical-ref (⊢sub ⊢V sub) (V-cast↟ v x x₁) = {!!}
canonical-ref (⊢sub ⊢V sub) (V-const↟ x) = {!!}
canonical-ref (⊢sub ⊢V sub) (V-ƛ↟ x) = {!!}
canonical-ref (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref ⊢V v

-- data Constant : Term → Type → Set where
--   Const-base : ∀ {ι} {k : rep ι} {ℓ}
--       --------------------------------------- Constant
--     → Constant ($ k of ℓ) (` ι of l ℓ)

--   Const-sub : ∀ {M} {ι ℓ₁ ℓ₂} {ιℓ₁<:ιℓ₂ : ` ι of l ℓ₁ <: ` ι of l ℓ₂}
--     → Constant M (` ι of l ℓ₁)
--     → ` ι of l ℓ₁ ≢ ` ι of l ℓ₂
--       ------------------------------------------------------ ConstantSubtyping
--     → Constant (M ↟ ιℓ₁<:ιℓ₂) (` ι of l ℓ₂)

--   Const-inj : ∀ {M} {ι ℓ} {c : Cast (` ι of l ℓ) ⇒ (` ι of ⋆)}
--     → Constant M (` ι of l ℓ)
--       ------------------------------------------------------ ConstantInjection
--     → Constant (M ⟨ c ⟩) (` ι of ⋆)

-- canonical-const : ∀ {Σ gc pc ι g V}
--   → [] ; Σ ; gc ; pc ⊢ V ⦂ ` ι of g
--   → Value V
--     --------------------------
--   → Constant V (` ι of g)
-- canonical-const ⊢const V-const = Const-base
-- canonical-const (⊢cast ⊢V) (V-cast v (I-base-inj c)) =
--   case canonical-const ⊢V v of λ where
--   Const-base          → Const-inj Const-base
--   (Const-sub cst neq) → Const-inj (Const-sub cst neq)
-- canonical-const (⊢sub ⊢V (<:-ty <:-⋆ <:-ι)) (V-sub v neq)= contradiction refl neq
-- canonical-const (⊢sub ⊢V (<:-ty (<:-l ℓ≼) <:-ι)) (V-sub v neq) =
--   case canonical-const ⊢V v of λ where
--   Const-base           → Const-sub Const-base neq
--   (Const-sub cst neq′) → Const-sub (Const-sub cst neq′) neq
-- canonical-const (⊢sub-pc ⊢V _) v = canonical-const ⊢V v


-- canonical⋆ : ∀ {Γ Σ gc pc V T}
--   → Γ ; Σ ; gc ; pc ⊢ V ⦂ T of ⋆
--   → Value V
--   → ∃[ A ] Σ[ c ∈ Cast A ⇒ T of ⋆ ] ∃[ W ]
--        (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ A)
-- canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
--   ⟨ _ , c , W , refl , i , ⊢W ⟩
-- canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) (V-sub v neq) =
--   case canonical⋆ ⊢V v of λ where
--   ⟨ A , c , W , refl , i , ⊢W ⟩ →
--       ⟨ A , c , W , {!!} , i , ⊢W  ⟩
-- canonical⋆ (⊢sub-pc ⊢V gc<:gc′) v =
--   case canonical⋆ ⊢V v of λ where
--     ⟨ A , B , c , W , refl , i , ⊢W , B<:T⋆ ⟩ →
--       ⟨ A , B , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , B<:T⋆ ⟩

-- canonical-pc⋆ : ∀ {Γ Σ gc pc V A B g}
--   → Γ ; Σ ; gc ; pc ⊢ V ⦂ ⟦ ⋆ ⟧ A ⇒ B of g
--   → Value V
--   → ∃[ C ] ∃[ D ] Σ[ c ∈ Cast C ⇒ D ] ∃[ W ]
--        (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ C) × (D <: ⟦ ⋆ ⟧ A ⇒ B of g)
-- canonical-pc⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
--   ⟨ _ , _ , c , W , refl , i , ⊢W , <:-refl ⟩
-- canonical-pc⋆ (⊢sub ⊢V (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B))) v =
--   case canonical-pc⋆ ⊢V v of λ where
--     ⟨ C , D , c , W , refl , i , ⊢W , D<:A′→B′ ⟩ →
--       let D<:A→B = <:-trans D<:A′→B′ (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B)) in
--         ⟨ C , D , c , W , refl , i , ⊢W , D<:A→B ⟩
-- canonical-pc⋆ (⊢sub-pc ⊢V gc<:gc′) v =
--   case canonical-pc⋆ ⊢V v of λ where
--   ⟨ C , D , c , W , refl , i , ⊢W , D<:A→B ⟩ →
--     ⟨ C , D , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , D<:A→B ⟩

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



-- stamp-inert : ∀ {A B} → (c : Cast A ⇒ B) → Inert c → ∀ ℓ
--                       → (Cast (stamp A (l ℓ)) ⇒ (stamp B (l ℓ)))
-- stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι))
--             (I-base-inj _) ℓ =
--   cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι)
-- stamp-inert (cast (⟦ gc₁ ⟧ A ⇒ B of g₁) (⟦ gc₂ ⟧ C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
--             (I-fun _ I-label I-label) ℓ =
--   let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
--     cast (⟦ gc₁ ⟧ A ⇒ B of (g₁ ⋎̃ l ℓ)) (⟦ gc₂ ⟧ C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~
-- stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB))
--             (I-ref _ I-label I-label) ℓ =
--   let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
--     cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~

-- stamp-inert-inert : ∀ {A B ℓ} {c : Cast A ⇒ B} (i : Inert c) → Inert (stamp-inert c i ℓ)
-- stamp-inert-inert (I-base-inj c) = I-base-inj _
-- stamp-inert-inert (I-fun c I-label I-label) =
--   I-fun (stamp-inert c _ _) I-label I-label
-- stamp-inert-inert (I-ref c I-label I-label) =
--   I-ref (stamp-inert c _ _) I-label I-label

-- stamp-val : ∀ V → Value V → StaticLabel → Term
-- stamp-val (addr a of ℓ₁) V-addr ℓ = addr a of (ℓ₁ ⋎ ℓ)
-- stamp-val (ƛ⟦ pc ⟧ A ˙ N of ℓ₁) V-ƛ ℓ = ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ)
-- stamp-val ($ k of ℓ₁) V-const ℓ = $ k of (ℓ₁ ⋎ ℓ)
-- stamp-val (V ⟨ c ⟩) (V-cast v i) ℓ = stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩
-- stamp-val ● V-● ℓ = ●

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
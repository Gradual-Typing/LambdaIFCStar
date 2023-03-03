module CCExpSub.Values where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Types
open import Common.TypeBasedCast
open import Common.SubtypeCast
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_


data Err : Term → Set where
  E-error : ∀ {A} {e : Error} → Err (error A e)

{-
  non-classifying: true of low ⟨ Bool of low ↟ Bool of high ⟩
  classifying:     true of high
-}

data SimpleValue : Term → Set
data Value : Term → Set

data SimpleValue where
  V-const   : ∀ {ι} {k : rep ι} {ℓ} → SimpleValue ($ k of ℓ)
  V-addr    : ∀ {a ℓ} → SimpleValue (addr a of ℓ)
  V-ƛ       : ∀ {pc A N ℓ} → SimpleValue (ƛ⟦ pc ⟧ A ˙ N of ℓ)
  V-cast    : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → SimpleValue (V ⟨ c ⟩)

data Value where
  V-v   : ∀ {V} → SimpleValue V → Value V
  V-↟  : ∀ {A B V} {s : A ↟ B} → SimpleValue V → Value (V ↟⟨ s ⟩)
  V-●  : Value ●



stamp-inert : ∀ {A B} (c : Cast A ⇒ B)
  → Inert c → ∀ ℓ
  → (Cast (stamp A (l ℓ)) ⇒ (stamp B (l ℓ)))
stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι))
            (I-base-inj _) ℓ =
  cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι)
stamp-inert (cast (⟦ gc₁ ⟧ A ⇒ B of g₁) (⟦ gc₂ ⟧ C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
            (I-fun _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
  cast (⟦ gc₁ ⟧ A ⇒ B of (g₁ ⋎̃ l ℓ)) (⟦ gc₂ ⟧ C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~
stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB))
            (I-ref _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
  cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~

stamp-inert-inert : ∀ {A B ℓ} {c : Cast A ⇒ B} (i : Inert c) → Inert (stamp-inert c i ℓ)
stamp-inert-inert (I-base-inj c) = I-base-inj _
stamp-inert-inert (I-fun c I-label I-label) = I-fun (stamp-inert c _ _) I-label I-label
stamp-inert-inert (I-ref c I-label I-label) = I-ref (stamp-inert c _ _) I-label I-label

stamp-↟ : ∀ {A B} (s : A ↟ B) ℓ
  → stamp A (l ℓ) ↟ stamp B (l ℓ)
stamp-↟ (cast↟ A B A<:B) ℓ =
  cast↟ (stamp A (l ℓ)) (stamp B (l ℓ)) (stamp-<: A<:B <:ₗ-refl)

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val ($ k of ℓ₁) (V-v V-const) ℓ = $ k of (ℓ₁ ⋎ ℓ)
stamp-val (addr a of ℓ₁) (V-v V-addr) ℓ = addr a of (ℓ₁ ⋎ ℓ)
stamp-val (ƛ⟦ pc ⟧ A ˙ N of ℓ₁) (V-v V-ƛ) ℓ = ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ)
stamp-val (V ⟨ c ⟩) (V-v (V-cast v i)) ℓ = stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩
stamp-val ● V-● ℓ = ●
{- values with subtyping ↟ -}
stamp-val ($    k of ℓ₁ ↟⟨ s ⟩) (V-↟ V-const) ℓ₂ =
  $ k of (ℓ₁ ⋎ ℓ₂) ↟⟨ stamp-↟ s ℓ₂ ⟩
stamp-val (addr a of ℓ₁ ↟⟨ s ⟩) (V-↟ V-addr)  ℓ₂ =
  addr a of (ℓ₁ ⋎ ℓ₂) ↟⟨ stamp-↟ s ℓ₂ ⟩
stamp-val (ƛ⟦ pc ⟧ A ˙ N of ℓ₁ ↟⟨ s ⟩) (V-↟ V-ƛ) ℓ₂ =
  ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ₂) ↟⟨ stamp-↟ s ℓ₂ ⟩
stamp-val (V ⟨ c ⟩ ↟⟨ s ⟩) (V-↟ (V-cast v i)) ℓ =
  (stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩) ↟⟨ stamp-↟ s ℓ ⟩

-- A stamped value is value
stamp-val-value : ∀ {V ℓ} (v : Value V) → Value (stamp-val V v ℓ)
stamp-val-value (V-v V-const) = V-v V-const
stamp-val-value (V-↟ V-const) = V-↟ V-const
stamp-val-value (V-v V-addr) = V-v V-addr
stamp-val-value (V-↟ V-addr) = V-↟ V-addr
stamp-val-value (V-v V-ƛ) = V-v V-ƛ
stamp-val-value (V-↟ V-ƛ) = V-↟ V-ƛ
stamp-val-value (V-v (V-cast v i)) =
  V-v (V-cast (stamp-val-value v) (stamp-inert-inert i))
stamp-val-value (V-↟ (V-cast v i)) =
  V-↟ (V-cast (stamp-val-value v) (stamp-inert-inert i))
stamp-val-value V-● = V-●

stamp-inert-low : ∀ {A B} {c : Cast A ⇒ B} (i : Inert c)
  → stamp-inert c i low ≡ subst₂ (λ □₁ □₂ → Cast □₁ ⇒ □₂) (sym (stamp-low A)) (sym (stamp-low B)) c
stamp-inert-low (I-base-inj (cast (` ι of l ℓ) (` ι of ⋆) _ A~B)) with A~B
... | ~-ty (~⋆ {l low }) ~-ι = refl
... | ~-ty (~⋆ {l high}) ~-ι = refl
stamp-inert-low (I-fun (cast (⟦ gc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ gc₂ ⟧ C ⇒ D of g₂) p (~-ty ℓ₁~g₂ A→B~C→D)) I-label I-label)
  with ℓ₁  | g₂     | ℓ₁~g₂
... | high | ⋆      | ~⋆ = refl
... | high | l high | l~ = refl
... | low  | ⋆      | ~⋆ = refl
... | low  | l low  | l~ = refl
stamp-inert-low (I-ref (cast (Ref A of l ℓ₁) (Ref B of g₂) p (~-ty ℓ₁~g₂ RefA~RefB)) I-label I-label)
  with ℓ₁  | g₂     | ℓ₁~g₂
... | high | ⋆      | ~⋆ = refl
... | high | l high | l~ = refl
... | low  | ⋆      | ~⋆ = refl
... | low  | l low  | l~ = refl

stamp-↟-low : ∀ {A B} (s : A ↟ B) →
  stamp-↟ s low ≡ subst₂ (λ □₁ □₂ → □₁ ↟ □₂) (sym (stamp-low A)) (sym (stamp-low B)) s
stamp-↟-low (cast↟ (S of ⋆) (T of ⋆) (<:-ty <:-⋆ S<:T)) = refl
stamp-↟-low (cast↟ (S of l _) (T of l _) (<:-ty (<:-l l≼l) S<:T)) = refl
stamp-↟-low (cast↟ (S of l _) (T of l _) (<:-ty (<:-l l≼h) S<:T)) = refl
stamp-↟-low (cast↟ (S of l _) (T of l _) (<:-ty (<:-l h≼h) S<:T)) = refl

stamp-val-low : ∀ {V} (v : Value V) → stamp-val V v low ≡ V
stamp-val-low (V-v (V-const {ℓ = ℓ})) rewrite ℓ⋎low≡ℓ {ℓ} = refl
stamp-val-low (V-↟ {A} {B} {s = s} (V-const {ℓ = ℓ}))
  rewrite ℓ⋎low≡ℓ {ℓ} | stamp-↟-low s | stamp-low A | stamp-low B = refl
stamp-val-low (V-v (V-addr {ℓ = ℓ})) rewrite ℓ⋎low≡ℓ {ℓ} = refl
stamp-val-low (V-↟ {A} {B} {s = s} (V-addr {ℓ = ℓ}))
  rewrite ℓ⋎low≡ℓ {ℓ} | stamp-↟-low s | stamp-low A | stamp-low B = refl
stamp-val-low (V-v (V-ƛ {ℓ = ℓ})) rewrite ℓ⋎low≡ℓ {ℓ} = refl
stamp-val-low (V-↟ {A} {B} {s = s} (V-ƛ {ℓ = ℓ}))
  rewrite ℓ⋎low≡ℓ {ℓ} | stamp-↟-low s | stamp-low A | stamp-low B = refl
stamp-val-low (V-v (V-cast {A} {B} v i))
  rewrite stamp-val-low v | stamp-inert-low i | stamp-low A | stamp-low B = refl
stamp-val-low (V-↟ {A} {B₁} {s = s} (V-cast {B₂} {C} v i))
  rewrite stamp-val-low v | stamp-inert-low i | stamp-↟-low s
  | stamp-low A | stamp-low B₁ | stamp-low B₂ | stamp-low C = refl
stamp-val-low V-● = refl

⊢value-pc : ∀ {Γ Σ gc gc′ pc pc′ V A}
  → Γ ; Σ ; gc  ; pc ⊢ V ⦂ A
  → Value V
    ------------------------------------
  → Γ ; Σ ; gc′ ; pc′ ⊢ V ⦂ A
⊢value-pc (⊢addr eq) (V-v V-addr)       = ⊢addr eq
⊢value-pc (⊢lam ⊢N) (V-v V-ƛ)           = ⊢lam ⊢N
⊢value-pc ⊢const (V-v V-const)          = ⊢const
⊢value-pc (⊢cast ⊢V) (V-v (V-cast v i)) = ⊢cast (⊢value-pc ⊢V v)
⊢value-pc (⊢sub ⊢V) (V-↟ v)            = ⊢sub (⊢value-pc ⊢V (V-v v))
⊢value-pc (⊢sub-pc ⊢V gc<:gc′) v        = ⊢value-pc ⊢V v

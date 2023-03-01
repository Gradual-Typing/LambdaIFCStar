module CCExpSub.CanonicalForms where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.SubtypeCast
open import Common.TypeBasedCast
open import Memory.HeapContext
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_
open import CCExpSub.Values

open import CCExpSub.Uniqueness


data SimpFun : Term → HeapContext → Type → Set
data Fun : Term → HeapContext → Type → Set

data SimpFun where

  Fun-ƛ : ∀ {Σ A B N ℓᶜ ℓ}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
      ----------------------------------------------------- Lambda
    → SimpFun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) Σ (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ)

  Fun-proxy : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ g₁ g₂ V}
                {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
      ----------------------------------------------------- Function Proxy
    → SimpFun (V ⟨ c ⟩) Σ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)

data Fun where

  Fun-fun : ∀ {Σ A V} → SimpFun V Σ A → Fun V Σ A

  Fun-↟ : ∀ {Σ A B V} {s : A ↟ B} → SimpFun V Σ A → Fun (V ↟⟨ s ⟩) Σ B

-- Sanity check
fun-is-value : ∀ {Σ V gc A B g}
  → Fun V Σ (⟦ gc ⟧ A ⇒ B of g)
  → Value V
fun-is-value (Fun-fun (Fun-ƛ     _))         = V-val V-ƛ
fun-is-value (Fun-fun (Fun-proxy fun i))     = V-val (V-cast (fun-is-value fun) i)
fun-is-value (Fun-↟  (Fun-ƛ _))             = V-↟  V-ƛ
fun-is-value (Fun-↟  (Fun-proxy fun i))     = V-↟  (V-cast (fun-is-value fun) i)

-- Canonical form of value of function type
canonical-fun : ∀ {Σ gc pc A B g gᶜ V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gᶜ ⟧ A ⇒ B of g
  → Value V
    -------------------------------
  → Fun V Σ (⟦ gᶜ ⟧ A ⇒ B of g)
canonical-fun (⊢lam ⊢N) (V-val V-ƛ) = Fun-fun (Fun-ƛ ⊢N)
canonical-fun (⊢cast ⊢V) (V-val (V-cast v (I-fun c i₁ i₂))) =
  Fun-fun (Fun-proxy (canonical-fun ⊢V v) (I-fun c i₁ i₂))
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-ƛ) =
  case canonical-fun ⊢V (V-val V-ƛ) of λ where
  (Fun-fun (Fun-ƛ ⊢N)) → Fun-↟ (Fun-ƛ ⊢N)
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ (V-cast v i)) =
  case canonical-fun ⊢V (V-val (V-cast v i)) of λ where
  (Fun-fun (Fun-proxy fun i)) → Fun-↟ (Fun-proxy fun i)
canonical-fun {gc = gc} {pc} (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-const) =
  case uniqueness ⊢V (⊢const {gc = gc} {pc}) of λ where ()
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-addr) =
  case canonical-fun ⊢V (V-val V-addr) of λ where
  (Fun-fun ())
canonical-fun (⊢sub-pc ⊢V gc<:gc′) v = canonical-fun ⊢V v

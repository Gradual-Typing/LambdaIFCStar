module CCExpSub.Values where

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

open import CCExpSub.Uniqueness


data Err : Term → Set where
  E-error : ∀ {A} {e : Error} → Err (error A e)

data Value : Term → Set where
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-const↟ : ∀ {A B} {ι} {k : rep ι} {ℓ} {A<:B : A <: B}
    → A ≢ B → Value ($ k of ℓ ↟ A<:B)
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-addr↟ : ∀ {A B} {a ℓ} {A<:B : A <: B}
    → A ≢ B → Value (addr a of ℓ ↟ A<:B)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ)
  V-ƛ↟ : ∀ {A₁ A₂} {pc A N ℓ} {A₁<:A₂ : A₁ <: A₂}
    → A₁ ≢ A₂ → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ ↟ A₁<:A₂)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)
  V-cast↟ : ∀ {A B C V} {c : Cast A ⇒ B} {B<:C : B <: C}
    → Value V → Inert c → B ≢ C → Value ((V ⟨ c ⟩) ↟ B<:C)
  V-● : Value ●

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

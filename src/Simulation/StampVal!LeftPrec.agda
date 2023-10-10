module Simulation.StampVal!LeftPrec where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import CoercionExpr.Precision
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Precision
open import CC2.Stamping public


stamp-val!-left-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ V V′} {ℓ ℓ′}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → (v  : Value V )
  → (v′ : Value V′)
  → ℓ ≼ ℓ′
    ------------------------------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val! V v A ℓ ⊑ stamp-val V′ v′ A′ ℓ′
        ⇐ stamp A ⋆ ⊑ stamp A′ (l ℓ′)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw x) (V-raw x₁) l≼l = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {n = n} {low} {ℓ̂} a b) (V-raw V-addr) (V-raw V-addr) l≼h =
  let A⊑A′ = ⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ a b) in
  ⊑-cast (⊑-addr a b) (⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {ℓ = high} a b) (V-raw V-addr) (V-raw V-addr) l≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-lam g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) l≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ ⊑-const (V-raw V-const) (V-raw V-const) l≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw x) (V-raw x₁) h≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw x) (V-cast x₁ x₂) ℓ≼ℓ′ = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast x x₁) v′ ℓ≼ℓ′ = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)

module CC2.StampValPrec where

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


stamp-val-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ V V′} {ℓ}
  → A ⊑ A′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → (v  : Value V )
  → (v′ : Value V′)
    ------------------------------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val V v A ℓ ⊑ stamp-val V′ v′ A′ ℓ
        ⇐ stamp A (l ℓ) ⊑ stamp A′ (l ℓ)
stamp-val-prec {A = T of ⋆} {ℓ = high} A⊑A′ prec (V-raw x) (V-raw x₁) = {!!}
stamp-val-prec {A = .(` _) of l high} {ℓ = high} A⊑A′ ⊑-const (V-raw x) (V-raw x₁) = ⊑-const
stamp-val-prec {A = .(Ref (_ of l _)) of l high} {ℓ = high} A⊑A′ (⊑-addr a b) (V-raw _) (V-raw _) = ⊑-addr a b
stamp-val-prec {A = .(⟦ _ ⟧ _ ⇒ _) of l high} {ℓ = high} A⊑A′ (⊑-lam x y z) (V-raw _) (V-raw _) = ⊑-lam x y z
stamp-val-prec {A = .(` _) of l low} {ℓ = high} A⊑A′ ⊑-const (V-raw x) (V-raw x₁) = ⊑-cast ⊑-const (⊑-base (prec-refl _))
stamp-val-prec {A = .(Ref (_ of l _)) of l low} {ℓ = high} (⊑-ty l⊑l (⊑-ref A⊑A′)) (⊑-addr a b) (V-raw x) (V-raw x₁) =
  ⊑-cast (⊑-addr a b) (⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (prec-refl _))
stamp-val-prec {A = .(⟦ _ ⟧ _ ⇒ _) of l low} {ℓ = high} (⊑-ty _ (⊑-fun g⊑g′ A⊑A′ B⊑B′)) (⊑-lam x y z) (V-raw _) (V-raw _) =
  ⊑-cast (⊑-lam x y z) (⊑-fun (⊑-id g⊑g′) (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) (prec-refl _))
stamp-val-prec {A = A} {A′} {ℓ = low} A⊑A′ V⊑V′ (V-raw _) (V-raw _)
  rewrite stamp-low A | stamp-low A′ = V⊑V′
stamp-val-prec {A = T of ⋆} {ℓ = high} A⊑A′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) = {!!}
stamp-val-prec {A = T of l high} {ℓ = high} A⊑A′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) =
  ⊑-castr V⊑V′ (stamp-ir-high-prec-right A⊑c′ i′)
stamp-val-prec {A = T of l low} {ℓ = high} A⊑A′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) = {!!}
stamp-val-prec {A = A} {A′} {ℓ = low} A⊑A′ (⊑-castr V⊑V′ A⊑c′) (V-raw x) (V-cast x₁ i)
  rewrite stamp-low A with i
... | ir-base {g = g} _ _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
... | ir-ref {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
... | ir-fun {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
stamp-val-prec {ℓ = ℓ} A⊑A′ prec (V-cast x x₁) (V-raw x₂) = {!!}
stamp-val-prec {ℓ = ℓ} A⊑A′ prec (V-cast x x₁) (V-cast x₂ x₃) = {!!}
stamp-val-prec _ V⊑W v V-● = contradiction V⊑W (_ ⋤●)
stamp-val-prec _ V⊑W V-● w = contradiction V⊑W (●⋤ _)

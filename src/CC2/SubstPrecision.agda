module CC2.SubstPrecision where

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

open import Syntax
open import Common.Utils
open import Memory.HeapContext
open import CoercionExpr.Precision using (coerce⇒⋆-prec)
open import LabelExpr.CatchUp renaming (catchup to catchupₑ)
open import LabelExpr.Security
open import CC2.Statics
open import CC2.Precision
open import CC2.SubstPreserve -- using (_⦂_⇒_; _⊢_⦂_⇒_)


_;_⊢_⊑ˢ_⦂_⇒_,_⇒_ : ∀ (Σ Σ′ : HeapContext) → (σ σ′ : Subst) → (Γ Δ Γ′ Δ′ : Context) → Set
Σ ; Σ′ ⊢ σ ⊑ˢ σ′ ⦂ Γ ⇒ Δ , Γ′ ⇒ Δ′ =
  (Σ ⊢ σ ⦂ Γ ⇒ Δ) → (Σ′ ⊢ σ′ ⦂ Γ′ ⇒ Δ′) →
  ∀ {x A A′}
  → Γ  ∋ x ⦂ A
  → Γ′ ∋ x ⦂ A′
  → (∀ {gc gc′ ℓv ℓv′} → Δ ; Δ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ σ x ⊑ σ′ x ⇐ A ⊑ A′)


rename-pres-⊑ : ∀ {Γ Γ′ Δ Δ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′} {M M′} {ρ : Rename}
  → ρ ⦂ Γ  ⇒ Δ
  → ρ ⦂ Γ′ ⇒ Δ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    -----------------------------------------------------------------------------
  → Δ ; Δ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ rename ρ M ⊑ rename ρ M′ ⇐ A ⊑ A′
rename-pres-⊑ ⊢ρ ⊢ρ′ ⊑-const = ⊑-const
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-var Γ∋x⦂A Γ′∋x⦂A′) = ⊑-var (⊢ρ Γ∋x⦂A) (⊢ρ′ Γ′∋x⦂A′)
rename-pres-⊑ {ρ = ρ} ⊢ρ ⊢ρ′ (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) =
  ⊑-lam gc⊑gc′ A⊑A′ (rename-pres-⊑ {ρ = ext ρ}
                        (λ {x} ∋x → ext-pres ⊢ρ  {x} ∋x)
                        (λ {x} ∋x → ext-pres ⊢ρ′ {x} ∋x) N⊑N′)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-addr x y) = ⊑-addr x y
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-app L⊑L′ M⊑M′ eq₁ eq₂) =
  ⊑-app (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-app! L⊑L′ M⊑M′ eq₁ eq₂) =
  ⊑-app! (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-app!l L⊑L′ M⊑M′ eq₁ eq₂) =
  ⊑-app!l (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-if L⊑L′ M⊑M′ N⊑N′ eq₁ eq₂) =
  ⊑-if (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) (rename-pres-⊑ ⊢ρ ⊢ρ′ N⊑N′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-if! L⊑L′ M⊑M′ N⊑N′ eq₁ eq₂) =
  ⊑-if! (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) (rename-pres-⊑ ⊢ρ ⊢ρ′ N⊑N′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-if!l L⊑L′ M⊑M′ N⊑N′ eq₁ eq₂) =
  ⊑-if!l (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) (rename-pres-⊑ ⊢ρ ⊢ρ′ N⊑N′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-let M⊑M′ N⊑N′) =
  ⊑-let (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′)
        (rename-pres-⊑ (λ {x} ∋x → ext-pres ⊢ρ {x} ∋x) (λ {x} ∋x → ext-pres ⊢ρ′ {x} ∋x) N⊑N′)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-ref M⊑M′ x) =
  ⊑-ref (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) x
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-ref? M⊑M′) =
  ⊑-ref? (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-ref?l M⊑M′ x) =
  ⊑-ref?l (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) x
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-deref M⊑M′ eq₁ eq₂) =
  ⊑-deref (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-deref! M⊑M′ eq₁ eq₂) =
  ⊑-deref! (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-deref!l M⊑M′ eq₁ eq₂) =
  ⊑-deref!l (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-assign L⊑L′ M⊑M′ x y) =
  ⊑-assign (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) x y
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-assign? L⊑L′ M⊑M′) =
  ⊑-assign? (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′)
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-assign?l L⊑L′ M⊑M′ x y) =
  ⊑-assign?l (rename-pres-⊑ ⊢ρ ⊢ρ′ L⊑L′) (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) x y
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-prot M⊑M′ PC⊑PC′ x y eq₁ eq₂) =
  ⊑-prot (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) PC⊑PC′ x y eq₁ eq₂
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-prot! M⊑M′ PC⊑PC′ x y eq₁ eq₂ z) =
  ⊑-prot! (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) PC⊑PC′ x y eq₁ eq₂ z
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-prot!l M⊑M′ PC⊑PC′ x y eq₁ eq₂ z) =
  ⊑-prot!l (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) PC⊑PC′ x y eq₁ eq₂ z
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-cast M⊑M′ c⊑c′) = ⊑-cast (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) c⊑c′
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-castl M⊑M′ c⊑A′) = ⊑-castl (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) c⊑A′
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-castr M⊑M′ A⊑c′) = ⊑-castr (rename-pres-⊑ ⊢ρ ⊢ρ′ M⊑M′) A⊑c′
rename-pres-⊑ ⊢ρ ⊢ρ′ (⊑-blame ⊢M A⊑A′) = ⊑-blame (rename-pres ⊢M ⊢ρ) A⊑A′

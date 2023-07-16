module CC2.CatchUp where

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
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision

catchup : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M V′ μ PC} {A A′}
  → Value V′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ V′ ⇐ A ⊑ A′
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
    -------------------------------------------------------------------
  → ∃[ V ] (Value V) ×
       (M ∣ μ ∣ PC —↠ V ∣ μ) ×
       (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′)
catchup (V-raw x) ⊑-const Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup (V-raw x) (⊑-addr x₁ x₂) Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup (V-raw x) (⊑-lam x₁ x₂ x₃) Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup {μ = μ} {PC} (V-raw v′) (⊑-castl {c = c} M⊑V′ c⊑A′) Γ⊑Γ′ Σ⊑Σ′
--   with cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑V′
-- ... | ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ | v′ | c
... | ⟨ V , V-raw V-const , M↠V , ⊑-const ⟩ | V-const | cast (id ι) c̅ =
  {!!}
... | ⟨ V , V-raw V-addr , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-raw V-ƛ , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-cast v i , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-● , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
catchup (V-cast x x₁) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup V-● M⊑V′ Γ⊑Γ′ Σ⊑Σ′ = {!!}

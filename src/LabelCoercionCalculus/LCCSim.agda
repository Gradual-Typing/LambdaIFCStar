module LabelCoercionCalculus.LCCSim where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.Precision
open import LabelCoercionCalculus.LabelCC

open import LabelCoercionCalculus.SyntacComp
open import LabelCoercionCalculus.LCCCatchUp


sim : ∀ {g g′} {M M′ N′} {g⊑g′ : g ⊑ₗ g′}
  → ⊢ M ⊑ M′ ⇐ g⊑g′
  → M′ —→ₑ N′
    ---------------------------------------------
  → ∃[ N ] (M —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g⊑g′)


sim-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′ N′} {g₁⊑g₁′ : g₁ ⊑ₗ g₁′} {g₂⊑g₂′ : g₂ ⊑ₗ g₂′}
             {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢ M ⊑ M′ ⇐ g₁⊑g₁′
  → ⊢ c̅ ⊑ c̅′
  → M′ ⟪ c̅′ ⟫ —→ₑ N′
    ---------------------------------------------------
  → ∃[ N ] (M ⟪ c̅ ⟫ —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g₂⊑g₂′)
sim-cast M⊑M′ c̅⊑c̅′ (ξ R) = {!!}
sim-cast M⊑M′ c̅⊑c̅′ ξ-blame = {!!}
sim-cast M⊑M′ c̅⊑c̅′ β-id = {!!}
sim-cast M⊑M′ c̅⊑c̅′ (cast x x₁) = {!!}
sim-cast M⊑M′ c̅⊑c̅′ (blame x) = {!!}
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} M⊑M′ c̅⊑c̅′ (comp i′)
  with catchup {g⊑g′ = g₁⊑g₁′} (v-cast i′) M⊑M′
... | ⟨ l ℓ , v-l , M↠V , prec ⟩  = {!!}
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , prec ⟩  = {!!}


sim (⊑-cast M⊑M′ x) M′→N′ = {!!}
sim (⊑-castl M⊑M′ x) M′→N′ = {!!}
sim (⊑-castr M⊑M′ x) M′→N′ = {!!}

module LabelExpr.CatchUpBack where

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
open import LabelExpr.LabelExpr


data InSync : ∀ (M N : LExpr) → Set where

  v-v : ∀ {g g′} {M V} {g⊑g′ : g ⊑ₗ g′}
    → LVal V
    → ⊢ M ⊑ V ⇐ g⊑g′
      -------------------
    → InSync M V

  v-⊥ : ∀ {g g′} {M p} {g⊑g′ : g ⊑ₗ g′}
    → ⊢ M ⊑ blame p ⇐ g⊑g′
      --------------------------
    → InSync M (blame p)


catchup-back : ∀ {g g′} {V M′} {g⊑g′ : g ⊑ₗ g′}
  → LVal V
  → ⊢ V ⊑ M′ ⇐ g⊑g′
  → ∃[ N′ ] (M′ —↠ₑ N′) × (InSync V N′)
catchup-back v-l ⊑-l = ⟨ l _ , _ ∎ , v-v {g⊑g′ = l⊑l} v-l ⊑-l ⟩
catchup-back (v-cast i) (⊑-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} V⊑M′ c̅⊑c̅′)
  with catchup-back {g⊑g′ = g₁⊑g₁′} v-l V⊑M′
... | ⟨ blame p , M′↠⊥ , v-⊥ V⊑⊥ ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    v-⊥ {g⊑g′ = g₂⊑g₂′} (⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢l)) ⟩
... | ⟨ V′ , M′↠V′ , v-v v′ V⊑V′ ⟩ = {!!}
catchup-back v (⊑-castl V⊑M′ x) = {!!}
catchup-back v (⊑-castr V⊑M′ x) = {!!}
catchup-back v (⊑-blame x) = {!!}

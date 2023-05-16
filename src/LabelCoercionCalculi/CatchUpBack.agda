module LabelCoercionCalculi.CatchUpBack where

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
open import LabelCoercionCalculi.CoercionExp
open import LabelCoercionCalculi.Precision

data InSync : ∀ {g₁ g₁′ g₂ g₂′} (c̅₁ : CoercionExp g₁ ⇒ g₂) (c̅₂ : CoercionExp g₁′ ⇒ g₂′) → Set where
  v-v : ∀ {g₁ g₁′ g₂ g₂′} {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅₂ : CoercionExp g₁′ ⇒ g₂′}
    → 𝒱 c̅₂
    → ⊢ c̅₁ ⊑ c̅₂
    → InSync c̅₁ c̅₂

  v-⊥ : ∀ {g₁ g₁′ g₂ g₂′} {c̅₁ : CoercionExp g₁ ⇒ g₂} {p}
    → ⊢ c̅₁ ⊑ ⊥ g₁′ g₂′ p
    → InSync c̅₁ (⊥ g₁′ g₂′ p)

catchup-back : ∀ {ℓ ℓ′ g g′} (c̅ : CoercionExp l ℓ ⇒ g) (c̅₁′ : CoercionExp l ℓ′ ⇒ g′)
  → 𝒱 c̅
  → ⊢ c̅ ⊑ c̅₁′
  → ∃[ c̅₂′ ] (c̅₁′ —↠ c̅₂′) × (InSync c̅ c̅₂′)
catchup-back .(id (l _)) c̅₁′ id leq = {!!}

catchup-back (c̅ ⨾ ℓ !) (c̅′ ⨾ id (l ℓ)) (inj v) (⊑-cast c̅⊑c̅′ l⊑l ⋆⊑)
  with catchup-back _ _ v c̅⊑c̅′
... | ⟨ c̅₂′ , c̅′↠c̅₂′ , c̅-c̅₂′ ⟩ = {!!}
catchup-back (c̅ ⨾ ℓ !) (c̅′ ⨾ ℓ !) (inj v) (⊑-cast c̅⊑c̅′ l⊑l ⋆⊑)
  with catchup-back _ _ v c̅⊑c̅′
... | ⟨ c̅₂′ , c̅′↠c̅₂′ , v-v v x ⟩ =
  ⟨ c̅₂′ ⨾ ℓ ! , plug-cong c̅′↠c̅₂′ , v-v (inj v) (⊑-cast x l⊑l ⋆⊑) ⟩
... | ⟨ c̅₂′ , c̅′↠c̅₂′ , v-⊥ x ⟩
  with prec→⊑ _ _ c̅⊑c̅′
... | ⟨ ℓ⊑ℓ′ , _ ⟩ =
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅′↠c̅₂′) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , v-⊥ (⊑-⊥ ℓ⊑ℓ′ ⋆⊑) ⟩
catchup-back (c̅ ⨾ ℓ !) (c̅′ ⨾ ↑) (inj v) (⊑-cast c̅⊑c̅′ l⊑l ⋆⊑)
  with catchup-back _ _ v c̅⊑c̅′
... | ⟨ c̅₂′ , c̅′↠c̅₂′ , c̅-c̅₂′ ⟩ = {!!}

catchup-back (c̅ ⨾ (ℓ !)) c̅₁′ (inj v) (⊑-castl leq x x₁) = {!!}
catchup-back (c̅ ⨾ (ℓ !)) .(_ ⨾ _) (inj v) (⊑-castr leq x x₁) = {!!}
catchup-back (c̅ ⨾ (ℓ !)) .(⊥ (l _) _ _) (inj v) (⊑-⊥ x x₁) = {!!}
catchup-back (c̅ ⨾ ↑) c̅₁′ (up v) leq = {!!}

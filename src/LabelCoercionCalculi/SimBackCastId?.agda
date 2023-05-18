module LabelCoercionCalculi.SimBackCastId? where

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
open import LabelCoercionCalculi.CatchUpBack


sim-back-cast-id? : ∀ {ℓ₁ ℓ₂ ℓ′ g′}
    {c̅₁ : CoercionExp l ℓ₁ ⇒ l ℓ₂} {c̅₁′ : CoercionExp l ℓ′ ⇒ g′}
    {c′ : ⊢ g′ ⇒ l ℓ₂}
  → ⊢ c̅₁ ⨾ ℓ₂ ! ⊑ c̅₁′
  → 𝒱 c̅₁
    --------------------------------------------
  → ∃[ c̅₂′ ] ∃[ c̅₂ ] (c̅₁′ ⨾ c′ —↠ c̅₂′) × (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-back-cast-id? {c′ = id .(l _)} c̅₁⨾!⊑c̅₁′ v = {!!}
sim-back-cast-id? {c′ = ↑} c̅₁⨾!⊑c̅₁′ v = {!!}
sim-back-cast-id? {c′ = low ?? p} c̅₁⨾!⊑c̅₁′ v
  with catchup-back _ _ (inj v) c̅₁⨾!⊑c̅₁′
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-v (inj v′) x ⟩ = {!!}
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-⊥ x ⟩ = {!!}
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ c̅′ ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj v′) x ⟩ = {!!}
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj v′) x ⟩ = {!!}
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-⊥ x ⟩ = {!!}
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ (up id)
  with catchup-back _ _ (inj (up id)) c̅₁⨾!⊑c̅₁′
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-v v′ x ⟩ = {!!}
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-⊥ x ⟩ = {!!}

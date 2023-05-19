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
sim-back-cast-id? {c′ = low ?? p} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj id) x ⟩ =
  ⟨ id (l low) , _ , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ (low !) ⨾ (low ?? p) —→⟨ ?-id id ⟩ id (l low) ∎) , _ ∎ , ⊑-id l⊑l ⟩
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-castr (⊑-castl _ () _) y z) ⟩
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj (up id)) (⊑-castr _ _ _) ⟩ =
  ⟨ ⊥ _ _ p , _ , ↠-trans (plug-cong c̅₁′↠c̅₂′) (id (l low) ⨾ ↑ ⨾ (high !) ⨾ (low ?? p) —→⟨ ?-⊥ (up id) ⟩
                                                 ⊥ (l low) (l low) p ∎) , _ ∎ , ⊑-⊥ l⊑l l⊑l ⟩
... | ⟨ c̅₂′ , c̅₁′↠⊥ , v-⊥ x ⟩ with prec→⊑ _ _ x
... | ⟨ l⊑l , _ ⟩ =
  ⟨ ⊥ _ _ _ , _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , _ ∎ , ⊑-⊥ l⊑l l⊑l ⟩
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ c̅′ ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj v′) x ⟩ = {!!}
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj v′) x ⟩ = {!!}
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-⊥ x ⟩ = {!!}
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ (up id)
  with catchup-back _ _ (inj (up id)) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj id) x ⟩ =
  ⟨ id (l low) ⨾ ↑ , _ , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ (low !) ⨾ (high ?? p) —→⟨ ?-↑ id ⟩ id (l low) ⨾ ↑ ∎) , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-cast (⊑-castl _ () _) _ _) ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-castr (⊑-castl (⊑-castl _ () _) _ _) _ _) ⟩
... | ⟨ id (l low) ⨾ ↑ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj (up id)) x ⟩ =
  ⟨ id (l low) ⨾ ↑ , _ , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ ↑ ⨾ (high !) ⨾ (high ?? p) —→⟨ ?-id (up id) ⟩ id (l low) ⨾ ↑ ∎) , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ c̅₂′ , c̅₁′↠c̅₂′ , v-⊥ x ⟩ = {!!}

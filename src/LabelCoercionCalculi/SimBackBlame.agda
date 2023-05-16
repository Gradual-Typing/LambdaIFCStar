module LabelCoercionCalculi.SimBackBlame where

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

sim-back-blame : ∀ {ℓ ℓ′ g g′} {c̅′ : CoercionExp (l ℓ′) ⇒ g′} {p}
  → ⊢ ⊥ (l ℓ) g p ⊑ c̅′
  → ∃[ q ] (c̅′ —↠ ⊥ (l ℓ′) g′ q) × (⊢ ⊥ (l ℓ) g p ⊑ ⊥ (l ℓ′) g′ q)
sim-back-blame (⊑-castr ⊥⊑c̅′ x g⊑g′)
  with sim-back-blame ⊥⊑c̅′ | prec→⊑ _ _ ⊥⊑c̅′
... | ⟨ q , c̅′↠⊥ , leq ⟩ | ⟨ ℓ⊑ℓ′ , _ ⟩ =
  ⟨ q , ↠-trans (plug-cong c̅′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ g⊑g′ ⟩
sim-back-blame (⊑-⊥ ℓ⊑ℓ′ g⊑g′) = ⟨ _ , _ ∎ , ⊑-⊥ ℓ⊑ℓ′ g⊑g′ ⟩

collide-castr : ∀ {ℓ ℓ′ g′} {c̅ : CoercionExp l ℓ ⇒ l high} {c̅′ : CoercionExp l ℓ′ ⇒ g′} {c′ : ⊢ g′ ⇒ l low} {p}
  → ⊢ c̅ ⨾ high ! ⊑ c̅′
  → 𝒱 c̅
  → ∃[ q ] (c̅′ ⨾ c′ —↠ ⊥ (l ℓ′) (l low) q) × (⊢ ⊥ (l ℓ) (l low) p ⊑ ⊥ (l ℓ′) (l low) q)
collide-castr (⊑-cast leq l⊑l ⋆⊑) v = {!!}
collide-castr (⊑-castl leq x x₁) v = {!!}
collide-castr (⊑-castr leq x x₁) v = {!!}
collide-castr (⊑-⊥ x x₁) v = {!!}


sim-back-collide : ∀ {ℓ ℓ′} {c̅ : CoercionExp l ℓ ⇒ l high} {c̅′ : CoercionExp l ℓ′ ⇒ l low} {p}
  → ⊢ c̅ ⨾ high ! ⊑ c̅′
  → 𝒱 c̅
  → ∃[ q ] (c̅′ —↠ ⊥ (l ℓ′) (l low) q) × (⊢ ⊥ (l ℓ) (l low) p ⊑ ⊥ (l ℓ′) (l low) q)
sim-back-collide (⊑-cast {c′ = ()} leq l⊑l ⋆⊑) v
sim-back-collide (⊑-castr {c′ = c′} prec ⋆⊑ ⋆⊑) v = {!!}
sim-back-collide (⊑-⊥ l⊑l ⋆⊑) v = ⟨ _ , ⊥ _ _ _ ∎ , ⊑-⊥ l⊑l l⊑l ⟩

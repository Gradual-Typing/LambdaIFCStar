module LabelCoercionCalculi.SimBackCast↑ where

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


sim-back-cast-↑ : ∀ {ℓ ℓ′ g′}
    {c̅₁ : CoercionExp l ℓ ⇒ l low} {c̅₁′ : CoercionExp l ℓ′ ⇒ g′}
    {c′ : ⊢ g′ ⇒ l high}
  → ⊢ c̅₁ ⨾ low ! ⊑ c̅₁′
  → 𝒱 c̅₁
    --------------------------------------------
  → ∃[ c̅₂′ ] ∃[ c̅₂ ] (c̅₁′ ⨾ c′ —↠ c̅₂′) × (c̅₁ ⨾ ↑ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-back-cast-↑ {c′ = c′} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′ | c′
... | ⟨ id (l low) , c̅₁⨾!↠c̅₂′ , v-v id x ⟩ | ↑ =
  ⟨ id (l low) ⨾ ↑ , _ , plug-cong c̅₁⨾!↠c̅₂′ , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ id (l high) , c̅₁⨾!↠c̅₂′ , v-v id x ⟩ | c′ =
  case prec→⊑ _ _ x of λ where ⟨ () , _ ⟩
... | ⟨ id (l low) ⨾ ↑ , c̅₁⨾!↠c̅₂′ , v-v (up id) x ⟩ | id (l high) =
  ⟨ id (l low) ⨾ ↑ , _ , ↠-trans (plug-cong c̅₁⨾!↠c̅₂′)
    (_ —→⟨ id (up id) ⟩ id (l low) ⨾ ↑ ∎) , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ id (l low) ⨾ low ! , c̅₁⨾!↠c̅₂′ , v-v (inj id) x ⟩ | high ?? _ =
  ⟨ id (l low) ⨾ ↑ , _ , ↠-trans (plug-cong c̅₁⨾!↠c̅₂′)
    (id (l low) ⨾ (low !) ⨾ (high ?? _) —→⟨ ?-↑ id ⟩ id (l low) ⨾ ↑ ∎) , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁⨾!↠c̅₂′ , v-v (inj id) x ⟩ | high ?? _ =
  case prec→⊑ _ _ x of λ where ⟨ () , _ ⟩
... | ⟨ id (l low) ⨾ ↑ ⨾ high ! , c̅₁⨾!↠c̅₂′ , v-v (inj (up id)) x ⟩ | high ?? _ =
  ⟨ id (l low) ⨾ ↑ , _ , ↠-trans (plug-cong c̅₁⨾!↠c̅₂′)
    (_ —→⟨ ?-id (up id) ⟩ id (l low) ⨾ ↑ ∎) , _ ∎ , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ ⊥ _ _ _ , c̅₁⨾!↠⊥ , v-⊥ x ⟩ | _ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ x in
  ⟨ ⊥ _ _ _ , _ , ↠-trans (plug-cong c̅₁⨾!↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , _ ∎ , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩

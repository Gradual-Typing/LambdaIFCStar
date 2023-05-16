module LabelCoercionCalculi.SimBack where

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
open import LabelCoercionCalculi.SimBackLemmas


sim-back : ∀ {ℓ ℓ′ g g′} {c̅₁ c̅₂ : CoercionExp (l ℓ) ⇒ g} {c̅₁′ : CoercionExp (l ℓ′) ⇒ g′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → c̅₁ —→ c̅₂
    -----------------------------------------------------------------
  → ∃[ c̅₂′ ] ∃[ c̅₃ ] (c̅₁′ —↠ c̅₂′) × (c̅₂ —↠ c̅₃) × (⊢ c̅₃ ⊑ c̅₂′)


sim-back-castl : ∀ {ℓ ℓ′ g₁ g₂ g′} {c̅ : CoercionExp (l ℓ) ⇒ g₁} {c : ⊢ g₁ ⇒ g₂} {c̅₁} {c̅₁′ : CoercionExp (l ℓ′) ⇒ g′}
  → ⊢ c̅ ⊑ c̅₁′
  → g₁ ⊑ₗ g′ → g₂ ⊑ₗ g′  {- c ⊑ g′ -}
  → c̅ ⨾ c —→ c̅₁
    -----------------------------------------------------------------
  → ∃[ c̅₂′ ] ∃[ c̅₂ ] (c̅₁′ —↠ c̅₂′) × (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-back-castl c̅⊑c̅₁′ g₁⊑g′ g₂⊑g′ (ξ c̅→c̅₁)
  with sim-back c̅⊑c̅₁′ c̅→c̅₁
... | ⟨ c̅₂′ , c̅₂ , c̅₁′↠c̅₂′ , c̅₁↠c̅₂ , c̅₂⊑c̅₂′ ⟩ =
  ⟨ c̅₂′ , c̅₂ ⨾ _ , c̅₁′↠c̅₂′ , plug-cong c̅₁↠c̅₂ , ⊑-castl c̅₂⊑c̅₂′ g₁⊑g′ g₂⊑g′ ⟩
sim-back-castl ⊥⊑c̅₁′ g₁⊑g′ g₂⊑g′ ξ-⊥
  with sim-back-blame ⊥⊑c̅₁′ | prec→⊑ _ _ ⊥⊑c̅₁′
... | ⟨ q , c̅₁′↠⊥ , ⊥⊑⊥ ⟩ | ⟨ ℓ⊑ℓ′ , _ ⟩ =
  ⟨ ⊥ _ _ q , _ , c̅₁′↠⊥ , _ ∎ , ⊑-⊥ ℓ⊑ℓ′ g₂⊑g′ ⟩
sim-back-castl c̅⊑c̅₁′ g₁⊑g′ g₂⊑g′ (id v) = {!!}
sim-back-castl c̅⊑c̅₁′ g₁⊑g′ g₂⊑g′ (?-id x) = {!!}
sim-back-castl c̅⊑c̅₁′ g₁⊑g′ g₂⊑g′ (?-↑ x) = {!!}
sim-back-castl c̅⨾!⊑c̅₁′ ⋆⊑ l⊑l (?-⊥ v)
  with catchup-back _ _ (inj v) c̅⨾!⊑c̅₁′
... | ⟨ id (l low) , c̅₁′↠c̅₂′ , v-v id (⊑-castl _ () _) ⟩
... | ⟨ ⊥ _ _ p , c̅₁′↠⊥ , v-⊥ _ ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ p , _ , c̅₁′↠⊥ , _ ∎ , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩


sim-back (⊑-cast c̅⊑c̅′ g₁⊑g₁′ g⊑g′) c̅₁→c̅₂   = {!!}
sim-back (⊑-castl c̅⊑c̅₁′ g₁⊑g′ g⊑g′) c̅⨾c→c̅₂ = sim-back-castl c̅⊑c̅₁′ g₁⊑g′ g⊑g′ c̅⨾c→c̅₂
sim-back (⊑-castr {c′ = c′} c̅₁⊑c̅′ g⊑g₁′ g⊑g′) c̅₁→c̅₂
  with sim-back c̅₁⊑c̅′ c̅₁→c̅₂
... | ⟨ c̅₂′ , c̅₃ , c̅₁′↠c̅₂′ , c̅₂↠c̅₃ , c̅₃⊑c̅₂′ ⟩ =
  ⟨ c̅₂′ ⨾ c′ , c̅₃ , plug-cong c̅₁′↠c̅₂′ , c̅₂↠c̅₃ , ⊑-castr c̅₃⊑c̅₂′ g⊑g₁′ g⊑g′ ⟩
sim-back (⊑-⊥ l⊑l g⊑g′) c̅₁→c̅₂ = ⟨ _ , _ , _ ∎ , _ ∎ , ⊑-⊥ l⊑l g⊑g′ ⟩

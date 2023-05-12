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


sim-back : ∀ {ℓ ℓ′ g g′} {c̅₁ c̅₂ : CoercionExp (l ℓ) ⇒ g} {c̅₁′ : CoercionExp (l ℓ′) ⇒ g′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → c̅₁ —→ c̅₂
    -----------------------------------------------------------------
  → ∃[ c̅₂′ ] ∃[ c̅₃ ] (c̅₁′ —↠ c̅₂′) × (c̅₂ —↠ c̅₃) × (⊢ c̅₃ ⊑ c̅₂′)
sim-back (⊑-cast c̅⊑c̅′ g₁⊑g₁′ g⊑g′) c̅₁→c̅₂   = {!!}
sim-back (⊑-castl c̅⊑c̅₁′ g₁⊑g′ g⊑g′) c̅⨾c→c̅₂ = {!!}
sim-back (⊑-castr {c′ = c′} c̅₁⊑c̅′ g⊑g₁′ g⊑g′) c̅₁→c̅₂
  with sim-back c̅₁⊑c̅′ c̅₁→c̅₂
... | ⟨ c̅₂′ , c̅₃ , c̅₁′↠c̅₂′ , c̅₂↠c̅₃ , c̅₃⊑c̅₂′ ⟩ =
  ⟨ c̅₂′ ⨾ c′ , c̅₃ , plug-cong c̅₁′↠c̅₂′ , c̅₂↠c̅₃ , ⊑-castr c̅₃⊑c̅₂′ g⊑g₁′ g⊑g′ ⟩
sim-back (⊑-⊥ l⊑l g⊑g′) c̅₁→c̅₂ = ⟨ _ , _ , _ ∎ , _ ∎ , ⊑-⊥ l⊑l g⊑g′ ⟩

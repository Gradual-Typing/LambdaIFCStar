module LabelCoercionCalculi.Simulation where

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
open import LabelCoercionCalculi.CatchUp
open import LabelCoercionCalculi.SimLemmas


sim : ∀ {g₁ g₁′ g₂ g₂′} {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅₁′ c̅₂′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → c̅₁′ —→ c̅₂′
  → ∃[ c̅₂ ] (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)


sim-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
             {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅₁′ : CoercionExp g₁′ ⇒ g₂′}
             {c̅₂′ : CoercionExp g₁′ ⇒ g₃′}
             {c  : ⊢ g₂ ⇒ g₃} {c′  : ⊢ g₂′ ⇒ g₃′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₃′     {- c ⊑ c′ -}
  → c̅₁′ ⨾ c′ —→ c̅₂′
    ---------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ ⨾ c —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-cast {c = c} {c′} c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (ξ c̅₁′→c̅′)
  with sim c̅₁⊑c̅₁′ c̅₁′→c̅′
... | ⟨ c̅ , c̅₁↠c̅ , c̅⊑c̅′ ⟩ = ⟨ c̅ ⨾ c , plug-cong c̅₁↠c̅ , ⊑-cast c̅⊑c̅′ g₂⊑g₂′ g₃⊑g₃′ ⟩
sim-cast {c̅₁ = c̅₁} {c = c} {c′} c̅₁⊑⊥ g₂⊑g₂′ g₃⊑g₃′ ξ-⊥ =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ c̅₁ _ c̅₁⊑⊥ in
  ⟨ c̅₁ ⨾ c , _ ∎ , ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′ ⟩
sim-cast {c̅₁ = c̅₁} {c̅₁′} {c = id ⋆} c̅₁⊑c̅₁′ ⋆⊑ ⋆⊑ (id v′)
  with catchup c̅₁ c̅₁′ v′ c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅₁′ ⟩
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (id   v′) = sim-cast-id  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-id v′) = sim-cast-id? c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-↑ v′) = sim-cast-↑  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-⊥  v′) =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ _ _ c̅₁⊑c̅₁′ in
  ⟨ _ , _ ∎ , ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′ ⟩



sim (⊑-cast c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′) c̅₁′→c̅₂′ = sim-cast c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′ c̅₁′→c̅₂′
sim (⊑-castl c̅₁⊑c̅₁′ x x₁) c̅₁′→c̅₂′ = {!!}
sim (⊑-castr c̅₁⊑c̅₁′ x x₁) c̅₁′→c̅₂′ = {!!}

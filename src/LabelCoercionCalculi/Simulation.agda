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


sim : ∀ {ℓ ℓ′ g g′} {c̅₁ : CoercionExp (l ℓ) ⇒ g} {c̅₁′ c̅₂′ : CoercionExp (l ℓ′) ⇒ g′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → c̅₁′ —→ c̅₂′
    --------------------------------------
  → ∃[ c̅₂ ] (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)


sim-cast : ∀ {ℓ ℓ′ g₂ g₂′ g₃ g₃′}
             {c̅₁ : CoercionExp (l ℓ) ⇒ g₂} {c̅₁′ : CoercionExp (l ℓ′) ⇒ g₂′}
             {c̅₂′ : CoercionExp (l ℓ′) ⇒ g₃′}
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
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (id   v′) = sim-cast-id  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-id v′) = sim-cast-id? c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-↑ v′) = sim-cast-↑  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-⊥  v′) =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ _ _ c̅₁⊑c̅₁′ in
  ⟨ _ , _ ∎ , ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′ ⟩


sim-castr : ∀ {ℓ ℓ′ g₂ g₂′ g₃′}
             {c̅₁ : CoercionExp (l ℓ) ⇒ g₂} {c̅₁′ : CoercionExp (l ℓ′) ⇒ g₂′}
             {c̅₂′ : CoercionExp (l ℓ′) ⇒ g₃′}
             {c′  : ⊢ g₂′ ⇒ g₃′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → g₂ ⊑ₗ g₂′ → g₂ ⊑ₗ g₃′
  → c̅₁′ ⨾ c′ —→ c̅₂′
    ---------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-castr {c′ = c′} c̅₁⊑c̅₁′ g₂⊑g₂′ g₂⊑g₃′ (ξ c̅₁′→c̅′)
  with sim c̅₁⊑c̅₁′ c̅₁′→c̅′
... | ⟨ c̅ , c̅₁↠c̅ , c̅⊑c̅′ ⟩ = ⟨ c̅ , c̅₁↠c̅ , ⊑-castr c̅⊑c̅′ g₂⊑g₂′ g₂⊑g₃′ ⟩
sim-castr {c̅₁ = c̅₁} {c′ = c′} c̅₁⊑⊥ g₂⊑g₂′ g₂⊑g₃′ ξ-⊥ =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ c̅₁ _ c̅₁⊑⊥ in
  ⟨ c̅₁ , _ ∎ , ⊑-⊥ g₁⊑g₁′ g₂⊑g₃′ ⟩
-- sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (id   v′) = sim-cast-id  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
-- sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-id v′) = sim-cast-id? c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
-- sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-↑ v′) = sim-cast-↑  c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ v′
sim-castr c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-⊥  v′) =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ _ _ c̅₁⊑c̅₁′ in
  ⟨ _ , _ ∎ , ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′ ⟩


sim (⊑-cast  c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′) c̅₁′→c̅₂′ = sim-cast c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′ c̅₁′→c̅₂′
sim (⊑-castl {c = c} c̅₁⊑c̅₁′ g₃⊑g₂′ g₂⊑g₂′) c̅₁′→c̅₂′
  with sim c̅₁⊑c̅₁′ c̅₁′→c̅₂′
... | ⟨ c̅ , c̅₁↠c̅ , c̅⊑c̅′ ⟩ = ⟨ c̅ ⨾ c , plug-cong c̅₁↠c̅ , ⊑-castl c̅⊑c̅′ g₃⊑g₂′ g₂⊑g₂′ ⟩
sim (⊑-castr c̅₁⊑c̅₁′ g₂⊑g₃′ g₂⊑g₂′) c̅₁′→c̅₂′ = sim-castr c̅₁⊑c̅₁′ g₂⊑g₃′ g₂⊑g₂′ c̅₁′→c̅₂′

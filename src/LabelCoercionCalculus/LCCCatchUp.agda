module LabelCoercionCalculus.LCCCatchUp where

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
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.Precision
open import LabelCoercionCalculus.LabelCC

open import LabelCoercionCalculus.SyntacComp
open import LabelCoercionCalculus.CatchUp renaming (catchup to catchupₗ)

catchup : ∀ {g g′} {M V′} {g⊑g′ : g ⊑ₗ g′}
  → LCCVal V′
  → ⊢ M ⊑ V′ ⇐ g⊑g′
    -------------------------------------------------------
  → ∃[ V ] (LCCVal V) × (M —↠ₑ V) × (⊢ V ⊑ V′ ⇐ g⊑g′)
catchup v-l ⊑-l = ⟨ _ , v-l , _ ∎ , ⊑-l ⟩
catchup v-l (⊑-castl {g₁} {g₂} {g′} {M} {M′} {c̅} {g₁⊑g′ = g₁⊑g′} {g₂⊑g′} M⊑ℓ c̅⊑id)
  with catchup {g⊑g′ = g₁⊑g′} v-l M⊑ℓ
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case catchupₗ c̅ (id g′) id c̅⊑id of λ where
  ⟨ id _ , id , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫        —→⟨ cast c̅↠c̅ₙ id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-l ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast c̅↠c̅ₙ (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast ⟨ inj 𝓋 , (λ ()) ⟩ , ♥ , ⊑-castl {g₁⊑g′ = l⊑l} {⋆⊑} ⊑-l c̅ₙ⊑id ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    case ⟨ g₂⊑g′ , 𝓋 ⟩ of λ where
    ⟨ l⊑l , () ⟩  {- a coercion value from high ⇒ low is impossible -}
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑id ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) (id g′) id (comp-pres-⊑id c̅₁⊑id c̅⊑id) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast c̅₁⨟c̅↠c̅ₙ id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-l ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast c̅₁⨟c̅↠c̅ₙ (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast ⟨ inj 𝓋 , (λ ()) ⟩ , ♥ , ⊑-castl {g₁⊑g′ = l⊑l} {⋆⊑} ⊑-l c̅ₙ⊑id ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    case ⟨ g₂⊑g′ , 𝓋 ⟩ of λ where
    ⟨ l⊑l , () ⟩  {- a coercion value from high ⇒ low is impossible -}
catchup (v-cast x) M⊑V′ = {!!}

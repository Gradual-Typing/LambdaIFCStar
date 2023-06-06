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


open import LabelCoercionCalculus.CatchUp renaming (catchup to catchupₗ)

catchup : ∀ {g g′} {M V′} {g⊑g′ : g ⊑ₗ g′}
  → LCCVal V′
  → ⊢ M ⊑ V′ ⇐ g⊑g′
  → ∃[ V ] (LCCVal V) × (M —↠ₑ V) × (⊢ V ⊑ V′ ⇐ g⊑g′)
catchup v-l ⊑-l = ⟨ _ , v-l , _ ∎ , ⊑-l ⟩
catchup v-l (⊑-castl {g₁} {g₂} {g′} {g₁⊑g′ = g₁⊑g′} M⊑ℓ c̅⊑id)
  with catchup {g⊑g′ = g₁⊑g′} v-l M⊑ℓ
... | ⟨ V , v , M↠V , V⊑ℓ ⟩
  with catchupₗ _ _ id c̅⊑id
...   | ⟨ c̅ₙ , id , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ V , v , {!!} , V⊑ℓ ⟩
...   | ⟨ c̅ₙ , (inj _) , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ = {!!}
...   | ⟨ c̅ₙ , (up _) , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ = {!!}
...   | ⟨ c̅ₙ , id⨾? , c̅↠c̅ₙ , ⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩ = {!!}
catchup (v-cast x) M⊑V′ = {!!}

module LabelCoercionCalculi.SimCast↑ where

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


sim-cast-↑-proj : ∀ {g g′} {p} {c̅₁ : CoercionExp g ⇒ ⋆} {c̅′ : CoercionExp g′ ⇒ l low}
  → ⊢ c̅₁ ⊑ c̅′ ⨾ low !
  → 𝒱 c̅′
    --------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ ⨾ high ?? p —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅′ ⨾ ↑)
sim-cast-↑-proj {p = p} {c̅₁ = c̅₁} {c̅′ = id (l low)} c̅₁⊑c̅′⨾! id
  with catchup c̅₁ _ (inj id) c̅₁⊑c̅′⨾!
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-cast id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl x y z) ⋆⊑ ⋆⊑ ⟩ = {!!}
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑id l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , {!!} ⟩
sim-cast-↑-proj {c̅₁ = c̅₁} {c̅′ = id ⋆ ⨾ low ?? p′} c̅₁⊑c̅′⨾! id⨾? = {!!}



sim-cast-↑ : ∀ {g₁ g₂ g₃ g′}
                {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g′ ⇒ l low}
                {c  : ⊢ g₂ ⇒ g₃}
  → ⊢ c̅₁ ⊑ c̅′ ⨾ low !
  → g₂ ⊑ₗ ⋆ → g₃ ⊑ₗ l high  {- c ⊑ c₂′ -}
  → 𝒱 c̅′
    --------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ ⨾ c —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅′ ⨾ ↑)
sim-cast-↑ {c̅₁ = c̅₁} {c = id ⋆} c̅₁⊑c̅₁′ ⋆⊑ ⋆⊑ v′
  with catchup c̅₁ _ (inj v′) c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =  {- The simple case. Get rid of id and we're done -}
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) ,
    ⊑-castr (prec-inj-left _ _ v v′ c̅ₙ⊑c̅₁′) ⋆⊑ ⋆⊑ ⟩
sim-cast-↑ {c̅₁ = c̅₁} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l v′ = sim-cast-↑-proj c̅₁⊑c̅₁′ v′

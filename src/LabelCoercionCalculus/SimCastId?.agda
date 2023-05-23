module LabelCoercionCalculus.SimCastId? where

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
open import LabelCoercionCalculus.CatchUp


sim-cast-id? : ∀ {g₁ g₂ g₃ g′ ℓ}
    {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g′ ⇒ l ℓ}
    {c  : ⊢ g₂ ⇒ g₃}
  → ⊢ c̅₁ ⊑ c̅′ ⨾ ℓ !
  → g₂ ⊑ₗ ⋆ → g₃ ⊑ₗ l ℓ  {- c ⊑ c₂′ -}
  → 𝒱 c̅′
    --------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ ⨾ c —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅′)
sim-cast-id? {c̅₁ = c̅₁} {c = id ⋆} c̅₁⊑c̅₁′ ⋆⊑ ⋆⊑ v′
  with catchup c̅₁ _ (inj v′) c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , prec-inj-left _ _ v v′ c̅ₙ⊑c̅₁′ ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id (l low)} {c = low ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l id
  with catchup c̅₁ _ (inj id) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr x ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠id , ⊑-castl x ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) y z ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id ⋆ ⨾ low ?? p′} {c = low ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l id⨾?
  with catchup c̅₁ _ (inj id⨾?) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr x ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠id , ⊑-castl x ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) _ _) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id (l high)} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l id
  with catchup c̅₁ _ (inj id) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id (l low) ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (up id)
  with catchup c̅₁ _ (inj (up id)) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-cast x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast x l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑id⨾↑ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) y z) ⋆⊑ ⋆⊑ ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id ⋆ ⨾ low ?? p′ ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (up id⨾?)
  with catchup c̅₁ _ (inj (up id⨾?)) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-cast x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast x l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl x l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast x l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castr (⊑-castl _ () _) y z) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩
sim-cast-id? {c̅₁ = c̅₁} {c̅′ = id ⋆ ⨾ high ?? p′} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l id⨾?
  with catchup c̅₁ _ (inj id⨾?) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) y z) ⋆⊑ ⋆⊑ ⟩

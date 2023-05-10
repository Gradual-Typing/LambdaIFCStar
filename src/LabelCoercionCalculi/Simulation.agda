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


sim : ∀ {g₁ g₁′ g₂ g₂′} {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅₁′ c̅₂′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → c̅₁′ —→ c̅₂′
  → ∃[ c̅₂ ] (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)


sim-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
    {c̅₁ : CoercionExp g₁ ⇒ g₂} {c̅₁′ : CoercionExp g₁′ ⇒ g₂′}
    {c̅₂′ : CoercionExp g₁′ ⇒ g₃′}
    {c  : ⊢ g₂ ⇒ g₃}           {c′  : ⊢ g₂′ ⇒ g₃′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₃′     {- c ⊑ c′ -}
  → c̅₁′ ⨾ c′ —→ c̅₂′
    ------------------------------------------
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
sim-cast {c̅₁ = c̅₁} {c̅₁′} {c = id (l ℓ)} c̅₁⊑c̅₁′ l⊑l l⊑l (id v′)
  with catchup c̅₁ c̅₁′ v′ c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅₁′ ⟩
sim-cast {c̅₁ = c̅₁} {c̅₁′} {c = ℓ !} c̅₁⊑c̅₁′ l⊑l ⋆⊑ (id v′)
  with catchup c̅₁ c̅₁′ v′ c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ c̅ₙ ⨾ ℓ ! , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅₁′ l⊑l ⋆⊑ ⟩
sim-cast {c̅₁ = c̅₁} {id (l low)} {c = low ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (id id)
  with catchup c̅₁ _ id c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅₁′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠id⨾! , id⨾!⊑c̅₁′ ⟩ =
  ⟨ id (l low) , ↠-trans (plug-cong c̅₁↠id⨾!) (_ —→⟨ ?-id id ⟩ _ ∎) , ⊑-id l⊑l ⟩
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠id⨾?⨾! , id⨾?⨾!⊑c̅₁′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , ↠-trans (plug-cong c̅₁↠id⨾?⨾!) (_ —→⟨ ?-id id⨾? ⟩ _ ∎) , ⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
sim-cast {c̅₁ = c̅₁} {id ⋆ ⨾ low ?? q} {c = low ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (id id⨾?)
  with catchup c̅₁ _ id⨾? c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅₁′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠id⨾! , id⨾!⊑id⨾? ⟩ =
  case id⨾!⊑id⨾? of λ where  {- all impossible -}
  (⊑-cast (⊑-id ()) _ _)
  (⊑-castl (⊑-castr (⊑-id ()) y z) l⊑l ⋆⊑)
  (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑)
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠id⨾?⨾! , id⨾?⨾!⊑c̅₁′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , ↠-trans (plug-cong c̅₁↠id⨾?⨾!) (_ —→⟨ ?-id id⨾? ⟩ _ ∎) , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
sim-cast {c̅₁ = c̅₁} {id (l high)} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (id id)
  with catchup c̅₁ _ id c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅₁′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
sim-cast {c̅₁ = c̅₁} {id ⋆ ⨾ high ?? p′} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (id id⨾?)
  with catchup c̅₁ _ id⨾? c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑id⨾? ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑id⨾? ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
sim-cast {c̅₁ = c̅₁} {id (l low) ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′⨾↑ ⋆⊑ l⊑l (id (up id))
  with catchup c̅₁ _ (up id) c̅₁⊑c̅₁′⨾↑
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑c̅₁′⨾↑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₁′⨾↑ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑c̅₁′ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑c̅₁′ l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑ ⟩
sim-cast {c̅₁ = c̅₁} {id ⋆ ⨾ low ?? p′ ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′⨾↑ ⋆⊑ l⊑l (id (up id⨾?))
  with catchup c̅₁ _ (up id⨾?) c̅₁⊑c̅₁′⨾↑
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑c̅₁′⨾↑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₁′⨾↑ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl c̅ₙ⊑id () _) _ _) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾?⨾↑ _ _ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾?⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) _ _) _ _ ⟩
sim-cast {c̅₁ = c̅₁} {c = id ⋆} c̅₁⊑c̅₁′ ⋆⊑ ⋆⊑ (?-id v′)
  with catchup c̅₁ _ (inj v′) c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅₁′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , prec-inj-left _ _ v v′ c̅ₙ⊑c̅₁′ ⟩
sim-cast {c̅₁ = c̅₁} {c = low ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (?-id v′)
  with catchup c̅₁ _ (inj v′) c̅₁⊑c̅₁′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , _ ⟩ = {!!}
sim-cast {c̅₁ = c̅₁} {c̅₂′ = id (l high)} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (?-id id)
  with catchup c̅₁ _ (inj id) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , x ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
sim-cast {c̅₁ = c̅₁} {c̅₂′ = id (l low) ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (?-id (up id))
  with catchup c̅₁ _ (inj (up id)) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-cast x l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast x l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast x y z ⟩ = {!!}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) y z) ⋆⊑ ⋆⊑ ⟩
sim-cast {c̅₁ = c̅₁} {c̅₂′ = id ⋆ ⨾ low ?? p′ ⨾ ↑} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (?-id (up id⨾?))
  with catchup c̅₁ _ (inj (up id⨾?)) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr x ⋆⊑ ⋆⊑ ⟩ = {!!}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , _ ⟩ = {!!}
sim-cast {c̅₁ = c̅₁} {c̅₂′ = id ⋆ ⨾ high ?? p′} {c = high ?? p} c̅₁⊑c̅₁′ ⋆⊑ l⊑l (?-id id⨾?)
  with catchup c̅₁ _ (inj id⨾?) c̅₁⊑c̅₁′
... | ⟨ id ⋆ , id , c̅₁↠id , ⊑-castr id⊑c̅₂′ ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅₂′ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr x ⋆⊑ ⋆⊑ ⟩ = {!!}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , _ ⟩ = {!!}

sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-↑ x) = {!!}
sim-cast c̅₁⊑c̅₁′ g₂⊑g₂′ g₃⊑g₃′ (?-⊥ x) = {!!}


sim (⊑-cast c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′) c̅₁′→c̅₂′ = sim-cast c̅₁⊑c̅₁′ g₃⊑g₃′ g₂⊑g₂′ c̅₁′→c̅₂′
sim (⊑-castl c̅₁⊑c̅₁′ x x₁) c̅₁′→c̅₂′ = {!!}
sim (⊑-castr c̅₁⊑c̅₁′ x x₁) c̅₁′→c̅₂′ = {!!}

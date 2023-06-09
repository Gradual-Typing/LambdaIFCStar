module CoercionExpr.SimCastId where

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
open import CoercionExpr.CoercionExpr
open import CoercionExpr.Precision
open import CoercionExpr.CatchUp


sim-cast-id : ∀ {g₁ g₁′ g₂ g₂′ g₃}
             {c̅₁ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
             {c  : ⊢ g₂ ⇒ g₃}
  → ⊢ c̅₁ ⊑ c̅′
  → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₂′
  → 𝒱 c̅′
    ------------------------------------------
  → ∃[ c̅₂ ] (c̅₁ ⨾ c —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅′)
sim-cast-id {c̅₁ = c̅₁} {c̅′} {c = id ⋆} c̅₁⊑c̅′ ⋆⊑ ⋆⊑ v′
  with catchup c̅₁ c̅′ v′ c̅₁⊑c̅′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅′ ⟩
sim-cast-id {c̅₁ = c̅₁} {c̅′} {c = id (l ℓ)} c̅₁⊑c̅′ l⊑l l⊑l v′
  with catchup c̅₁ c̅′ v′ c̅₁⊑c̅′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅′ ⟩
sim-cast-id {c̅₁ = c̅₁} {c̅′} {c = ℓ !} c̅₁⊑c̅′ l⊑l ⋆⊑ v′
  with catchup c̅₁ c̅′ v′ c̅₁⊑c̅′
... | ⟨ c̅ₙ , v , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ c̅ₙ ⨾ ℓ ! , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅′ l⊑l ⋆⊑ ⟩
sim-cast-id {c̅₁ = c̅₁} {id (l low)} {c = low ?? p} c̅₁⊑c̅′ ⋆⊑ l⊑l id
  with catchup c̅₁ _ id c̅₁⊑c̅′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠id⨾! , id⨾!⊑c̅′ ⟩ =
  ⟨ id (l low) , ↠-trans (plug-cong c̅₁↠id⨾!) (_ —→⟨ ?-id id ⟩ _ ∎) , ⊑-id l⊑l ⟩
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠id⨾?⨾! , id⨾?⨾!⊑c̅′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , ↠-trans (plug-cong c̅₁↠id⨾?⨾!) (_ —→⟨ ?-id id⨾? ⟩ _ ∎) , ⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
sim-cast-id {c̅₁ = c̅₁} {id ⋆ ⨾ low ?? q} {c = low ?? p} c̅₁⊑c̅′ ⋆⊑ l⊑l id⨾?
  with catchup c̅₁ _ id⨾? c̅₁⊑c̅′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠id⨾! , id⨾!⊑id⨾? ⟩ =
  case id⨾!⊑id⨾? of λ where  {- all impossible -}
  (⊑-cast (⊑-id ()) _ _)
  (⊑-castl (⊑-castr (⊑-id ()) y z) l⊑l ⋆⊑)
  (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑)
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠id⨾?⨾! , id⨾?⨾!⊑c̅′ ⟩ =
  ⟨ id ⋆ ⨾ low ?? p , ↠-trans (plug-cong c̅₁↠id⨾?⨾!) (_ —→⟨ ?-id id⨾? ⟩ _ ∎) , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
sim-cast-id {c̅₁ = c̅₁} {id (l high)} {c = high ?? p} c̅₁⊑c̅′ ⋆⊑ l⊑l id
  with catchup c̅₁ _ id c̅₁⊑c̅′
... | ⟨ id ⋆ , id , c̅₁↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅′ ⋆⊑ l⊑l ⟩
... | ⟨ id (l low) ⨾ low  ! , inj id , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
... | ⟨ id ⋆ ⨾ low ?? p ⨾ low  ! , inj id⨾? , c̅₁↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
sim-cast-id {c̅₁ = c̅₁} {id ⋆ ⨾ high ?? p′} {c = high ?? p} c̅₁⊑c̅′ ⋆⊑ l⊑l id⨾?
  with catchup c̅₁ _ id⨾? c̅₁⊑c̅′
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑id⨾? ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑id⨾? ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
sim-cast-id {c̅₁ = c̅₁} {id (l low) ⨾ ↑} {c = high ?? p} c̅₁⊑c̅′⨾↑ ⋆⊑ l⊑l (up id)
  with catchup c̅₁ _ (up id) c̅₁⊑c̅′⨾↑
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑c̅′⨾↑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅′⨾↑ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑c̅′ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑c̅′ l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑ ⟩
sim-cast-id {c̅₁ = c̅₁} {id ⋆ ⨾ low ?? p′ ⨾ ↑} {c = high ?? p} c̅₁⊑c̅′⨾↑ ⋆⊑ l⊑l (up id⨾?)
  with catchup c̅₁ _ (up id⨾?) c̅₁⊑c̅′⨾↑
... | ⟨ id ⋆ , id , c̅₁↠id , id⊑c̅′⨾↑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , plug-cong c̅₁↠id , ⊑-castl id⊑c̅′⨾↑ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-cast c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl c̅ₙ⊑id () _) _ _) ⋆⊑ ⋆⊑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾?⨾↑ _ _ ⟩ =
  ⟨ c̅ₙ , ↠-trans (plug-cong c̅₁↠c̅ₙ⨾!) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾?⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅₁↠c̅ₙ⨾! , ⊑-castr (⊑-castr (⊑-castl _ () _) _ _) _ _ ⟩

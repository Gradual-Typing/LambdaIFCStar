module CoercionExpr.SimBackCastId? where

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
open import CoercionExpr.CatchUpBack


sim-back-cast-id? : ∀ {ℓ₁ ℓ₂ ℓ′ g′}
    {c̅ : CExpr l ℓ₁ ⇒ l ℓ₂} {c̅₁′ : CExpr l ℓ′ ⇒ g′}
    {c′ : ⊢ g′ ⇒ l ℓ₂}
  → ⊢ c̅ ⨾ ℓ₂ ! ⊑ c̅₁′
  → CVal c̅
    --------------------------------------------
  → ∃[ c̅₂′ ] (c̅₁′ ⨾ c′ —↠ c̅₂′) × (⊢ c̅ ⊑ c̅₂′)
sim-back-cast-id? {c′ = id (l low)} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) , c̅₁′↠c̅₂′ , v-v id x ⟩ =
  ⟨ id (l low) , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ id (l low) —→⟨ id id ⟩ id (l low) ∎) , ⊑-id l⊑l ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ x ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = id (l high)} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l high) , c̅₁′↠c̅₂′ , v-v id x ⟩ =
  ⟨ id (l high) , ↠-trans (plug-cong c̅₁′↠c̅₂′) (_ —→⟨ id id ⟩ _ ∎) , ⊑-id l⊑l ⟩
... | ⟨ id (l low) ⨾ ↑ , c̅₁′↠c̅₂′ , v-v (up id) x ⟩ =
  case prec→⊑ _ _ x of λ where ⟨ () , _ ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ x ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = id (l high)} c̅₁⨾!⊑c̅₁′ (up id)
  with catchup-back _ _ (inj (up id)) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l high) , c̅₁′↠c̅₂′ , v-v id x ⟩ =
  case prec→⊑ _ _ x of λ where ⟨ () , _ ⟩
... | ⟨ id (l low) ⨾ ↑ , c̅₁′↠c̅₂′ , v-v (up id) x ⟩ =
  ⟨ id (l low) ⨾ ↑ , ↠-trans (plug-cong c̅₁′↠c̅₂′) (_ —→⟨ id (up id) ⟩ _ ∎) , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ x ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = ↑} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) , c̅₁′↠c̅₂′ , v-v id (⊑-castl _ () _) ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ x ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = ↑} c̅₁⨾!⊑c̅₁′ (up id)
  with catchup-back _ _ (inj (up id)) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) , c̅₁′↠c̅₂′ , v-v id (⊑-castl _ () _) ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ x ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = low ?? p} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj id) x ⟩ =
  ⟨ id (l low) , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ (low !) ⨾ (low ?? p) —→⟨ ?-id id ⟩ id (l low) ∎) , ⊑-id l⊑l ⟩
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-castr (⊑-castl _ () _) y z) ⟩
... | ⟨ c̅′ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj (up id)) (⊑-castr _ _ _) ⟩ =
  ⟨ ⊥ _ _ p , ↠-trans (plug-cong c̅₁′↠c̅₂′) (id (l low) ⨾ ↑ ⨾ (high !) ⨾ (low ?? p) —→⟨ ?-⊥ (up id) ⟩
                                                 ⊥ (l low) (l low) p ∎) , ⊑-⊥ l⊑l l⊑l ⟩
... | ⟨ c̅₂′ , c̅₁′↠⊥ , v-⊥ x ⟩ with prec→⊑ _ _ x
... | ⟨ l⊑l , _ ⟩ =
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , ⊑-⊥ l⊑l l⊑l ⟩
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ id
  with catchup-back _ _ (inj id) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-castr (⊑-castl _ () _) _ _) ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) x ⟩ =
  ⟨ id (l high) , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l high) ⨾ (high !) ⨾ (high ?? p) —→⟨ ?-id id ⟩ id (l high) ∎) , ⊑-id l⊑l ⟩
... | ⟨ id (l low) ⨾ ↑ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj (up id)) x ⟩ =
  case prec→⊑ _ _ x of λ where ⟨ () , _ ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ _ ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥)
    (⊥ _ ⋆ _ ⨾ (high ?? p) —→⟨ ξ-⊥ ⟩ ⊥ _ (l high) _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩
sim-back-cast-id? {c′ = high ?? p} c̅₁⨾!⊑c̅₁′ (up id)
  with catchup-back _ _ (inj (up id)) c̅₁⨾!⊑c̅₁′
... | ⟨ id (l low) ⨾ low ! , c̅₁′↠c̅₂′ , v-v (inj id) x ⟩ =
  ⟨ id (l low) ⨾ ↑ , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ (low !) ⨾ (high ?? p) —→⟨ ?-↑ id ⟩ id (l low) ⨾ ↑ ∎) , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-cast (⊑-castl _ () _) _ _) ⟩
... | ⟨ id (l high) ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj id) (⊑-castr (⊑-castl (⊑-castl _ () _) _ _) _ _) ⟩
... | ⟨ id (l low) ⨾ ↑ ⨾ high ! , c̅₁′↠c̅₂′ , v-v (inj (up id)) x ⟩ =
  ⟨ id (l low) ⨾ ↑ , ↠-trans (plug-cong c̅₁′↠c̅₂′)
    (id (l low) ⨾ ↑ ⨾ (high !) ⨾ (high ?? p) —→⟨ ?-id (up id) ⟩ id (l low) ⨾ ↑ ∎) , ⊑-cast (⊑-id l⊑l) l⊑l l⊑l ⟩
... | ⟨ ⊥ _ _ _ , c̅₁′↠⊥ , v-⊥ _ ⟩ =
  let ⟨ ℓ⊑ℓ′ , _ ⟩ = prec→⊑ _ _ c̅₁⨾!⊑c̅₁′ in
  ⟨ ⊥ _ _ _ , ↠-trans (plug-cong c̅₁′↠⊥)
    (_ —→⟨ ξ-⊥ ⟩ ⊥ _ (l high) _ ∎) , ⊑-⊥ ℓ⊑ℓ′ l⊑l ⟩

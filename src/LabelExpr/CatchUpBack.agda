module LabelExpr.CatchUpBack where

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
open import LabelExpr.LabelExpr

open import CoercionExpr.CoercionExpr hiding (Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.Precision
open import CoercionExpr.SyntacComp
open import CoercionExpr.CatchUpBack renaming (InSync to InSyncₗ ; catchup-back to catchup-backₗ)


data InSync : ∀ (M N : LExpr) → Set where

  v-v : ∀ {g g′} {M V} {g⊑g′ : g ⊑ₗ g′}
    → LVal V
    → ⊢ M ⊑ V ⇐ g⊑g′
      -------------------
    → InSync M V

  v-⊥ : ∀ {g g′} {M p} {g⊑g′ : g ⊑ₗ g′}
    → ⊢ M ⊑ blame p ⇐ g⊑g′
      --------------------------
    → InSync M (blame p)


catchup-back : ∀ {g g′} {V M′} {g⊑g′ : g ⊑ₗ g′}
  → LVal V
  → ⊢ V ⊑ M′ ⇐ g⊑g′
  → ∃[ N′ ] (M′ —↠ₑ N′) × (InSync V N′)
catchup-back v-l ⊑-l = ⟨ l _ , _ ∎ , v-v {g⊑g′ = l⊑l} v-l ⊑-l ⟩
catchup-back (v-cast ⟨ 𝓋 , x ⟩) (⊑-cast {c̅ = c̅} {c̅′} {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} V⊑M′ c̅⊑c̅′)
  with catchup-back {g⊑g′ = l⊑l} v-l V⊑M′
... | ⟨ blame p , M′↠⊥ , v-⊥ V⊑⊥ ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    v-⊥ {g⊑g′ = g₂⊑g₂′} (⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢l)) ⟩
... | ⟨ l ℓ , M′↠V′ , v-v v-l ⊑-l ⟩ =
  case catchup-backₗ _ _ 𝓋 c̅⊑c̅′ of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      v-⊥ {g⊑g′ = g₂⊑g₂′} (⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢l)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} v-l (⊑-castl {g₁⊑g′ = l⊑l} {g₂⊑g₂′} ⊑-l (⊑-left-contract c̅⊑id)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ (up id) ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ up id , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
... | ⟨ l ℓ ⟪ c̅′₁ ⟫ , M′↠V′ , v-v (v-cast i) (⊑-castr {g⊑g₁′ = l⊑l} {l⊑l} ⊑-l ℓ⊑c̅′₁) ⟩ =
  let prec : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      prec = comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 prec of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      v-⊥ {g⊑g′ = g₂⊑g₂′} (⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢l)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} v-l (⊑-castl {g₁⊑g′ = l⊑l} {g₂⊑g₂′} ⊑-l (⊑-left-contract c̅⊑id)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (up id) ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ up id , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
      v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
catchup-back v (⊑-castl V⊑M′ x) = {!!}
catchup-back v (⊑-castr V⊑M′ x) = {!!}
catchup-back v (⊑-blame x) = {!!}

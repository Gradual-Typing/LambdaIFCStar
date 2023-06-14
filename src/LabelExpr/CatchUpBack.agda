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
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SyntacComp
open import CoercionExpr.CatchUpBack renaming (InSync to InSyncₗ ; catchup-back to catchup-backₗ)


data InSync : ∀ (M N : LExpr) → Set where

  v-v : ∀ {g g′} {M V}
    → LVal V
    → ⊢ M ⊑ V ⇐ g ⊑ g′
      -------------------
    → InSync M V

  v-⊥ : ∀ {g g′} {M p}
    → ⊢ M ⊑ blame p ⇐ g ⊑ g′
      --------------------------
    → InSync M (blame p)


catchup-back : ∀ {g g′} {V M′}
  → LVal V
  → ⊢ V ⊑ M′ ⇐ g ⊑ g′
  → ∃[ N′ ] (M′ —↠ₑ N′) × (InSync V N′)
catchup-back v-l ⊑-l = ⟨ l _ , _ ∎ , v-v v-l ⊑-l ⟩
catchup-back (v-cast ⟨ 𝓋 , x ⟩) (⊑-cast {c̅ = c̅} {c̅′} V⊑M′ c̅⊑c̅′)
  with catchup-back v-l V⊑M′
... | ⟨ blame p , M′↠⊥ , v-⊥ V⊑⊥ ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    v-⊥ (⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′))) ⟩
... | ⟨ l ℓ , M′↠V′ , v-v v-l ⊑-l ⟩ =
  case precₗ→⊑ _ _ c̅⊑c̅′ of λ where
  ⟨ l⊑l , _ ⟩ →
    case catchup-backₗ _ _ 𝓋 c̅⊑c̅′ of λ where
    ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
      ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
        v-⊥ (⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′))) ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
      ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
        v-v v-l (⊑-castl ⊑-l (⊑-left-contract c̅⊑id)) ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
      ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ (up id) ⟩ _ ∎) ,
        v-v (v-cast ⟨ up id , (λ ()) ⟩) (⊑-cast ⊑-l c̅′⊑c̅″) ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
      ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
        v-v (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast ⊑-l c̅′⊑c̅″) ⟩
... | ⟨ l ℓ ⟪ c̅′₁ ⟫ , M′↠V′ , v-v (v-cast i) (⊑-castr ⊑-l ℓ⊑c̅′₁) ⟩
  with preserve-mult (proj₂ (prec→⊢ V⊑M′)) M′↠V′
...   | ⊢cast ⊢l =
  let prec : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      prec = comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 prec of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      v-⊥ (⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′))) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      v-v v-l (⊑-castl ⊑-l (⊑-left-contract c̅⊑id)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (up id) ⟩ _ ∎) ,
      v-v (v-cast ⟨ up id , (λ ()) ⟩) (⊑-cast ⊑-l c̅′⊑c̅″) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
      v-v (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast ⊑-l c̅′⊑c̅″) ⟩
catchup-back (v-cast i) (⊑-castl V⊑M′ c̅⊑g′)
  with catchup-back v-l V⊑M′ | proj₁ (prec-left→⊑ _ c̅⊑g′)
... | ⟨ blame p , M′↠⊥ , v-⊥ prec ⟩ | l⊑l =
  ⟨ blame p , M′↠⊥ , v-⊥ (⊑-castl (⊑-blame ⊢l l⊑l) c̅⊑g′) ⟩
... | ⟨ V′ , M′↠V′ , v-v v′ M⊑V′ ⟩ | l⊑l
  with prec→⊢ M⊑V′ | prec→⊑ M⊑V′
... | ⟨ ⊢l , _ ⟩ | l⊑l =
    ⟨ V′ , M′↠V′ , v-v v′ (⊑-castl M⊑V′ c̅⊑g′) ⟩
catchup-back v (⊑-castr V⊑M′ g⊑c̅′) = {!!}
--   with catchup-back {g⊑g′ = g⊑g₁′} v V⊑M′
-- ... | ⟨ blame p , M′↠⊥ , v-⊥ V⊑⊥ ⟩ =
--   ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
--     v-⊥ {g⊑g′ = g⊑g₂′} (⊑-blame {g⊑g′ = g⊑g₂′} (proj₁ (prec→⊢ {g⊑g′ = g⊑g₁′} V⊑M′))) ⟩
-- ... | ⟨ l ℓ , M′↠V′ , v-v {g⊑g′ = g⊑g′} v-l prec ⟩
--   with preserve-mult (proj₂ (prec→⊢ {g⊑g′ = g⊑g₁′} V⊑M′)) M′↠V′
-- ...   | ⊢l
--   with  prec→⊢ {g⊑g′ = {!!}} prec | prec→⊢ V⊑M′ 
-- ...   | ⟨ ⊢V , ⊢l ⟩ | ⟨ ⊢V† , _ ⟩
--   with catchup-back-right _ (⊑-right-expand g⊑c̅′)
-- ...   | ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ =
--     ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
--       v-⊥ {g⊑g′ = g⊑g′} (⊑-blame {g⊑g′ = g⊑g′} ⊢V) ⟩
-- ...   | ⟨ id (l ℓ) , c̅′↠id , v-v id (⊑-id g⊑ℓ) ⟩ =
--     ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠id id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
--       v-v {g⊑g′ = g⊑g′} v-l prec ⟩
-- ...   | ⟨ id (l low) ⨾ ↑ , c̅′↠id⨾↑ , v-v (up id) c̅′⊑id⨾↑ ⟩ =
--     ⟨ l _ ⟪ id (l low) ⨾ ↑ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠id⨾↑ (up id) ⟩ _ ∎) ,
--       v-v {g⊑g′ = {!!}} (v-cast ⟨ up id , (λ ()) ⟩) (⊑-castr prec (⊑-right-contract {!c̅′⊑id⨾↑!})) ⟩
-- ...   | ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ = {!!}
--     -- ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
--     --   v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
-- catchup-back v (⊑-castr V⊑M′ g⊑c̅′) | ⟨ l ℓ ⟪ c̅′₁ ⟫ , M′↠V′ , v-v (v-cast i) prec ⟩ = {!!}
  -- let prec : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
  --     prec = comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′ in
  -- case catchup-backₗ _ _ 𝓋 prec of λ where
  -- ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
  --   ⟨ blame _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
  --     v-⊥ {g⊑g′ = g₂⊑g₂′} (⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢l)) ⟩
  -- ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
  --   ⟨ l _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
  --     v-v {g⊑g′ = g₂⊑g₂′} v-l (⊑-castl {g₁⊑g′ = l⊑l} {g₂⊑g₂′} ⊑-l (⊑-left-contract c̅⊑id)) ⟩
  -- ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
  --   ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (up id) ⟩ _ ∎) ,
  --     v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ up id , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
  -- ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
  --   ⟨ l _ ⟪ c̅″ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅′↠c̅″ (inj 𝓋′) ⟩ _ ∎) ,
  --     v-v {g⊑g′ = g₂⊑g₂′} (v-cast ⟨ inj 𝓋′ , (λ ()) ⟩) (⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅′⊑c̅″) ⟩
catchup-back v (⊑-blame ⊢V x) = ⟨ _ , _ ∎ , v-⊥ (⊑-blame ⊢V x) ⟩

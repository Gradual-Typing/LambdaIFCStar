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

open import CoercionExpr.CoercionExpr
  renaming (_—→⟨_⟩_ to _—→ₗ⟨_⟩_; _∎ to _∎ₗ)
  hiding (Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SyntacComp
open import CoercionExpr.CatchUpBack renaming (catchup-back to catchup-backₗ)


catchup-back : ∀ {g g′} {V M′}
  → LVal V
  → ⊢ V ⊑ M′ ⇐ g ⊑ g′
    ---------------------------------------------------------------
  → ∃[ N′ ] (LResult N′) × (M′ —↠ₑ N′) × (⊢ V ⊑ N′ ⇐ g ⊑ g′)
catchup-back v-l ⊑-l = ⟨ l _ , success v-l , _ ∎ , ⊑-l ⟩
catchup-back (v-cast (ir 𝓋 x)) (⊑-cast {c̅ = c̅} {c̅′} V⊑M′ c̅⊑c̅′)
  with catchup-back v-l V⊑M′
... | ⟨ blame p , fail , M′↠⊥ , V⊑⊥ ⟩ =
  ⟨ blame p , fail , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
... | ⟨ l ℓ , success v-l , M′↠V′ , ⊑-l ⟩ =
  case precₗ→⊑ _ _ c̅⊑c̅′ of λ where
  ⟨ l⊑l , _ ⟩ →
    case catchup-backₗ _ _ 𝓋 c̅⊑c̅′ of λ where
    ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
      ⟨ blame _ , fail , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
        ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
      ⟨ l _ , success v-l ,
        ↠ₑ-trans (plug-congₑ M′↠V′)
        (case c̅′↠c̅″ of λ where
         (_ ∎ₗ) → _ —→⟨ β-id ⟩ _ ∎
         (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
        ⊑-castl ⊑-l (⊑-left-contract c̅⊑id) ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
      ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
        ↠ₑ-trans (plug-congₑ M′↠V′)
                  (case c̅′↠c̅″ of λ where
                   (_ ∎ₗ) → _ ∎
                   (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (up id) ⟩ _ ∎) ,
        ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
    ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
      ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
        ↠ₑ-trans (plug-congₑ M′↠V′)
                  (case c̅′↠c̅″ of λ where
                   (_ ∎ₗ) → _ ∎
                   (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋′) ⟩ _ ∎) ,
        ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
... | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i) , M′↠V′ , ⊑-castr ⊑-l ℓ⊑c̅′₁ ⟩
  with preserve-mult (proj₂ (prec→⊢ V⊑M′)) M′↠V′
...   | ⊢cast ⊢l =
  let prec : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      prec = comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 prec of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , fail , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl ⊑-l (⊑-left-contract c̅⊑id) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (up id)) (up id) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (inj 𝓋′)) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
catchup-back (v-cast i) (⊑-castl V⊑M′ c̅⊑g′)
  with catchup-back v-l V⊑M′ | proj₁ (prec-left→⊑ _ c̅⊑g′)
... | ⟨ blame p , fail , M′↠⊥ , prec ⟩ | l⊑l =
  ⟨ blame p , fail , M′↠⊥ , ⊑-castl (⊑-blame ⊢l l⊑l) c̅⊑g′ ⟩
... | ⟨ V′ , success v′ , M′↠V′ , M⊑V′ ⟩ | l⊑l
  with prec→⊢ M⊑V′ | prec→⊑ M⊑V′
... | ⟨ ⊢l , _ ⟩ | l⊑l =
    ⟨ V′ , success v′ , M′↠V′ , ⊑-castl M⊑V′ c̅⊑g′ ⟩
catchup-back v (⊑-castr V⊑M′ g⊑c̅′)
  with catchup-back v V⊑M′
... | ⟨ blame p , fail , M′↠⊥ , V⊑⊥ ⟩ =
  ⟨ blame p , fail , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame (proj₁ (prec→⊢ V⊑M′)) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
... | ⟨ l ℓ , success v-l , M′↠V′ , prec ⟩
  with preserve-mult (proj₂ (prec→⊢ V⊑M′)) M′↠V′
...   | ⊢l
  with  prec→⊢ prec
...   | ⟨ ⊢V , ⊢l ⟩
  with catchup-back-right _ (⊑-right-expand g⊑c̅′)
...   | ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ =
    ⟨ blame _ , fail , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame ⊢V (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
...   | ⟨ id (l ℓ) , c̅′↠id , v-v id (⊑-id g⊑ℓ) ⟩ =
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′)
                (case c̅′↠id of λ where
                 (_ ∎ₗ) → _ —→⟨ β-id ⟩ _ ∎
                 (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      prec ⟩
...   | ⟨ id (l low) ⨾ ↑ , c̅′↠id⨾↑ , v-v (up id) c̅′⊑id⨾↑ ⟩ =
    ⟨ l _ ⟪ id (l low) ⨾ ↑ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′)
                (case c̅′↠id⨾↑ of λ where
                 (_ ∎ₗ) → _ ∎
                 (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (up id) ⟩ _ ∎) ,
      ⊑-castr prec (⊑-right-contract c̅′⊑id⨾↑) ⟩
...   | ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ =
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′)
                (case c̅′↠c̅″ of λ where
                 (_ ∎ₗ) → _ ∎
                 (_ —→ₗ⟨ r ⟩ r*) → _ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-castr prec (⊑-right-contract c̅′⊑c̅″) ⟩
catchup-back (v-cast (ir 𝓋 _)) (⊑-castr {c̅′ = c̅′} V⊑M′ g⊑c̅′)
    | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-cast {M = M} {c̅ = c̅} {c̅′₁} M⊑ℓ c̅⊑c̅′₁ ⟩ =
  let prec : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      prec = comp-pres-⊑-br c̅⊑c̅′₁ g⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 prec of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , fail ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl M⊑ℓ (⊑-left-contract c̅⊑id) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (up id)) (up id) ⟩ _ ∎) ,
      ⊑-cast M⊑ℓ c̅′⊑c̅″ ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (inj 𝓋′)) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast M⊑ℓ c̅′⊑c̅″ ⟩
catchup-back (v-cast (ir 𝓋 _) ) (⊑-castr {c̅′ = c̅′} V⊑M′ g⊑c̅′)
    | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castl {c̅ = c̅} (⊑-castr ⊑-l ℓ⊑c̅′₁) c̅⊑g′ ⟩ =
  let c̅⊑c̅′₁⨟c̅′ : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      c̅⊑c̅′₁⨟c̅′ = comp-pres-⊑-br (comp-pres-⊑-rl ℓ⊑c̅′₁ c̅⊑g′) g⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 c̅⊑c̅′₁⨟c̅′ of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ z ⟩ →
    ⟨ blame _ , fail ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl ⊑-l (⊑-left-contract c̅⊑id) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (up id)) (up id) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (inj 𝓋′)) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
catchup-back {g = g} {g′} v (⊑-castr {M = V} {c̅′ = c̅′} V⊑M′ g⊑c̅′)
    | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castr ⊑-l g⊑c̅′₁ ⟩ =
  let id⊑c̅′₁⨟c̅′ = ⊑-right-expand (comp-pres-⊑-rr g⊑c̅′₁ g⊑c̅′) in
  case catchup-backₗ _ _ id id⊑c̅′₁⨟c̅′ of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ _ ⟩ →
    ⟨ blame _ , fail ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame ⊢l (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-l ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (up id)) (up id) ⟩ _ ∎) ,
      ⊑-castr ⊑-l (⊑-right-contract c̅′⊑c̅″) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (inj 𝓋′)) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-castr ⊑-l (⊑-right-contract c̅′⊑c̅″) ⟩
catchup-back {g = g} {g′} (v-cast {c̅ = c̅} (ir 𝓋 _)) (⊑-castr {M = V} {c̅′ = c̅′} V⊑M′ g⊑c̅′)
    | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castr (⊑-castl ⊑-l c̅⊑ℓ) g⊑c̅′₁ ⟩ =
  let c̅⊑c̅′₁⨟c̅′ : ⊢ c̅ ⊑ c̅′₁ ⨟ c̅′
      c̅⊑c̅′₁⨟c̅′ = comp-pres-⊑-br (comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′₁) g⊑c̅′ in
  case catchup-backₗ _ _ 𝓋 c̅⊑c̅′₁⨟c̅′ of λ where
  ⟨ c̅″ , c̅′↠⊥ , v-⊥ _ ⟩ →
    ⟨ blame _ , fail ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v id c̅⊑id ⟩ →
    ⟨ l _ , success v-l ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl ⊑-l c̅⊑ℓ ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (up id) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (up id) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (up id)) (up id) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
  ⟨ c̅″ , c̅′↠c̅″ , v-v (inj 𝓋′) c̅′⊑c̅″ ⟩ →
    ⟨ l _ ⟪ c̅″ ⟫ , success (v-cast (ir (inj 𝓋′) (λ ()))) ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast (comp-→⁺ c̅′↠c̅″ (inj 𝓋′)) (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅′⊑c̅″ ⟩
catchup-back v (⊑-blame ⊢V x) = ⟨ _ , fail , _ ∎ , ⊑-blame ⊢V x ⟩

catchup-back-success : ∀ {g g′} {V M′ V′}
  → LVal V
  → ⊢ V ⊑ M′ ⇐ g ⊑ g′
  → (M′ —↠ₑ V′)
  → LVal V′
    ------------------------------
  → ⊢ V ⊑ V′ ⇐ g ⊑ g′
catchup-back-success v V⊑M′ M′↠V′ v′ =
  case catchup-back v V⊑M′ of λ where
  ⟨ _ , fail , M′↠⊥ , V⊑⊥ ⟩ →
    case det-multₑ M′↠V′ M′↠⊥ (success v′) fail of λ where
    refl → case v′ of λ where ()
  ⟨ V′ , success v′† , M′↠V′† , V⊑V′ ⟩ →
    case det-multₑ M′↠V′ M′↠V′† (success v′) (success v′†) of λ where
    refl → V⊑V′

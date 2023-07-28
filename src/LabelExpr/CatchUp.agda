module LabelExpr.CatchUp where

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

open import CoercionExpr.CoercionExpr renaming (_—→⟨_⟩_ to _—→ₗ⟨_⟩_ ; _∎ to _∎ₗ)
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SyntacComp
open import CoercionExpr.CatchUp renaming (catchup to catchupₗ)


catchup : ∀ {g g′} {M V′}
  → LVal V′
  → ⊢ M ⊑ V′ ⇐ g ⊑ g′
    -----------------------------------------------------------
  → ∃[ V ] (LVal V) × (M —↠ₑ V) × (⊢ V ⊑ V′ ⇐ g ⊑ g′)
catchup v-l ⊑-l = ⟨ _ , v-l , _ ∎ , ⊑-l ⟩
catchup v-l (⊑-castl {g₁} {g₂} {g′} {M} {M′} {c̅} M⊑ℓ c̅⊑ℓ)
  with catchup v-l M⊑ℓ
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case catchupₗ c̅ (id g′) id (⊑-left-expand c̅⊑ℓ) of λ where
  ⟨ id _ , id , _ ∎ₗ , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-l ⟩
  ⟨ id _ , id , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫        —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-l ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , plug-congₑ M↠V ,
      ⊑-castl ⊑-l (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-castl ⊑-l (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅↠c̅ₙ , ⊑-castl _ l⊑l () ⟩ {- a coercion value from high ⇒ low is impossible -}
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) (id g′) id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑ℓ c̅⊑ℓ)) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ id) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-l ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-castl ⊑-l (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅₁⨟c̅↠c̅ₙ , ⊑-castl _ l⊑l () ⟩ {- a coercion value from high ⇒ low is impossible -}
catchup (v-cast (ir 𝓋′ x )) (⊑-cast {g₁} {g₁′} {g₂} {g₂′} {M} {M′} {c̅} {c̅′} M⊑V′ c̅⊑c̅′)
  with catchup v-l M⊑V′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case catchupₗ c̅ c̅′ 𝓋′ c̅⊑c̅′ of λ where
  ⟨ id _ , id , _ ∎ₗ , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l (⊑-right-contract c̅ₙ⊑c̅′) ⟩
  ⟨ id _ , id , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫        —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l (⊑-right-contract c̅ₙ⊑c̅′) ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅′ ⟩ →
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , plug-congₑ M↠V , ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ , ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , up id , _ ∎ₗ , c̅ₙ⊑c̅′ ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ → ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up id) x ) , plug-congₑ M↠V , ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , up id , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (up id) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ → ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up id) x ) , ♥ , ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) c̅′ 𝓋′ (comp-pres-⊑-lb c̅₁⊑ℓ c̅⊑c̅′) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ id) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l (⊑-right-contract c̅ₙ⊑c̅′) ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , up id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ →
      let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
              (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
              l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (up id)) (up id) ⟩
              l ℓ ⟪ c̅ₙ ⟫ ∎) in
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up id) x) , ♥ ,
        ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
catchup (v-cast (ir 𝓋′ x )) (⊑-castl {g₁} {g₂} {g′} {M} {M′} {c̅} M⊑V′ c̅⊑g′)
  with catchup (v-cast (ir 𝓋′ x)) M⊑V′
... | ⟨ l ℓ , v-l , M↠V , ⊑-castr ⊑-l ℓ⊑c̅′ ⟩ =
  case catchupₗ c̅ (id g′) id (⊑-left-expand c̅⊑g′) of λ where
  ⟨ id _ , id , _ ∎ₗ , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l ℓ⊑c̅′ ⟩
  ⟨ id _ , id , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫        —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l ℓ⊑c̅′ ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , plug-congₑ M↠V ,
      ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , up 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑id) of λ where
    ⟨ _ , l⊑l ⟩ →
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up 𝓋) x) , plug-congₑ M↠V ,
             ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑id) ⟩
  ⟨ c̅ₙ , up 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅ ⟫ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (up 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    case (precₗ→⊑ _ _ c̅ₙ⊑id) of λ where
    ⟨ _ , l⊑l ⟩ →
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up 𝓋) x) , ♥ ,
             ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑id) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-cast ⊑-l c̅₁⊑c̅′ ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) _ 𝓋′ (comp-pres-⊑-bl c̅₁⊑c̅′ c̅⊑g′) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ id) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l (⊑-right-contract c̅ₙ⊑c̅′) ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ →
      let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
              (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
              l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (up 𝓋)) (up 𝓋) ⟩
              l ℓ ⟪ c̅ₙ ⟫ ∎) in
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up 𝓋) x) , ♥ ,
        ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) c̅₁⊑g′ ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) (id g′) id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ id) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l ℓ⊑c̅′ ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑c̅′) ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ →
      let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
              (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
              l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (up 𝓋)) (up 𝓋) ⟩
              l ℓ ⟪ c̅ₙ ⟫ ∎) in
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up 𝓋) x) , ♥ ,
        ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) (⊑-left-contract c̅ₙ⊑c̅′) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castr (⊑-castl ⊑-l c̅₁⊑ℓ) g₁⊑c̅′ ⟩ =
  case catchupₗ (c̅₁ ⨟ c̅) _ 𝓋′ (comp-pres-⊑-bl (comp-pres-⊑-lr c̅₁⊑ℓ g₁⊑c̅′) c̅⊑g′) of λ where
  ⟨ id _ , id , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ id) id ⟩
             l ℓ ⟪ id (l ℓ) ⟫ —→⟨ β-id ⟩
             l ℓ ∎) in
    ⟨ l ℓ , v-l , ♣ , ⊑-castr ⊑-l (⊑-right-contract c̅ₙ⊑c̅′) ⟩
  ⟨ c̅ₙ , inj 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
            (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
             l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩
             l ℓ ⟪ c̅ₙ ⟫ ∎) in
    ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (inj 𝓋) (λ ())) , ♥ ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
  ⟨ c̅ₙ , up 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
    case (precₗ→⊑ _ _ c̅ₙ⊑c̅′) of λ where
    ⟨ _ , l⊑l ⟩ →
      let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
              (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩
              l ℓ ⟪ c̅₁ ⨟ c̅ ⟫   —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅ₙ (up 𝓋)) (up 𝓋) ⟩
              l ℓ ⟪ c̅ₙ ⟫ ∎) in
      ⟨ l ℓ ⟪ c̅ₙ ⟫ , v-cast (ir (up 𝓋) x) , ♥ ,
        ⊑-cast ⊑-l c̅ₙ⊑c̅′ ⟩
catchup (v-cast (ir 𝓋′ x)) (⊑-castr {g} {g₁′} {g₂′} {M} {M′} {c̅′} M⊑V′ g⊑c̅)
  with catchup v-l M⊑V′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  ⟨ l ℓ , v-l , M↠V , ⊑-castr ⊑-l g⊑c̅ ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V ,
    ⊑-castr (⊑-castl ⊑-l c̅₁⊑ℓ) g⊑c̅ ⟩

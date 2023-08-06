module LabelExpr.Sim where

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
open import LabelExpr.CatchUp

open import CoercionExpr.CoercionExpr renaming (_—→⟨_⟩_ to _—→ₗ⟨_⟩_; _∎ to _∎ₗ)
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SyntacComp
open import CoercionExpr.GG hiding (sim) renaming (catchup to catchupₗ)


sim : ∀ {g g′} {M M′ N′}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g′
  → M′ —→ₑ N′
    ---------------------------------------------
  → ∃[ N ] (M —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g ⊑ g′)


sim-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′ N′} {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
  → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g₁′
  → ⊢ c̅ ⊑ c̅′
  → M′ ⟪ c̅′ ⟫ —→ₑ N′
    ---------------------------------------------------
  → ∃[ N ] (M ⟪ c̅ ⟫ —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g₂ ⊑ g₂′)
sim-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ (ξ M′→N′)
  with sim M⊑M′ M′→N′
... | ⟨ N , M→N , N⊑N′ ⟩ =
  ⟨ N ⟪ c̅ ⟫ , plug-congₑ M→N , ⊑-cast N⊑N′ c̅⊑c̅′ ⟩
sim-cast M⊑M′ c̅⊑c̅′ ξ-blame =
  ⟨ _ , _ ∎ , ⊑-blame (⊢cast (proj₁ (prec→⊢ M⊑M′))) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
sim-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑id β-id
  with catchup v-l M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case catchupₗ _ _ id c̅⊑id of λ where
  ⟨ c̅₁ , id , _ ∎ₗ , ⊑-id l⊑l ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ β-id ⟩ _ ∎) in
    ⟨ l ℓ , ♥ , ⊑-l ⟩
  ⟨ c̅₁ , id , _ —→ₗ⟨ r ⟩ r* , ⊑-id l⊑l ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ β-id ⟩ _ ∎) in
    ⟨ l ℓ , ♥ , ⊑-l ⟩
  ⟨ c̅₁ , inj 𝓋 , _ ∎ₗ , c̅₁⊑id ⟩ →
    ⟨ l ℓ ⟪ c̅₁ ⟫ , plug-congₑ M↠V , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
  ⟨ c̅₁ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
  ⟨ c̅₁ , up 𝓋 , _ ∎ₗ , c̅₁⊑id ⟩ →
    ⟨ l ℓ ⟪ c̅₁ ⟫ , plug-congₑ M↠V , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
  ⟨ c̅₁ , up 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) (up 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  let c̅₁⨟c̅⊑id : ⊢ c̅₁ ⨟ c̅ ⊑ id (l ℓ)
      c̅₁⨟c̅⊑id = comp-pres-⊑-lb c̅₁⊑ℓ c̅⊑id in
  case catchupₗ _ _ id c̅₁⨟c̅⊑id of λ where
  ⟨ c̅₁ , id , c̅₁⨟c̅↠c̅₁ , ⊑-id l⊑l ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
                      (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅₁ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) in
    ⟨ l ℓ , ♥ , ⊑-l ⟩
  ⟨ c̅₁ , inj 𝓋 , c̅₁⨟c̅↠c̅₁ , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
                      (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅₁ (inj 𝓋)) (inj 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
  ⟨ c̅₁ , up 𝓋 , c̅₁⨟c̅↠c̅₁ , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
                      (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅₁ (up 𝓋)) (up 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
sim-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ (cast c̅′↠c̅ₙ 𝓋′)
  with catchup v-l M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′↠c̅ₙ) of λ where
  ⟨ c̅₁ , 𝓋 , _ ∎ₗ , c̅₁⊑c̅ₙ ⟩ →
    ⟨ l ℓ ⟪ c̅₁ ⟫ , plug-congₑ M↠V , ⊑-cast ⊑-l c̅₁⊑c̅ₙ ⟩
  ⟨ c̅₁ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅₁⊑c̅ₙ ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-cast ⊑-l c̅₁⊑c̅ₙ ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  let c̅₁⨟c̅⊑c̅′ : ⊢ c̅₁ ⨟ c̅ ⊑ c̅′
      c̅₁⨟c̅⊑c̅′ = comp-pres-⊑-lb c̅₁⊑ℓ c̅⊑c̅′ in
  let ⟨ c̅₂ , 𝓋 , c̅₁⨟c̅↠c̅₂ , c̅₂⊑c̅ₙ ⟩ = sim-mult c̅₁⨟c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′↠c̅ₙ) in
  let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
                    (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅₁⨟c̅↠c̅₂ 𝓋) 𝓋 ⟩ _ ∎) in
  ⟨ l ℓ ⟪ c̅₂ ⟫ , ♥ , ⊑-cast ⊑-l c̅₂⊑c̅ₙ ⟩
sim-cast M⊑M′ c̅⊑c̅′ (blame _)
  with prec→⊢ M⊑M′
... | ⟨ ⊢M , ⊢l ⟩ = ⟨ _ , _ ∎ , ⊑-blame (⊢cast ⊢M) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
sim-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ (comp i′)
  with catchup (v-cast i′) M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-castr ⊑-l ℓ⊑c̅ᵢ ⟩ =
  ⟨ l ℓ ⟪ c̅ ⟫ , plug-congₑ M↠V , ⊑-cast ⊑-l (comp-pres-⊑-rb ℓ⊑c̅ᵢ c̅⊑c̅′) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , prec ⟩
  with prec→⊢ prec
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv prec
... | ⟨ refl , c̅₁⊑c̅ᵢ ⟩ =
  let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
                    (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩ _ ∎) in
  ⟨ l ℓ ⟪ c̅₁ ⨟ c̅ ⟫ , ♣ ,
    ⊑-cast ⊑-l (comp-pres-⊑ c̅₁⊑c̅ᵢ c̅⊑c̅′) ⟩


sim-castr : ∀ {g g₁′ g₂′} {M M′ N′} {c̅′ : CExpr g₁′ ⇒ g₂′}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g₁′
  → ⊢r g ⊑ c̅′
  → M′ ⟪ c̅′ ⟫ —→ₑ N′
    ---------------------------------------------------
  → ∃[ N ] (M —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g ⊑ g₂′)
sim-castr M⊑M′ g⊑c̅′ (ξ M′→N′)
  with sim M⊑M′ M′→N′
... | ⟨ N , M↠N , N⊑N′ ⟩ = ⟨ N , M↠N , ⊑-castr N⊑N′ g⊑c̅′ ⟩
sim-castr M⊑M′ g⊑c̅′ ξ-blame =
  ⟨ _ , _ ∎ , ⊑-blame (proj₁ (prec→⊢ M⊑M′)) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
sim-castr M⊑M′ (⊑-id g⊑ℓ) β-id
  with catchup v-l M⊑M′
... | ⟨ V , v , M↠V , V⊑M′ ⟩ = ⟨ V , M↠V , V⊑M′ ⟩
sim-castr M⊑M′ g⊑c̅′ (cast c̅′↠c̅ₙ 𝓋′) =
  let id⊑c̅′ = ⊑-right-expand g⊑c̅′ in
  case sim-mult id⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′↠c̅ₙ) of λ where
  ⟨ _ , _ , _ ∎ₗ , id⊑c̅ₙ ⟩ →
    ⟨ _ , _ ∎ , ⊑-castr M⊑M′ (⊑-right-contract id⊑c̅ₙ) ⟩
sim-castr M⊑M′ g⊑c̅′ (blame _) =
  ⟨ _ , _ ∎ , ⊑-blame (proj₁ (prec→⊢ M⊑M′)) (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
sim-castr M⊑M′ g⊑c̅′ (comp i′)
  with catchup (v-cast i′) M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-castr ⊑-l ℓ⊑c̅ᵢ ⟩ =
  ⟨ l ℓ , M↠V , ⊑-castr ⊑-l (comp-pres-⊑-rr ℓ⊑c̅ᵢ g⊑c̅′) ⟩
... | ⟨ l ℓ ⟪ c̅ ⟫ , v-cast i , M↠V , prec ⟩
  with prec→⊢ prec
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv prec
... | ⟨ refl , c̅⊑c̅ᵢ ⟩ =
  ⟨ l ℓ ⟪ c̅ ⟫ , M↠V , ⊑-cast ⊑-l (comp-pres-⊑-br c̅⊑c̅ᵢ g⊑c̅′) ⟩


sim (⊑-cast M⊑M′ c̅⊑c̅′) M′→N′ = sim-cast M⊑M′ c̅⊑c̅′ M′→N′
sim (⊑-castl M⊑M′ c̅⊑g′) M′→N′
  with sim M⊑M′ M′→N′
... | ⟨ N , M↠N , N⊑N′ ⟩ = ⟨ N ⟪ _ ⟫ , plug-congₑ M↠N , ⊑-castl N⊑N′ c̅⊑g′ ⟩
sim (⊑-castr M⊑M′ g⊑c̅′) M′→N′ = sim-castr M⊑M′ g⊑c̅′ M′→N′

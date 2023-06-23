module LabelExpr.SimBack where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels

open import LabelExpr.LabelExpr
open import LabelExpr.CatchUpBack

open import CoercionExpr.CoercionExpr
  hiding (_—→⟨_⟩_; _∎; Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SyntacComp
open import CoercionExpr.GG renaming (catchup-back to catchup-backₗ; sim-back to sim-backₗ)

sim-back : ∀ {g g′} {M M′ N}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g′
  → M —→ₑ N
    -----------------------------------------------------------------
  → ∃[ N′ ] (M′ —↠ₑ N′) × (⊢ N ⊑ N′ ⇐ g ⊑ g′)

sim-back-blame : ∀ {g g′} {M′} {p}
  → ⊢ blame p ⊑ M′ ⇐ g ⊑ g′
  → ∃[ q ] (M′ —↠ₑ blame q) × (⊢ blame p ⊑ blame q ⇐ g ⊑ g′)
sim-back-blame (⊑-castr blame⊑M′ g⊑c̅′)
  with sim-back-blame blame⊑M′
... | ⟨ q , M′↠blame , prec ⟩ =
  ⟨ q , ↠ₑ-trans (plug-congₑ M′↠blame) (blame q ⟪ _ ⟫ —→⟨ ξ-blame ⟩ blame q ∎) ,
    ⊑-blame ⊢blame (proj₂ (prec-right→⊑ _ g⊑c̅′)) ⟩
sim-back-blame (⊑-blame x y) = ⟨ _ , blame _ ∎ , ⊑-blame x y ⟩

sim-back-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′ N} {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
  → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g₁′
  → ⊢ c̅ ⊑ c̅′
  → M ⟪ c̅ ⟫ —→ₑ N
  → ∃[ N′ ] (M′ ⟪ c̅′ ⟫ —↠ₑ N′) × (⊢ N ⊑ N′ ⇐ g₂ ⊑ g₂′)
sim-back-cast M⊑M′ c̅⊑c̅′ (ξ M→N)
  with sim-back M⊑M′ M→N
... | ⟨ N′ , M′↠N′ , N⊑N′ ⟩ =
  ⟨ N′ ⟪ _ ⟫ , plug-congₑ M′↠N′ , ⊑-cast N⊑N′ c̅⊑c̅′ ⟩
sim-back-cast M⊑M′ c̅⊑c̅′ ξ-blame
  with sim-back-blame M⊑M′
... | ⟨ q , M′↠⊥ , prec ⟩ =
  ⟨ blame q , ↠ₑ-trans (plug-congₑ M′↠⊥) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame ⊢blame (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
sim-back-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ β-id
 with prec→⊑ M⊑M′
... | l⊑l with catchup-back v-l M⊑M′
...   | ⟨ blame p , fail , M′↠blame , ⊑-blame ⊢l l⊑l ⟩ =
  ⟨ blame p ,
    ↠ₑ-trans (plug-congₑ M′↠blame) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame ⊢l (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
...   | ⟨ l ℓ , success v-l , M′↠V′ , ⊑-l ⟩ =
  ⟨ l ℓ ⟪ c̅′ ⟫ , plug-congₑ M′↠V′ , ⊑-castr ⊑-l (⊑-right-contract c̅⊑c̅′) ⟩
...   | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castr ⊑-l ℓ⊑c̅′₁ ⟩ =
  ⟨ l ℓ ⟪ c̅′₁ ⟫ ⟪ c̅′ ⟫ , plug-congₑ M′↠V′ ,
    ⊑-castr (⊑-castr ⊑-l ℓ⊑c̅′₁) (⊑-right-contract c̅⊑c̅′) ⟩
sim-back-cast M⊑M′ c̅⊑c̅′ (cast c̅↠c̅ₙ 𝓋)
 with prec→⊑ M⊑M′
... | l⊑l with catchup-back v-l M⊑M′
...   | ⟨ blame p , fail , M′↠blame , ⊑-blame ⊢l l⊑l ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠blame) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
...   | ⟨ l ℓ , success v-l , M′↠V′ , ⊑-l ⟩ =
  case sim-back-success c̅⊑c̅′ 𝓋 c̅↠c̅ₙ of λ where
  ⟨ ⊥ _ _ p , c̅′↠⊥ , v-⊥ _ ⟩ →
    ⟨ blame p ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v id c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅ₙ′ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl ⊑-l (⊑-left-contract c̅ₙ⊑c̅ₙ′) ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v (up id) c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ l low ⟪ id _ ⨾ ↑ ⟫ ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅ₙ′ (up id) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅ₙ′ ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v (inj 𝓋′) c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ cast c̅′↠c̅ₙ′ (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅ₙ′ ⟩
...   | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castr ⊑-l ℓ⊑c̅′₁ ⟩ =
  case sim-back-success (comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′) 𝓋 c̅↠c̅ₙ of λ where
  ⟨ ⊥ _ _ p , c̅′↠⊥ , v-⊥ _ ⟩ →
    ⟨ blame p ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v id c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast c̅′↠c̅ₙ′ id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
      ⊑-castl ⊑-l (⊑-left-contract c̅ₙ⊑c̅ₙ′) ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v (up id) c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ l low ⟪ id _ ⨾ ↑ ⟫ ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast c̅′↠c̅ₙ′ (up id) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅ₙ′ ⟩
  ⟨ c̅ₙ′ , c̅′↠c̅ₙ′ , v-v (inj 𝓋′) c̅ₙ⊑c̅ₙ′ ⟩ →
    ⟨ _ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ cast c̅′↠c̅ₙ′ (inj 𝓋′) ⟩ _ ∎) ,
      ⊑-cast ⊑-l c̅ₙ⊑c̅ₙ′ ⟩
sim-back-cast M⊑M′ c̅⊑c̅′ (blame c̅↠⊥) with prec→⊑ M⊑M′
... | l⊑l with catchup-back v-l M⊑M′
...   | ⟨ blame p , fail , M′↠blame , ⊑-blame ⊢l l⊑l ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠blame) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame ⊢blame (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
...   | ⟨ l ℓ , success v-l , M′↠V′ , ⊑-l ⟩ =
  case sim-back-fail c̅⊑c̅′ c̅↠⊥ of λ where
  ⟨ q , c̅′↠⊥ , prec ⟩ →
    ⟨ blame q ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (l ℓ ⟪ _ ⟫ —→⟨ blame c̅′↠⊥ ⟩ blame q ∎) ,
      ⊑-blame ⊢blame (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
...   | ⟨ l ℓ ⟪ c̅′₁ ⟫ , success (v-cast i₁) , M′↠V′ , ⊑-castr ⊑-l ℓ⊑c̅′₁ ⟩ =
  case sim-back-fail (comp-pres-⊑-rb ℓ⊑c̅′₁ c̅⊑c̅′) c̅↠⊥ of λ where
  ⟨ q , c̅′↠⊥ , prec ⟩ →
    ⟨ blame q ,
      ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i₁ ⟩ _ —→⟨ blame c̅′↠⊥ ⟩ _ ∎) ,
      ⊑-blame ⊢blame (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
sim-back-cast {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ (comp i)
  with catchup-back (v-cast i) M⊑M′
... | ⟨ blame p , fail , M′↠blame , V⊑blame ⟩ =
  ⟨ blame p , ↠ₑ-trans (plug-congₑ M′↠blame) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
    ⊑-blame (⊢cast ⊢l) (proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)) ⟩
... | ⟨ l ℓ′ , success v-l , M′↠V′ , ⊑-castl ⊑-l c̅ᵢ⊑ℓ ⟩ =
  ⟨ l ℓ′ ⟪ c̅′ ⟫ , plug-congₑ M′↠V′ , ⊑-cast ⊑-l (comp-pres-⊑-lb c̅ᵢ⊑ℓ c̅⊑c̅′) ⟩
... | ⟨ l ℓ′ ⟪ c̅ᵢ′ ⟫ , success (v-cast i′) , M′↠V′ , V⊑V′ ⟩
  with prec→⊢ V⊑V′
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv V⊑V′
... | ⟨ refl , c̅ᵢ⊑c̅ᵢ′ ⟩ =
  ⟨ l ℓ′ ⟪ c̅ᵢ′ ⨟ c̅′ ⟫ , ↠ₑ-trans (plug-congₑ M′↠V′) (_ —→⟨ comp i′ ⟩ _ ∎) ,
    ⊑-cast ⊑-l (comp-pres-prec c̅ᵢ⊑c̅ᵢ′ c̅⊑c̅′) ⟩

sim-back-castl : ∀ {g₁ g₂ g′} {M M′ N} {c̅ : CExpr g₁ ⇒ g₂}
  → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g′
  → ⊢l c̅ ⊑ g′
  → M ⟪ c̅ ⟫ —→ₑ N
  → ∃[ N′ ] (M′ —↠ₑ N′) × (⊢ N ⊑ N′ ⇐ g₂ ⊑ g′)
sim-back-castl M⊑M′ c̅⊑g′ (ξ M→N)
  with sim-back M⊑M′ M→N
... | ⟨ N′ , M′↠N′ , N⊑N′ ⟩ = ⟨ N′ , M′↠N′ , ⊑-castl N⊑N′ c̅⊑g′ ⟩
sim-back-castl M⊑M′ c̅⊑g′ ξ-blame
  with sim-back-blame M⊑M′
... | ⟨ p , M′↠blame , prec ⟩ =
  ⟨ blame p , M′↠blame , ⊑-blame ⊢blame (proj₂ (prec-left→⊑ _ c̅⊑g′)) ⟩
sim-back-castl M⊑M′ (⊑-id l⊑l) β-id
  with catchup-back v-l M⊑M′
... | ⟨ N′ , _ , M′↠N′ , V⊑N′ ⟩ = ⟨ N′ , M′↠N′ , V⊑N′ ⟩
sim-back-castl M⊑M′ c̅⊑g′ (cast c̅↠c̅ₙ 𝓋)
  with catchup-back v-l M⊑M′
... | ⟨ N′ , _ , M′↠N′ , V⊑N′ ⟩ =
  ⟨ N′ , M′↠N′ , ⊑-castl V⊑N′ (pres-prec-left-mult c̅⊑g′ c̅↠c̅ₙ) ⟩
sim-back-castl M⊑M′ c̅⊑g′ (blame c̅↠⊥) = contradiction c̅↠⊥ (prec-left-safe c̅⊑g′)
sim-back-castl M⊑M′ c̅⊑g′ (comp i)
  with catchup-back (v-cast i) M⊑M′
... | ⟨ blame p , fail , M′↠blame , V⊑blame ⟩ =
  ⟨ blame p , M′↠blame , ⊑-blame (⊢cast ⊢l) (proj₂ (prec-left→⊑ _ c̅⊑g′)) ⟩
... | ⟨ l ℓ′ , success v-l , M′↠V′ , ⊑-castl ⊑-l c̅ᵢ⊑ℓ ⟩ =
  ⟨ l ℓ′ , M′↠V′ , ⊑-castl ⊑-l (comp-pres-⊑-ll c̅ᵢ⊑ℓ c̅⊑g′) ⟩
... | ⟨ l ℓ′ ⟪ c̅′ ⟫ , success (v-cast i′) , M′↠V′ , ⊑-cast ⊑-l c̅ᵢ⊑c̅′ ⟩ =
  ⟨ _ , M′↠V′ , ⊑-cast ⊑-l (comp-pres-⊑-bl c̅ᵢ⊑c̅′ c̅⊑g′) ⟩
... | ⟨ l ℓ′ ⟪ c̅′ ⟫ , success (v-cast i′) , M′↠V′ , ⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) c̅ᵢ⊑g′ ⟩ =
  ⟨ _ , M′↠V′ , ⊑-cast ⊑-l (comp-pres-⊑-bl (comp-pres-⊑-rl ℓ⊑c̅′ c̅ᵢ⊑g′) c̅⊑g′) ⟩
... | ⟨ l ℓ′ ⟪ c̅′ ⟫ , success (v-cast i′) , M′↠V′ , ⊑-castr (⊑-castl ⊑-l c̅ᵢ⊑ℓ) g₁⊑c̅′ ⟩ =
  ⟨ _ , M′↠V′ , ⊑-cast ⊑-l (comp-pres-⊑-bl (comp-pres-⊑-lr c̅ᵢ⊑ℓ g₁⊑c̅′) c̅⊑g′) ⟩

sim-back (⊑-cast M⊑M′ c̅⊑c̅′) M⟨c⟩→N = sim-back-cast M⊑M′ c̅⊑c̅′ M⟨c⟩→N
sim-back (⊑-castl M⊑M′ c̅⊑g′) M⟨c⟩→N = sim-back-castl M⊑M′ c̅⊑g′ M⟨c⟩→N
sim-back (⊑-castr M⊑M′ g⊑c̅′) M→N
  with sim-back M⊑M′ M→N
... | ⟨ N′ , M′↠N′ , N⊑N′ ⟩ =
  ⟨ N′ ⟪ _ ⟫ , plug-congₑ M′↠N′ , ⊑-castr N⊑N′ g⊑c̅′ ⟩
sim-back (⊑-blame ⊢M g⊑g′) M→N =
  ⟨ _ , _ ∎ , ⊑-blame (preserve ⊢M M→N) g⊑g′ ⟩

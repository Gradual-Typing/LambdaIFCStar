module LabelExpr.SimBack where

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
open import LabelExpr.CatchUpBack

open import CoercionExpr.CoercionExpr hiding (Progress; progress; plug-cong; ↠-trans)
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
sim-back-cast M⊑M′ c̅⊑c̅′ β-id = {!!}
sim-back-cast M⊑M′ c̅⊑c̅′ (cast x x₁) = {!!}
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

sim-back-cast M⊑M′ c̅⊑c̅′ (comp x) = {!!}

sim-back (⊑-cast M⊑M′ c̅⊑c̅′) M⟨c⟩→N = sim-back-cast M⊑M′ c̅⊑c̅′ M⟨c⟩→N
sim-back (⊑-castl M⊑M′ c̅⊑g′) M⟨c⟩→N = {!!}
sim-back (⊑-castr M⊑M′ g⊑c̅′) M→N
  with sim-back M⊑M′ M→N
... | ⟨ N′ , M′↠N′ , N⊑N′ ⟩ =
  ⟨ N′ ⟪ _ ⟫ , plug-congₑ M′↠N′ , ⊑-castr N⊑N′ g⊑c̅′ ⟩
sim-back (⊑-blame ⊢M g⊑g′) M→N =
  ⟨ _ , _ ∎ , ⊑-blame (preserve ⊢M M→N) g⊑g′ ⟩

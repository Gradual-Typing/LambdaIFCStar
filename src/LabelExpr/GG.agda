module LabelExpr.GG where

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
open import CoercionExpr.GG hiding (sim; sim-mult) renaming (catchup to catchupₗ)
open import LabelExpr.Sim using (sim)


sim-mult : ∀ {g g′} {M M′ V′}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g′
  → M′ —↠ₑ V′
  → LVal V′
    --------------------------------------------------------
  → ∃[ V ] (LVal V) × (M —↠ₑ V) × (⊢ V ⊑ V′ ⇐ g ⊑ g′)
sim-mult M⊑V′ (V′ ∎) v′ = catchup v′ M⊑V′
sim-mult M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠V′) v′ =
  let ⟨ N , M↠N , N⊑N′ ⟩ = sim M⊑M′ M′→N′ in
  let ⟨ V , v , N↠V , V⊑V′ ⟩ = sim-mult N⊑N′ N′↠V′ v′ in
  ⟨ V , v , ↠ₑ-trans M↠N N↠V , V⊑V′ ⟩

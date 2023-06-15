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
sim-back M⊑M′ M→N = {!!}

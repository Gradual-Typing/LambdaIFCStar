module LabelExpr.Erasure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.Erasure
open import LabelExpr.LabelExpr

ϵₑ : LExpr → StaticLabel
ϵₑ (l high)  = high
ϵₑ (l low)   = low
ϵₑ (e ⟪ c̅ ⟫) = (ϵₑ e) ⋎ (ϵ c̅)
ϵₑ (blame p) = high


{- Properties of erasure -}

ϵₑ-high : ∀ {e} → ⊢ e ⇐ l high → ϵₑ e ≡ high
ϵₑ-high ⊢l = refl
ϵₑ-high (⊢cast {M = e} {c̅} ⊢e) rewrite ϵ-high c̅ | ℓ⋎high≡high {ϵₑ e} = refl
ϵₑ-high ⊢blame = refl

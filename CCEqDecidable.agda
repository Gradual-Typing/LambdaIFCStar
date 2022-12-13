module CCEqDecidable where

open import Data.Maybe
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Syntax using (Var)
open import Utils
open import Types
open import HeapContext
open import TypeBasedCast
open import CC


const-eq? : ∀ {ι} → (k₁ k₂ : rep ι) → Dec (k₁ ≡ k₂)
const-eq? {Bool} false false = yes refl
const-eq? {Bool} false true  = no λ ()
const-eq? {Bool} true false  = no λ ()
const-eq? {Bool} true true   = yes refl
const-eq? {Unit} tt tt       = yes refl

addr-eq? : ∀ (a₁ a₂ : Addr) → Dec (a₁ ≡ a₂)
addr-eq? (a⟦ ℓ̂₁ ⟧ n₁) (a⟦ ℓ̂₂ ⟧ n₂) =
  case ℓ̂₁ =? ℓ̂₂ of λ where
  (yes refl) →
    case n₁ ≟ n₂ of λ where
    (yes refl) → yes refl
    (no  neq)  → no λ { refl → contradiction refl neq }
  (no  neq)  → no λ { refl → contradiction refl neq }

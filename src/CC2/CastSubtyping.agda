module CC2.CastSubtyping where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import CoercionExpr.SyntacComp using (comp-not-val)
open import CC2.Statics
open import CC2.CastReduction


{- Cast to value justifies label subtyping -}
cast-≼ : ∀ {Γ Σ gc ℓv} {S T ℓ₁ ℓ₂} {V W} {c : Cast S of l ℓ₁ ⇒ T of l ℓ₂}
  → Value V
  → Γ ; Σ ; gc ; ℓv ⊢ V ⇐ S of l ℓ₁
  → V ⟨ c ⟩ —↠ W
  → Value W
    --------------------------------------
  → ℓ₁ ≼ ℓ₂
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-base id x)) = contradiction refl x
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-base (up id) _)) = low ≼high
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-ref id))      = ≼-refl
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-ref (up id))) = low ≼high
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-fun id))      = ≼-refl
cast-≼ v ⊢V (_ ∎) (V-cast _ (ir-fun (up id))) = low ≼high
cast-≼ v ⊢V (_ —→⟨ cast x x₁ x₂ ⟩ ↠W) w = {!!}
cast-≼ v ⊢V (_ —→⟨ cast-blame x x₁ ⟩ ↠W) w = {!!}
cast-≼ v ⊢V (_ —→⟨ cast-id ⟩ ↠W) w = {!!}
cast-≼ v (⊢cast ⊢V) (_ —→⟨ cast-comp V-const (ir-base x x₁) ⟩ ↠W) w = {!!}
cast-≼ v (⊢cast ⊢V) (_ —→⟨ cast-comp V-addr (ir-ref x) ⟩ ↠W) w = {!!}
cast-≼ v (⊢cast ⊢V) (_ —→⟨ cast-comp V-ƛ (ir-fun id) ⟩ ↠W) w = {!!}
cast-≼ {c = cast (fun d̅ c d) c̅} v (⊢cast ⊢V) (_ —→⟨ cast-comp V-ƛ (ir-fun (up id)) ⟩ ↠W) w
  with ↠W | w
... | _ —→⟨ cast V-ƛ →⁺c̅ₙ id ⟩ r* | w =
  case comp-security (up id) (→⁺-impl-↠ →⁺c̅ₙ) id of λ where
  ()
... | _ —→⟨ cast V-ƛ →⁺c̅ₙ (up id) ⟩ r* | w = {!!}
... | _ —→⟨ cast-blame vᵣ c̅↠⊥ ⟩ _ ∎ | V-raw ()
... | _ ∎ | V-cast vᵣ (ir-fun 𝓋) = contradiction 𝓋 (comp-not-val _ _)

module LabelExpr.NSU where

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
open import LabelExpr.Stamping
open import LabelExpr.GG


sim-nsu-ref : ∀ {V V′ W′} {ℓ} {p q}
  → ⊢ V ⊑ V′ ⇐ ⋆ ⊑ ⋆
  → (v  : LVal V )
  → (v′ : LVal V′)
  → V′ ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ —↠ₑ W′
  → LVal W′
    -------------------------------------------------------------
  → ∃[ W ] (LVal W) × (V ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l q ⟫ —↠ₑ W)
sim-nsu-ref {V} {V′} {W′} {ℓ} {p} {q} V⊑V′ v v′ ↠W′ w′ =
  case sim-mult prec ↠W′ w′ of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where
    prec : ⊢ V  ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l q ⟫        ⊑
             V′ ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ ⇐ l ℓ ⊑ l ℓ
    prec = ⊑-cast V⊑V′ (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)


sim-nsu-assign : ∀ {V V′ W′} {g g′ ℓ ℓ′ ℓ̂} {p q}
  → ⊢ V ⊑ V′ ⇐ g ⊑ g′
  → (v  : LVal V )
  → (v′ : LVal V′)
  → ℓ ≼ ℓ′
  → stamp!ₑ V′ v′ ℓ′ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ W′
  → LVal W′
    ---------------------------------------------------------------------------
  → ∃[ W ] (LVal W) × (stamp!ₑ V v ℓ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l q ⟫ —↠ₑ W)
sim-nsu-assign {V} {V′} {W′} {g} {g′} {ℓ} {ℓ′} {ℓ̂} {p} {q} V⊑V′ v v′ ℓ≼ℓ′ ↠W′ w′ =
  case sim-mult prec ↠W′ w′ of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where
    prec : ⊢ stamp!ₑ V  v  ℓ  ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l q ⟫        ⊑
             stamp!ₑ V′ v′ ℓ′ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ ⇐ l ℓ̂ ⊑ l ℓ̂
    prec = ⊑-cast (stamp!ₑ-prec v v′ V⊑V′ ℓ≼ℓ′) (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)

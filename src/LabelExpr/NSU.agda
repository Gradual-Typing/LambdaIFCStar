module LabelExpr.NSU where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction; ¬?)
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

sim-nsu-ref-left : ∀ {V V′} {ℓ₁ ℓ₂} {p}
  → ⊢ V ⊑ V′ ⇐ ⋆ ⊑ l ℓ₁
  → (v  : LVal V )
  → (v′ : LVal V′)
  → ℓ₁ ≼ ℓ₂
    -------------------------------------------------------------
  → ∃[ W ] (LVal W) × (V ⟪ coerceₗ {⋆} {l ℓ₂} ≾-⋆l p ⟫ —↠ₑ W)
sim-nsu-ref-left {V} {V′} {p = p} V⊑V′ v v′ l≼l =
  case catchup v′ prec of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where
    prec : ⊢ V  ⟪ id ⋆ ⨾ low ?? p ⟫ ⊑ V′ ⇐ l low ⊑ l low
    prec = ⊑-castl V⊑V′ (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)
sim-nsu-ref-left {V} {V′} {p = p} V⊑V′ v v′ l≼h
  with prec→⊢ V⊑V′ | v′
... | ⟨ _ , ⊢cast ⊢l ⟩ | v-cast (ir id low≢low) =
  contradiction refl (recompute (¬? (_ ==? _)) low≢low)
... | ⟨ _ , ⊢l ⟩ | v-l =
  case catchup (v-cast (ir (up id) λ ())) prec of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where  {- we need to insert an upcast on the more precise side -}
    prec : ⊢ V  ⟪ id ⋆ ⨾ high ?? p ⟫           ⊑
             V′ ⟪ id (l low) ⨾ ↑  ⟫ ⇐ l high ⊑ l high
    prec = ⊑-cast V⊑V′ (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)
sim-nsu-ref-left {V} {V′} {p = p} V⊑V′ v v′ h≼h =
  case catchup v′ prec of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where
    prec : ⊢ V  ⟪ id ⋆ ⨾ high ?? p ⟫ ⊑ V′ ⇐ l high ⊑ l high
    prec = ⊑-castl V⊑V′ (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)


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


sim-nsu-assign-left : ∀ {V V′} {g ℓ₁ ℓ₂ ℓ₃} {p}
  → ⊢ V ⊑ V′ ⇐ g ⊑ l ℓ₁
  → (v  : LVal V )
  → (v′ : LVal V′)
  → ℓ₁ ≼ ℓ₃ → ℓ₂ ≼ ℓ₃
    ---------------------------------------------------------------------------
   → ∃[ W ] (LVal W) × (stamp!ₑ V v ℓ₂ ⟪ coerceₗ {⋆} {l ℓ₃} ≾-⋆l p ⟫ —↠ₑ W)
sim-nsu-assign-left {V} {V′} {g′} {.low}  {.low}  {.low}  {p} V⊑V′ v v′ l≼l l≼l = {!!}
sim-nsu-assign-left {V} {V′} {g′} {.low}  {.low}  {.high} {p} V⊑V′ v v′ l≼h l≼h
  with prec→⊢ V⊑V′ | v′
... | ⟨ ⊢V , ⊢V′ ⟩ =
  case ⟨ ⊢V′ , v′ ⟩ of λ where
  ⟨ ⊢l , v-l ⟩ →
    case catchup {!v-cast!} prec of λ where
    ⟨ W , w , ↠W , _ ⟩ → {!!}
  ⟨ ⊢cast ⊢l , v-cast (ir id x) ⟩ → contradiction refl (recompute (¬? (_ ==? _)) x)
      where
      prec : ⊢ stamp!ₑ V  v  low  ⟪ id ⋆ ⨾ high ?? p ⟫        ⊑
               stampₑ  V′ v′ low ⟪ id (l low) ⨾ ↑ ⟫ ⇐ l high ⊑ l high
      prec = ⊑-cast (stamp!ₑ-left-prec v v′ V⊑V′) (⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l)
sim-nsu-assign-left {V} {V′} {g′} {.low}  {.high} {.high} {p} V⊑V′ v v′ l≼h h≼h =
  let ⟨ ⊢V , ⊢V′ ⟩ = prec→⊢ V⊑V′ in
  let v′-stamped = stampₑ-LVal v′ in
  let ♣ : stampₑ V′ v′ high ⟪ id (l high) ⟫ —↠ₑ stampₑ V′ v′ high
      ♣ = cast-id-id v′-stamped (stampₑ-wt v′ ⊢V′) in
  case sim-mult prec ♣ v′-stamped of λ where
  ⟨ W , w , ↠W , _ ⟩ → ⟨ W , w , ↠W ⟩
    where
    prec : ⊢ stamp!ₑ V  v  high  ⟪ id ⋆ ⨾ high ?? p ⟫        ⊑
             stampₑ  V′ v′ high ⟪ id (l high) ⟫ ⇐ l high ⊑ l high
    prec = ⊑-cast (stamp!ₑ-left-prec v v′ V⊑V′) (⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l)
sim-nsu-assign-left {V} {V′} {g′} {.high} {.low}  {.high} {p} V⊑V′ v v′ h≼h l≼h = {!!}
sim-nsu-assign-left {V} {V′} {g′} {.high} {.high} {.high} {p} V⊑V′ v v′ h≼h h≼h = {!!}

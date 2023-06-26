module CC2.Progress where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC2.Statics
open import CC2.Reduction
open import Memory.HeapTyping Term Value _;_;_;_⊢_⇐_


data Progress (M : Term) (μ : Heap) (PC : LExpr) : Set where

  step : ∀ {N μ′}
    → M ∣ μ ∣ PC —→ N ∣ μ′
      ----------------------------- Step
    → Progress M μ PC

  done : Value M
      ----------------------- Done
    → Progress M μ PC

  err : Err M
      ----------------------- Error
    → Progress M μ PC

progress : ∀ {Σ gc A} {PC M μ}
  → (v : LVal PC)
  → ⊢ PC ⇐ gc
  → [] ; Σ ; gc ; ∥ PC ∥ v ⊢ M ⇐ A
  → Σ ⊢ μ
    ------------------------------------------
  → Progress M μ PC
progress vc ⊢PC (⊢var ())
progress _ ⊢PC ⊢const    ⊢μ = done (V-raw V-const)
progress _ ⊢PC (⊢addr _) ⊢μ = done (V-raw V-addr)
progress _ ⊢PC (⊢lam ⊢M) ⊢μ = done (V-raw V-ƛ)
progress {M = prot PC′ (success vc′) ℓ M A} vc ⊢PC (⊢prot ⊢M ⊢PC′ _ eq) ⊢μ =
  case progress vc′ ⊢PC′ ⊢M ⊢μ of λ where
  (step M→M′)  → step (prot-ctx M→M′)
  (err E-blame) → step prot-blame
  (done v)      → step (prot-val v ⊢M)
progress {M = prot (bl p) fail ℓ M A} vc ⊢PC ⊢prot-blame-pc ⊢μ =
  step prot-blame-pc
progress {M = app L M A B ℓ} vc ⊢PC (⊢app ⊢L ⊢M eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = app□ M A B ℓ} L→L′)
  (err E-blame) → step (ξ-blame {F = app□ M A B ℓ})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where
    ⟨ V-ƛ , ⊢lam ⊢N ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′) → step (ξ {F = app L □ (V-raw v) A B ℓ} M→M′)
      (err E-blame) → step (ξ-blame {F = app L □ (V-raw v) A B ℓ})
      (done w) → step (β w vc)
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-ƛ , ⊢cast {c = cast (fun d̅ c d) c̅ₙ} (⊢lam ⊢N) , ir-fun 𝓋 ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′) → step (ξ {F = app L □ (V-cast v i) A B ℓ} M→M′)
      (err E-blame) → step (ξ-blame {F = app L □ (V-cast v i) A B ℓ})
      (done w) →
        case lexpr-sn (stampₑ _ vc ℓ ⟪ d̅ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
        ⟨ PC′ , ↠PC′ , r ⟩ →
          case cast-sn {c = c} w ⊢M of λ where
          ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
            step (app-blame w 𝓋 V⟨c⟩↠blame)
          ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
            step (app-cast w vc 𝓋 ↠PC′ r V⟨c⟩↠V′ v′)
progress {M = app! L M A B g} vc ⊢PC (⊢app! ⊢L ⊢M eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = app!□ M A B g} L→L′)
  (err E-blame) → step (ξ-blame {F = app!□ M A B g})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where
    ⟨ V-ƛ , ⊢lam ⊢N ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′) → step (ξ {F = app! L □ (V-raw v) A B g} M→M′)
      (err E-blame) → step (ξ-blame {F = app! L □ (V-raw v) A B g})
      (done w) →
        case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
        ⟨ PC′ , ↠PC′ , r ⟩ →
          step (β-app! w vc ⊢PC ↠PC′ r)
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-ƛ , ⊢cast {c = cast (fun d̅ c d) c̅ₙ} (⊢lam ⊢N) , ir-fun 𝓋 ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′) → step (ξ {F = app! L □ (V-cast v i) A B g} M→M′)
      (err E-blame) → step (ξ-blame {F = app! L □ (V-cast v i) A B g})
      (done w) →
        case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫ ⟪ d̅ ⟫)
                      (⊢cast (⊢cast (stampₑ-wt vc ⊢PC))) of λ where
        ⟨ PC′ , ↠PC′ , r ⟩ →
          case cast-sn {c = c} w ⊢M of λ where
          ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
            step (app!-blame w 𝓋 V⟨c⟩↠blame)
          ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
            step (app!-cast w vc 𝓋 ⊢PC ↠PC′ r V⟨c⟩↠V′ v′)
progress {M = if L A ℓ M N} vc ⊢PC (⊢if ⊢L ⊢M ⊢N eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = if□ A ℓ M N} L→L′)
  (err E-blame) → step (ξ-blame {F = if□ A ℓ M N})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where
    ⟨ V-const {k =  true} , ⊢const ⟩ → step (β-if-true  vc)
    ⟨ V-const {k = false} , ⊢const ⟩ → step (β-if-false vc)
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-const , ⊢cast ⊢const , ir-base id ℓ≢ℓ ⟩ → contradiction refl ℓ≢ℓ
    ⟨ V-const {k =  true} , ⊢cast ⊢const , ir-base (up id) x ⟩ →
      step (if-true-cast  vc)
    ⟨ V-const {k = false} , ⊢cast ⊢const , ir-base (up id) x ⟩ →
      step (if-false-cast vc)
progress {M = if! L A g M N} vc ⊢PC (⊢if! ⊢L ⊢M ⊢N eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = if!□ A g M N} L→L′)
  (err E-blame) → step (ξ-blame {F = if!□ A g M N})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where
    ⟨ V-const {k =  true} , ⊢const ⟩ →
      case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
      ⟨ PC′ , ↠PC′ , r ⟩ →
        step (β-if!-true  vc ⊢PC ↠PC′ r)
    ⟨ V-const {k = false} , ⊢const ⟩ →
      case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
      ⟨ PC′ , ↠PC′ , r ⟩ →
        step (β-if!-false vc ⊢PC ↠PC′ r)
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-const , ⊢cast ⊢const , ir-base id ℓ≢ℓ ⟩ → contradiction refl ℓ≢ℓ
    ⟨ V-const {k =  true} , ⊢cast ⊢const , ir-base 𝓋 x ⟩ →
      case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
      ⟨ PC′ , ↠PC′ , r ⟩ →
        step (if!-true-cast vc 𝓋 x ⊢PC ↠PC′ r)
    ⟨ V-const {k = false} , ⊢cast ⊢const , ir-base 𝓋 x ⟩ →
      case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫) (⊢cast (stampₑ-wt vc ⊢PC)) of λ where
      ⟨ PC′ , ↠PC′ , r ⟩ →
        step (if!-false-cast vc 𝓋 x ⊢PC ↠PC′ r)
progress {M = `let M A N} vc ⊢PC (⊢let ⊢M ⊢N) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = let□ A N} M→M′)
  (err E-blame) → step (ξ-blame {F = let□ A N})
  (done v)      → step (β-let v)
progress v ⊢PC ⊢M ⊢μ = {!!}
-- progress pc (if L A M N) (⊢if ⊢L ⊢M ⊢N) μ ⊢μ =
--   case progress pc L ⊢L μ ⊢μ of λ where
--   (step L→L′) → step (ξ {F = if□ A M N} L→L′)
--   (done v) →
--     case canonical-const ⊢L v of λ where
--     (Const-base {𝔹} {true} _)  → step β-if-true
--     (Const-base {𝔹} {false} _) → step β-if-false
--   (err (E-error {e})) → step (ξ-err {F = if□ A M N} {e = e})
-- progress pc (if⋆ L A M N) (⊢if⋆ ⊢L ⊢M ⊢N) μ ⊢μ =
--   case progress pc L ⊢L μ ⊢μ of λ where
--   (step L→L′) → step (ξ {F = if⋆□ A M N} L→L′)
--   (done v) →
--     case canonical-const ⊢L v of λ where
--     (Const-inj {𝔹} {true}  {c = cast (` ι of l ℓ′) (` ι of ⋆) _ _} _) → step β-if⋆-true
--     (Const-inj {𝔹} {false} {c = cast (` ι of l ℓ′) (` ι of ⋆) _ _} _) → step β-if⋆-false
--   (err (E-error {e})) → step (ξ-err {F = if⋆□ A M N} {e = e})
-- progress pc (`let M N) (⊢let ⊢M ⊢N) μ ⊢μ =
--   case progress pc M ⊢M μ ⊢μ of λ where
--   (step M→M′) → step (ξ {F = let□ N} M→M′)
--   (done v) → step (β-let v)
--   (err (E-error {e})) → step (ξ-err {F = let□ N} {e = e})
-- progress pc (ref⟦ ℓ ⟧ M) (⊢ref ⊢M pc′≼ℓ) μ ⊢μ =
--   step ref-static
-- progress pc (ref?⟦ ℓ ⟧ M p) (⊢ref? ⊢M) μ ⊢μ =
--   case pc ≼? ℓ of λ where
--   (yes pc≼ℓ) → step (ref?-ok pc≼ℓ)
--   (no  pc⋠ℓ) → step (ref?-fail pc⋠ℓ)
-- progress {Σ} pc (ref✓⟦ ℓ ⟧ M) (⊢ref✓ ⊢M pc≼ℓ) μ ⊢μ =
--   case progress pc M ⊢M μ ⊢μ of λ where
--     (step M→M′) → step (ξ {F = ref✓⟦ ℓ ⟧□} M→M′)
--     (done v) →
--       let ⟨ n , fresh ⟩ = gen-fresh μ in step (ref v fresh)
--     (err (E-error {e})) →
--       step (ξ-err {F = ref✓⟦ ℓ ⟧□} {e = e})
-- progress pc (! M) (⊢deref ⊢M) μ ⊢μ =
--   case progress pc M ⊢M μ ⊢μ of λ where
--   (step M→M′) → step (ξ {F = !□} M→M′)
--   (done v) →
--     case canonical-ref ⊢M v of λ where
--     (Ref-addr {n = n} {ℓ₁ = ℓ₁} eq _) →
--       let ⟨ wf , V₁ , v₁ , eq , ⊢V₁ ⟩ = ⊢μ n ℓ₁ eq in
--       step (deref {v = v₁} eq)
--     (Ref-proxy r (I-ref (cast (Ref (_ of l _) of l _) _ _ _) I-label I-label) _) →
--       step (deref-cast (ref-is-value r))
--   (err (E-error {e})) → step (ξ-err {F = !□} {e = e})
-- progress pc (assign L M) (⊢assign ⊢L ⊢M ℓ≼ℓ̂ pc′≼ℓ̂) μ ⊢μ =
--   step assign-static
-- progress pc (assign? L M p) (⊢assign? ⊢L ⊢M) μ ⊢μ =
--   case progress pc L ⊢L μ ⊢μ of λ where
--   (step L→L′) → step (ξ {F = assign?□ M p} L→L′)
--   (done v) →
--     case canonical-ref ⊢L v of λ where
--     (Ref-addr {n = n} {ℓ₁ = ℓ₁} eq (<:-ty () _))
--     (Ref-proxy r (I-ref (cast (Ref (T of l ℓ̂) of l ℓ) _ _ _) I-label I-label)
--       (<:-ty <:-⋆ (<:-ref (<:-ty <:-⋆ _) _))) →
--         case nsu? pc ℓ ℓ̂ of λ where
--         (yes nsu-yes) → step (assign?-ok (ref-is-value r) nsu-yes)
--         (no  nsu-no)  → step (assign?-fail (ref-is-value r) nsu-no)
--   (err (E-error {e})) → step (ξ-err {F = assign?□ M p} {e = e})
-- progress pc (assign✓ L M) (⊢assign✓ ⊢L ⊢M ℓ≼ℓ̂ pc≼ℓ̂) μ ⊢μ =
--   case progress pc L ⊢L μ ⊢μ of λ where
--   (step L→L′) → step (ξ {F = assign✓□ M} L→L′)
--   (done v) →
--     case progress pc M ⊢M μ ⊢μ of λ where
--     (step M→M′) → step (ξ {F = (assign✓ L □) v} M→M′)
--     (done w) →
--       case canonical-ref ⊢L v of λ where
--       (Ref-addr eq _) → step (β-assign w)
--       (Ref-proxy r i _) →
--         case i of λ where
--         (I-ref _ I-label I-label) → step (assign-cast (ref-is-value r) w i)
--     (err (E-error {e})) → step (ξ-err {F = (assign✓ L □) v} {e = e})
--   (err (E-error {e})) → step (ξ-err {F = assign✓□ M} {e = e})
-- progress pc (prot g ℓ M) (⊢prot ⊢M _) μ ⊢μ =
--   case progress (pc ⋎ ℓ) M ⊢M μ ⊢μ of λ where
--   (step M→N) → step (prot-ctx M→N)
--   (done v) → step (prot-val v)
--   (err E-error) → step prot-err
-- progress pc (M ⟨ c ⟩) (⊢cast ⊢M) μ ⊢μ =
--   case progress pc M ⊢M μ ⊢μ of λ where
--   (step M→M′) → step (ξ {F = □⟨ c ⟩} M→M′)
--   (done v) →
--     case active-or-inert c of λ where
--     (inj₁ a) →
--       case applycast-progress (⊢value-pc ⊢M v) v a of λ where
--       ⟨ N , M⟨c⟩↝N ⟩ → step (cast v a M⟨c⟩↝N)
--     (inj₂ i) → done (V-cast v i)
--   (err (E-error {e})) → step (ξ-err {F = □⟨ c ⟩} {e = e})
-- progress pc (blame e p) ⊢blame μ ⊢μ = err E-error
-- progress pc M (⊢sub ⊢M _) μ ⊢μ = progress pc M ⊢M μ ⊢μ
-- progress pc M (⊢sub-pc ⊢M _) μ ⊢μ = progress pc M ⊢M μ ⊢μ

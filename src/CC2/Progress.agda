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
progress {M = prot PC′ vc′ ℓ M A} vc ⊢PC (⊢prot ⊢M ⊢PC′ _ eq) ⊢μ =
  case progress vc′ ⊢PC′ ⊢M ⊢μ of λ where
  (step M→M′)  → step (prot-ctx M→M′)
  (err E-blame) → step prot-blame
  (done v)      → step (prot-val v)
progress {M = prot PC′ vc′ ℓ M A} vc ⊢PC (⊢prot ⊢M ⊢PC′ _ eq) ⊢μ =
  case progress vc′ ⊢PC′ ⊢M ⊢μ of λ where
  (step M→M′)  → step (prot-ctx M→M′)
  (err E-blame) → step prot-blame
  (done v)      → step (prot-val v)
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
        ⟨ PC′ , ↠PC′ , success vc′ ⟩ →
          case cast-sn {c = c} w ⊢M of λ where
          ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
            step (app-blame w vc 𝓋 ↠PC′ vc′ V⟨c⟩↠blame)
          ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
            step (app-cast w vc 𝓋 ↠PC′ vc′ V⟨c⟩↠V′ v′)
        ⟨ bl p , ↠blame , fail ⟩ →
          step (app-blame-pc w vc 𝓋 ↠blame)
progress {M = app! L M A B} vc ⊢PC (⊢app! ⊢L ⊢M eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = app!□ M A B} L→L′)
  (err E-blame) → step (ξ-blame {F = app!□ M A B})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where ⟨ V-ƛ , () ⟩
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-ƛ , ⊢cast {c = cast (fun d̅ c d) c̅ₙ} (⊢lam ⊢N) , ir-fun 𝓋 ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′) → step (ξ {F = app! L □ (V-cast v i) A B} M→M′)
      (err E-blame) → step (ξ-blame {F = app! L □ (V-cast v i) A B})
      (done w) →
        case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫ ⟪ d̅ ⟫)
                      (⊢cast (⊢cast (stampₑ-wt vc ⊢PC))) of λ where
        ⟨ PC′ , ↠PC′ , success vc′ ⟩ →
          case cast-sn {c = c} w ⊢M of λ where
          ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
            step (app!-blame w vc 𝓋 ⊢PC ↠PC′ vc′ V⟨c⟩↠blame)
          ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
            step (app!-cast w vc 𝓋 ⊢PC ↠PC′ vc′ V⟨c⟩↠V′ v′)
        ⟨ bl p , ↠blame , fail ⟩ →
          step (app!-blame-pc w vc 𝓋 ⊢PC ↠blame)
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
progress {M = if! L A M N} vc ⊢PC (⊢if! ⊢L ⊢M ⊢N eq) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = if!□ A M N} L→L′)
  (err E-blame) → step (ξ-blame {F = if!□ A M N})
  (done (V-raw v)) →
    case ⟨ v , ⊢L ⟩ of λ where ⟨ V-const , () ⟩  {- impossible -}
  (done (V-cast v i)) →
    case ⟨ v , ⊢L , i ⟩ of λ where
    ⟨ V-const {k =  true} , ⊢cast ⊢const , ir-base 𝓋 x ⟩ →
      case stamp⇒⋆↠LVal vc ⊢PC of λ where
      ⟨ PC′ , ↠PC′ , vc′ ⟩ →
        step (if!-true-cast vc 𝓋 ⊢PC ↠PC′ vc′)
    ⟨ V-const {k = false} , ⊢cast ⊢const , ir-base 𝓋 x ⟩ →
      case stamp⇒⋆↠LVal vc ⊢PC of λ where
      ⟨ PC′ , ↠PC′ , vc′ ⟩ →
        step (if!-false-cast vc 𝓋 ⊢PC ↠PC′ vc′)
progress {M = `let M A N} vc ⊢PC (⊢let ⊢M ⊢N) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = let□ A N} M→M′)
  (err E-blame) → step (ξ-blame {F = let□ A N})
  (done v)      → step (β-let v)
progress {M = ref⟦ ℓ ⟧ M} {μ} vc ⊢PC (⊢ref ⊢M _) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = ref⟦ ℓ ⟧□} M→M′)
  (err E-blame) → step (ξ-blame {F = ref⟦ ℓ ⟧□})
  (done v)      →
    let ⟨ n , fresh ⟩ = gen-fresh μ in
    step (ref v fresh)
progress {M = ref?⟦ ℓ ⟧ M p} {μ} vc ⊢PC (⊢ref? ⊢M) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = ref?⟦ ℓ ⟧□ p} M→M′)
  (err E-blame) → step (ξ-blame {F = ref?⟦ ℓ ⟧□ p})
  (done v)      →
    case lexpr-sn _ (⊢cast ⊢PC) of λ where
    ⟨ PC′ , ↠PC′ , success vc′ ⟩ →
      let ⟨ n , fresh ⟩ = gen-fresh μ in
      step (ref? v fresh ↠PC′ vc′)
    ⟨ bl q , ↠PC′ , fail ⟩ →
      step (ref?-blame-pc v ↠PC′)
progress {M = ! M A g} {μ} vc ⊢PC (⊢deref ⊢M x) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = !□ A g} M→M′)
  (err E-blame) → step (ξ-blame {F = !□ A g})
  (done (V-raw (V-addr {n}))) →
    case ⊢M of λ where
    (⊢addr {ℓ̂ = ℓ̂} eq) →
      let ⟨ wf , V , v , eq , ⊢V ⟩ = ⊢μ n ℓ̂ eq in
      step (deref {v = v} eq)
  (done (V-cast v i)) →
    case ⟨ v , ⊢M , i ⟩ of λ where
    ⟨ V-addr {n} , ⊢cast (⊢addr {ℓ̂ = ℓ̂} eq) , ir-ref 𝓋 ⟩ →
      let ⟨ wf , V , v , eq , ⊢V ⟩ = ⊢μ n ℓ̂ eq in
      step (deref-cast {v = v} 𝓋 eq)
progress {M = !! M A} {μ} vc ⊢PC (⊢deref! ⊢M x) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = !!□ A} M→M′)
  (err E-blame) → step (ξ-blame {F = !!□ A})
  (done (V-raw (V-addr {n}))) →
    case ⊢M of λ where ()  {- impossible -}
  (done (V-cast v i)) →
    case ⟨ v , ⊢M , i ⟩ of λ where
    ⟨ V-addr {n} , ⊢cast (⊢addr {ℓ̂ = ℓ̂} eq) , ir-ref 𝓋 ⟩ →
      let ⟨ wf , V , v , eq , ⊢V ⟩ = ⊢μ n ℓ̂ eq in
      step (deref!-cast {v = v} 𝓋 eq)
progress {M = assign L M T ℓ̂ ℓ} {μ} vc ⊢PC (⊢assign ⊢L ⊢M _ _) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = assign□ M T ℓ̂ ℓ} L→L′)
  (err E-blame) → step (ξ-blame {F = assign□ M T ℓ̂ ℓ})
  (done (V-raw (V-addr {n}))) →
    case progress vc ⊢PC ⊢M ⊢μ of λ where
    (step M→M′)  → step (ξ {F = assign _ □ (V-raw V-addr) T ℓ̂ ℓ} M→M′)
    (err E-blame) → step (ξ-blame {F = assign _ □ (V-raw V-addr) T ℓ̂ ℓ})
    (done v) → step (β-assign v)
  (done (V-cast w i)) →
    case ⟨ w , ⊢L , i ⟩ of λ where
    ⟨ V-addr {n} , ⊢cast (⊢addr eq) , ir-ref {c = c} 𝓋 ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′)  → step (ξ {F = assign _ □ (V-cast w i) T ℓ̂ ℓ} M→M′)
      (err E-blame) → step (ξ-blame {F = assign _ □ (V-cast w i) T ℓ̂ ℓ})
      (done v) →
        case cast-sn {c = c} v ⊢M of λ where
        ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
          step (assign-blame v 𝓋 V⟨c⟩↠blame)
        ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
          step (assign-cast v 𝓋 V⟨c⟩↠V′ v′)
progress {M = assign? L M T ĝ g p} {μ} vc ⊢PC (⊢assign? ⊢L ⊢M) ⊢μ =
  case progress vc ⊢PC ⊢L ⊢μ of λ where
  (step L→L′)  → step (ξ {F = assign?□ M T ĝ g p} L→L′)
  (err E-blame) → step (ξ-blame {F = assign?□ M T ĝ g p})
  (done (V-raw (V-addr {n}))) →
    case progress vc ⊢PC ⊢M ⊢μ of λ where
    (step M→M′)  → step (ξ {F = assign? _ □ (V-raw V-addr) T ĝ g p} M→M′)
    (err E-blame) → step (ξ-blame {F = assign? _ □ (V-raw V-addr) T ĝ g p})
    (done v) →
      case ⊢L of λ where
      (⊢addr {ℓ = ℓ} {ℓ̂} _) →
        case lexpr-sn (stampₑ _ vc ℓ ⟪ _ ⟫ ⟪ _ ⟫) (⊢cast (⊢cast (stampₑ-wt vc ⊢PC))) of λ where
        ⟨ PC′ , ↠PC′ , success vc′ ⟩ →
          step (β-assign? v vc ⊢PC ↠PC′ vc′)
        ⟨ bl q , ↠blame , fail ⟩ → step (assign?-blame-pc v vc ⊢PC ↠blame)
  (done (V-cast w i)) →
    case ⟨ w , ⊢L , i ⟩ of λ where
    ⟨ V-addr {n} , ⊢cast (⊢addr eq) , ir-ref {c = c} {d} {c̅ₙ} 𝓋 ⟩ →
      case progress vc ⊢PC ⊢M ⊢μ of λ where
      (step M→M′)  → step (ξ {F = assign? _ □ (V-cast w i) T ĝ g p} M→M′)
      (err E-blame) → step (ξ-blame {F = assign? _ □ (V-cast w i) T ĝ g p})
      (done v) →
        case lexpr-sn (stampₑ _ vc _ ⟪ _ ⟫ ⟪ _ ⟫) (⊢cast (⊢cast (stampₑ-wt vc ⊢PC))) of λ where
        ⟨ PC′ , ↠PC′ , success vc′ ⟩ →
          case cast-sn {c = c} v ⊢M of λ where
          ⟨ blame p , V⟨c⟩↠blame , fail ⟩ →
            step (assign?-cast-blame v vc 𝓋 ⊢PC ↠PC′ vc′ V⟨c⟩↠blame)
          ⟨ V′ , V⟨c⟩↠V′ , success v′ ⟩ →
            step (assign?-cast v vc 𝓋 ⊢PC ↠PC′ vc′ V⟨c⟩↠V′ v′)
        ⟨ bl q , ↠PC′ , fail ⟩ → step (assign?-cast-blame-pc v vc 𝓋 ⊢PC ↠PC′)
progress vc ⊢PC (⊢cast {c = c} ⊢M) ⊢μ =
  case progress vc ⊢PC ⊢M ⊢μ of λ where
  (step M→M′)  → step (ξ {F = □⟨ c ⟩} M→M′)
  (err E-blame) → step (ξ-blame {F = □⟨ c ⟩})
  (done v) →
    case cast-sn {c = c} v ⊢M of λ where
    ⟨ W , _ ∎ , success w ⟩ → done w
    ⟨ N , _ —→⟨ V⟨c⟩→L ⟩ L↠N , _ ⟩ → step (cast v V⟨c⟩→L)
progress v ⊢PC ⊢blame ⊢μ = err E-blame

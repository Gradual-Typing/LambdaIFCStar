module CC2.CastReduction where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import CC2.Statics


infix 2 _—→_

data _—→_ : Term → Term → Set where

  cast : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂}
    → RawValue Vᵣ
    → c̅ —→⁺ c̅ₙ
    → CVal c̅ₙ
      ----------------------------------------------------------- Cast
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ —→ Vᵣ ⟨ cast cᵣ c̅ₙ ⟩

  cast-blame : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ : CExpr g₁ ⇒ g₂} {p}
    → RawValue Vᵣ
    → c̅ —↠ₗ ⊥ g₁ g₂ p
      ----------------------------------------------------------- CastBlame
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ —→ blame p

  cast-id : ∀ {ι g} {k : rep ι}
      ----------------------------------------------------------- CastId
    → $ k ⟨ cast (id ι) (id g) ⟩ —→ $ k

  cast-comp : ∀ {Vᵣ A B C} {cᵢ : Cast A ⇒ B} {d : Cast B ⇒ C}
    → RawValue Vᵣ
    → Irreducible cᵢ
      ----------------------------------------------------------- CastComposition
    → Vᵣ ⟨ cᵢ ⟩ ⟨ d ⟩ —→ Vᵣ ⟨ cᵢ ⨟ d ⟩

open import Common.MultiStep ⊤ (λ {tt tt → Term}) _—→_ public

cast-sn : ∀ {Σ A B V} {c : Cast A ⇒ B}
  → Value V
  → [] ; Σ ; l low ; low ⊢ V ⇐ A
    ----------------------------------------
  → ∃[ M ] (V ⟨ c ⟩ —↠ M) × Result M
cast-sn {V = addr n} {c = cast (ref c d) c̅} (V-raw V-addr) (⊢addr eq)
  with cexpr-sn c̅
... | ⟨ c̅ₙ , c̅ₙ ∎ₗ , success 𝓋 ⟩ =
  ⟨ addr n ⟨ cast (ref c d) c̅ₙ ⟩ , _ ∎ ,
    success (V-cast V-addr (ir-ref 𝓋)) ⟩
... | ⟨ c̅ₙ , c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success 𝓋 ⟩ =
  ⟨ addr n ⟨ cast (ref c d) c̅ₙ ⟩ ,
    _ —→⟨ cast V-addr (c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) 𝓋 ⟩ _ ∎ ,
    success (V-cast V-addr (ir-ref 𝓋)) ⟩
... | ⟨ ⊥ _ _ p , c̅↠⊥ , fail ⟩ =
  ⟨ blame p , _ —→⟨ cast-blame V-addr c̅↠⊥ ⟩ _ ∎ , fail ⟩
cast-sn {V = ƛ N} {c = cast (fun d̅ c d) c̅} (V-raw V-ƛ) (⊢lam ⊢N)
  with cexpr-sn c̅
... | ⟨ c̅ₙ , _ ∎ₗ , success 𝓋 ⟩ =
  ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩ , _ ∎ ,
    success (V-cast V-ƛ (ir-fun 𝓋)) ⟩
... | ⟨ c̅ₙ ,  c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success 𝓋 ⟩ =
  ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩ ,
    _ —→⟨ cast V-ƛ (c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) 𝓋 ⟩ _ ∎ ,
    success (V-cast V-ƛ (ir-fun 𝓋)) ⟩
... | ⟨ ⊥ _ _ p , c̅↠⊥ , fail ⟩ =
  ⟨ blame p , _ —→⟨ cast-blame V-ƛ c̅↠⊥ ⟩ _ ∎ , fail ⟩
cast-sn {V = $ k} {c = cast (id ι) c̅} (V-raw V-const) ⊢const
  with cexpr-sn c̅
... | ⟨ c̅ₙ , c̅ ∎ₗ , success id ⟩ =
  ⟨ $ k , _ —→⟨ cast-id ⟩ _ ∎ ,
    success (V-raw V-const) ⟩
... | ⟨ c̅ₙ , c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success id ⟩ =
  ⟨ $ k , _ —→⟨ cast V-const (c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) id ⟩ _ —→⟨ cast-id ⟩ _ ∎ ,
    success (V-raw V-const) ⟩
... | ⟨ c̅ₙ , _ ∎ₗ , success (inj 𝓋) ⟩ =
  ⟨ $ k ⟨ cast (id ι) c̅ₙ ⟩ , _ ∎ ,
    success (V-cast V-const (ir-base (inj 𝓋) (λ ()))) ⟩
... | ⟨ c̅ₙ , c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success (inj 𝓋) ⟩ =
  ⟨ $ k ⟨ cast (id ι) c̅ₙ ⟩ ,
    _ —→⟨ cast V-const (c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) (inj 𝓋) ⟩ _ ∎ ,
    success (V-cast V-const (ir-base (inj 𝓋) (λ ()))) ⟩
... | ⟨ c̅ₙ , _ ∎ₗ , success (up id) ⟩ =
  ⟨ $ k ⟨ cast (id ι) c̅ₙ ⟩ , _ ∎ ,
    success (V-cast V-const (ir-base (up id) (λ ()))) ⟩
... | ⟨ c̅ₙ , c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success (up id) ⟩ =
  ⟨ $ k ⟨ cast (id ι) c̅ₙ ⟩ ,
    _ —→⟨ cast V-const (c̅ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) (up id) ⟩ _ ∎ ,
    success (V-cast V-const (ir-base (up id) (λ ()))) ⟩
... | ⟨ ⊥ _ _ p , c̅↠⊥ , fail ⟩ =
  ⟨ blame p , _ —→⟨ cast-blame V-const c̅↠⊥ ⟩ _ ∎ , fail ⟩
cast-sn {c = c} (V-cast {c = cᵢ} v i) (⊢cast ⊢Vᵣ)
  with cast-sn {c = cᵢ ⨟ c} (V-raw v) ⊢Vᵣ
... | ⟨ M , Vᵣ⟨cᵢ⨟c⟩↠M , r ⟩ = ⟨ M , _ —→⟨ cast-comp v i ⟩ Vᵣ⟨cᵢ⨟c⟩↠M , r ⟩

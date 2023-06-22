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
    → c̅ —↠ₗ c̅ₙ
    → CVal c̅ₙ
      ----------------------------------------------------------- Cast
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ —→ Vᵣ ⟨ cast cᵣ c̅ₙ ⟩

  cast-blame : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂} {p}
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

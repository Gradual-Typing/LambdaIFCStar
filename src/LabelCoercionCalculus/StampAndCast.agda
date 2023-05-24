module LabelCoercionCalculus.StampAndCast where

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
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.Precision
open import LabelCoercionCalculus.SyntacComp
open import LabelCoercionCalculus.Stamping


stamp-and-cast : ∀ {ℓ₁ g₁ g₂} (c̅ₙ : CoercionExp l ℓ₁ ⇒ g₁)
  → 𝒱 c̅ₙ
  → (ℓ₂ : StaticLabel)
  → g₁ ⋎̃ l ℓ₂ ≾ g₂
  → NotProj (g₁ ⋎̃ l ℓ₂) g₂
  → CoercionExp l ℓ₁ ⇒ g₂
stamp-and-cast {ℓ₁} {g₁} {g₂} c̅ₙ v ℓ₂ lp np =
  stamp c̅ₙ v ℓ₂ ⨾ coerce-nproj (g₁ ⋎̃ l ℓ₂) g₂ lp np

stamp-cast-prec : ∀ {ℓ₁ ℓ₁′ g₁ g₁′ g₂ g₂′}
     (c̅ₙ : CoercionExp l ℓ₁ ⇒ g₁) (c̅ₙ′ : CoercionExp l ℓ₁′ ⇒ g₁′)
  → (v : 𝒱 c̅ₙ) → (v′ : 𝒱 c̅ₙ′)
  → (ℓ₂ ℓ₂′ : StaticLabel)
  → (c~ : g₁ ⋎̃ l ℓ₂ ≾ g₂) → (c~′ : g₁′ ⋎̃ l ℓ₂′ ≾ g₂′)
  → (np : NotProj (g₁ ⋎̃ l ℓ₂) g₂) → (np′ : NotProj (g₁′ ⋎̃ l ℓ₂′) g₂′)
  → ⊢ c̅ₙ ⊑ c̅ₙ′
  → g₂ ⊑ₗ g₂′
  → ℓ₂ ≼ ℓ₂′
  → ⊢ stamp-and-cast c̅ₙ v ℓ₂ c~ np ⊑ stamp-and-cast c̅ₙ′ v′ ℓ₂′ c~′ np′
stamp-cast-prec {g₁ = g₁} {g₁′} c̅ₙ c̅ₙ′ v v′ .low .low c~ c~′ np np′ prec g⊑g′ l≼l
  rewrite g⋎̃low≡g {g₁} | g⋎̃low≡g {g₁′} = ⊑-cast prec (proj₂ (prec→⊑ _ _ prec)) g⊑g′
stamp-cast-prec c̅ₙ c̅ₙ′ v v′ .high .high c~ c~′ np np′ prec g⊑g′ h≼h = {!!}

stamp-cast-prec (id (l ℓ₁)) (id _) id id .low .high c~ c~′ np np′ (⊑-id l⊑l) ⋆⊑ l≼h
  with ℓ₁
... | low  = ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑
... | high = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp-cast-prec (id (l ℓ₁)) (id _) id id .low .high c~ c~′ np np′ (⊑-id l⊑l) l⊑l l≼h
  with ℓ₁ | c~ | c~′
... | low  | ≾-l l≼h | ≾-l h≼h = ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l l⊑l
... | high | ≾-l h≼h | ≾-l h≼h = ⊑-cast (⊑-id l⊑l) l⊑l l⊑l
stamp-cast-prec (id .(l _)) (_ ⨾ _ !) id (inj id) .low .high c~ c~′ np np′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec (id .(l _)) (_ ⨾ (_ !)) id (inj (up id)) .low .high c~ c~′ np np′ (⊑-castr (⊑-castr (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec (id (l _)) (_ ⨾ ↑) id (up v′) .low .high c~ c~′ np np′ prec g⊑g′ l≼h = {!!}
stamp-cast-prec (_ ⨾ (_ !)) c̅ₙ′ (inj v) v′ .low .high c~ c~′ np np′ prec g⊑g′ l≼h = {!!}
stamp-cast-prec (_ ⨾ ↑) c̅ₙ′ (up v) v′ .low .high c~ c~′ np np′ prec g⊑g′ l≼h = {!!}

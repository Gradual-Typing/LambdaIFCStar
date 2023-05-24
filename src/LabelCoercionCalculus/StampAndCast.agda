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

stamp-cast-prec : ∀ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ g₁ g₁′ g₂ g₂′}
     {np : NotProj (g₁ ⋎̃ l ℓ₂) g₂} {np′ : NotProj (g₁′ ⋎̃ l ℓ₂′) g₂′}
     {c̅ₙ : CoercionExp l ℓ₁ ⇒ g₁} {c̅ₙ′ : CoercionExp l ℓ₁′ ⇒ g₁′}
  → (v : 𝒱 c̅ₙ) → (v′ : 𝒱 c̅ₙ′)
  → (c~ : g₁ ⋎̃ l ℓ₂ ≾ g₂) → (c~′ : g₁′ ⋎̃ l ℓ₂′ ≾ g₂′)
  → ⊢ c̅ₙ ⊑ c̅ₙ′
  → g₂ ⊑ₗ g₂′
  → ℓ₂ ≼ ℓ₂′
    ------------------------------------------------------------------------
  → ⊢ stamp-and-cast c̅ₙ v ℓ₂ c~ np ⊑ stamp-and-cast c̅ₙ′ v′ ℓ₂′ c~′ np′
{- stamping low on both sides -}
stamp-cast-prec {g₁ = g₁} {g₁′} v v′ c~ c~′ prec g⊑g′ l≼l
  rewrite g⋎̃low≡g {g₁} | g⋎̃low≡g {g₁′} = ⊑-cast prec (proj₂ (prec→⊑ _ _ prec)) g⊑g′
{- stamping high on both sides -}
stamp-cast-prec v v′ c~ c~′ prec g⊑g′ h≼h = {!!}
{- stamping low on less precise and high on more precise side -}
stamp-cast-prec {ℓ} id id c~ c~′ (⊑-id l⊑l) ⋆⊑ l≼h with ℓ
... | low  = ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑
... | high = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp-cast-prec {ℓ} id id c~ c~′ (⊑-id l⊑l) l⊑l l≼h
  with ℓ | c~ | c~′
... | low  | ≾-l l≼h | ≾-l h≼h =
  ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l l⊑l
... | high | ≾-l h≼h | ≾-l h≼h =
  ⊑-cast (⊑-id l⊑l) l⊑l l⊑l
stamp-cast-prec id (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec id (inj (up id)) c~ c~′
                (⊑-castr (⊑-castr (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec id (up id) c~ c~′
                (⊑-castr (⊑-id l⊑l) x ()) g⊑g′ l≼h
stamp-cast-prec {ℓ} (inj id) id c~ c~′
                (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h with ℓ
... | low  = ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
... | high = ⊑-cast (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {ℓ} (inj id) (inj id) c~ c~′
                (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h with ℓ
... | low  = ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
... | high = ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {ℓ} (inj id) (inj id) c~ c~′
                (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h with ℓ
... | low  = ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
... | high = ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-cast (⊑-castr (⊑-id ()) x x₁) l⊑l _) g⊑g′ l≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castl (⊑-castr _ l⊑l ()) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
    (⊑-castr (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′
                (⊑-castl (⊑-castr _ () _) l⊑l ⋆⊑) g⊑g′ l≼h
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-castr (⊑-castl _ l⊑l x₃) x x₁) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) id c~ c~′
                (⊑-castl (⊑-castl (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj id) c~ c~′
                (⊑-cast (⊑-castl (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj id) c~ c~′
                (⊑-castr (⊑-castl (⊑-castl (⊑-id l⊑l) _ ()) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-cast (⊑-cast _ l⊑l l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castr (⊑-castl _ () _) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (up id) c~ c~′ (⊑-castl _ _ _) g⊑g′ l≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (up id) c~ c~′ (⊑-castr _ _ _) g⊑g′ l≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (up id) id c~ c~′ (⊑-castl (⊑-id l⊑l) _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-cast (⊑-id _) _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castl _ () _) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-cast _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-castl _ () _) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (up id) c~ c~′ prec g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l g⊑g′

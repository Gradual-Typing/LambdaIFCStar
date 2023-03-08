module Common.SubtypeCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types


infix 6 _↟_

data _↟_ : Type → Type → Set where
  cast↟ : ∀ A B → A <: B → A ↟ B

branch/s : ∀ {g₁ g₂} A (s : ` Bool of g₁ ↟ ` Bool of g₂)
  → (stamp A g₁) ↟ (stamp A g₂)
branch/s {g₁} {g₂} A (cast↟ .(` Bool of g₁) .(` Bool of g₂) (<:-ty g₁<:g₂ <:-ι)) =
  cast↟ (stamp A g₁) (stamp A g₂) (stamp-<: <:-refl g₁<:g₂)

dom/s : ∀ {A B C D gc₁ gc₂ g₁ g₂}
  → ⟦ gc₁ ⟧ A ⇒ B of g₁ ↟ ⟦ gc₂ ⟧ C ⇒ D of g₂
  → C ↟ A
dom/s (cast↟ (⟦ _ ⟧ A ⇒ B of _) (⟦ _ ⟧ C ⇒ D of _) (<:-ty _ (<:-fun _ C<:A _))) =
  cast↟ C A C<:A

cod/s : ∀ {A B C D gc₁ gc₂ g₁ g₂}
  → ⟦ gc₁ ⟧ A ⇒ B of g₁ ↟ ⟦ gc₂ ⟧ C ⇒ D of g₂
  → stamp B g₁ ↟ stamp D g₂
cod/s (cast↟ (⟦ gc₁ ⟧ A ⇒ B of g₁) (⟦ gc₂ ⟧ C ⇒ D of g₂) (<:-ty g₁<:g₂ (<:-fun _ C<:A B<:D))) =
  cast↟ (stamp B g₁) (stamp D g₂) (stamp-<: B<:D g₁<:g₂)

trans/s : ∀ {A B C} → A ↟ B → B ↟ C → A ↟ C
trans/s (cast↟ A B A<:B) (cast↟ B C B<:C) = cast↟ A C (<:-trans A<:B B<:C)

module TypeBasedCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Types
open import BlameLabels

infix 6 Cast_⇒_

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ A B → BlameLabel → A ~ B → Cast A ⇒ B

{- Let's first consider the label parts of A ⇒ B,
   where we have four cases:
   1) ℓ ⇒ ℓ    2) ℓ ⇒ ⋆    3) ⋆ ⇒ ℓ    4) ⋆ ⇒ ⋆  -}

-- g₁ ⇒ g₂ is inert if g₁ ≢ ⋆
data Inert_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  I-label : ∀ {ℓ g₂} → Inert l ℓ ⇒ g₂

-- ⋆ ⇒ g₂ is active
data Active_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  A-id⋆ : Active ⋆ ⇒ ⋆
  A-proj : ∀ {ℓ} → Active ⋆ ⇒ l ℓ

-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-base-inj : ∀ {ι ℓ}
    → (c : Cast ` ι of l ℓ ⇒ ` ι of ⋆)
      ------------------------------------- InertBaseInj
    → Inert c

  I-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast [ gc₁ ] A ⇒ B of g₁ ⇒ [ gc₂ ] C ⇒ D of g₂)
    → Inert gc₁ ⇒ gc₂ → Inert g₁ ⇒ g₂
      ------------------------------------- InertFun
    → Inert c

  I-ref : ∀ {S T g₁ g₁₁ g₂ g₂₁}
    → (c : Cast Ref (S of g₁₁) of g₁ ⇒ Ref (T of g₂₁) of g₂)
    → Inert g₁₁ ⇒ g₂₁ → Inert g₁ ⇒ g₂
      ------------------------------------- InertRef
    → Inert c

data Active : ∀ {A B} → Cast A ⇒ B → Set where
  A-base-id : ∀ {ι g}
    → (c : Cast ` ι of g ⇒ ` ι of g)
      ------------------------------------- ActiveBaseId
    → Active c

  A-base-proj : ∀ {ι ℓ}
    → (c : Cast ` ι of ⋆ ⇒ ` ι of l ℓ)
      ------------------------------------- ActiveBaseProj
    → Active c

  A-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast [ gc₁ ] A ⇒ B of g₁ ⇒ [ gc₂ ] C ⇒ D of g₂)
    → Active g₁ ⇒ g₂
      ------------------------------------- ActiveFun
    → Active c

  A-fun-pc : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast [ gc₁ ] A ⇒ B of g₁ ⇒ [ gc₂ ] C ⇒ D of g₂)
    → Active gc₁ ⇒ gc₂ → Inert g₁ ⇒ g₂
      ------------------------------------- ActiveFunPC
    → Active c

  A-ref : ∀ {A B g₁ g₂}
    → (c : Cast Ref A of g₁ ⇒ Ref B of g₂)
    → Active g₁ ⇒ g₂
      ------------------------------------- ActiveRef
    → Active c

  A-ref-ref : ∀ {S T g₁ g₁₁ g₂ g₂₁}
    → (c : Cast Ref (S of g₁₁) of g₁ ⇒ Ref (T of g₂₁) of g₂)
    → Active g₁₁ ⇒ g₂₁ → Inert g₁ ⇒ g₂
      ------------------------------------- ActiveRefLab
    → Active c

active-⋆ : ∀ {g} → Active ⋆ ⇒ g
active-⋆ {⋆} = A-id⋆
active-⋆ {l ℓ} = A-proj

active-or-inert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
{- Base -}
active-or-inert (cast (` ι of ⋆) (` ι of ⋆) p (~-ty _ ~-ι)) = inj₁ (A-base-id _)
active-or-inert (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty _ ~-ι)) = inj₁ (A-base-proj _)
active-or-inert (cast (` ι of l ℓ) (` ι of ⋆) p (~-ty _ ~-ι)) = inj₂ (I-base-inj _)
active-or-inert (cast (` ι of l ℓ) (` ι of l ℓ) p (~-ty l~ ~-ι)) = inj₁ (A-base-id _)
{- Ref -}
active-or-inert (cast (Ref A of ⋆) (Ref B of g) p (~-ty _ (~-ref _))) =
  inj₁ (A-ref _ active-⋆)
active-or-inert (cast (Ref (S of ⋆) of l ℓ₁) (Ref (T of g₂₁) of g₂) p (~-ty _ (~-ref _))) =
  inj₁ (A-ref-ref _ active-⋆ I-label)
active-or-inert (cast (Ref (S of l _) of l ℓ₁) (Ref (T of g₂₁) of g₂) p (~-ty _ (~-ref _))) =
  inj₂ (I-ref _ I-label I-label)
{- Fun -}
active-or-inert (cast ([ _ ] A ⇒ B of ⋆) ([ _ ] C ⇒ D of g) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun _ active-⋆)
active-or-inert (cast ([ ⋆ ] A ⇒ B of l ℓ) ([ gc ] C ⇒ D of _) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun-pc _ active-⋆ I-label)
active-or-inert (cast ([ l pc ] A ⇒ B of l _) C→D p (~-ty _ (~-fun _ _ _))) =
  inj₂ (I-fun _ I-label I-label)


dom/c : ∀ {A B C D gc₁ gc₂ g₁ g₂}
  → Cast [ gc₁ ] A ⇒ B of g₁ ⇒ [ gc₂ ] C ⇒ D of g₂
  → Cast C ⇒ A
dom/c (cast ([ gc₁ ] A ⇒ B of g₁) ([ gc₂ ] C ⇒ D of g₂) p (~-ty _ (~-fun _ A~C B~D))) =
  cast C A p (~-sym A~C)

cod/c : ∀ {A B C D gc₁ gc₂ g₁ g₂}
  → Cast [ gc₁ ] A ⇒ B of g₁ ⇒ [ gc₂ ] C ⇒ D of g₂
  → Cast stamp B g₁ ⇒ stamp D g₂
cod/c (cast ([ gc₁ ] A ⇒ B of g₁) ([ gc₂ ] C ⇒ D of g₂) p (~-ty g₁~g₂ (~-fun _ A~C B~D))) =
  cast (stamp B g₁) (stamp D g₂) p (stamp-~ B~D g₁~g₂)

in/c : ∀ {A B g₁ g₂}
  → Cast Ref A of g₁ ⇒ Ref B of g₂
  → Cast B ⇒ A
in/c (cast (Ref A of g₁) (Ref B of g₂) p (~-ty _ (~-ref A~B))) =
  cast B A p (~-sym A~B)

out/c : ∀ {A B g₁ g₂}
  → Cast Ref A of g₁ ⇒ Ref B of g₂
  → Cast stamp A g₁ ⇒ stamp B g₂
out/c (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ (~-ref A~B))) =
  cast (stamp A g₁) (stamp B g₂) p (stamp-~ A~B g₁~g₂)

branch/c : ∀ {g} A ℓ
  → Cast ` Bool of g ⇒ ` Bool of ⋆
  → Cast stamp A (l ℓ) ⇒ stamp A ⋆
branch/c A ℓ (cast _ _ p _) =
  cast (stamp A (l ℓ)) (stamp A ⋆) p (stamp-~ ~-refl ~⋆)

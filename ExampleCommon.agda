module ExampleCommon where

open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)

open import Types
open import SurfaceLang

-- publish : 𝔹 of low → ⊤
publish : Term
publish = ƛ⟦ low ⟧ ` Bool of l low ˙ $ tt of low of low

⊢publish : ∀ {Γ}
  → Γ ; l low ⊢ᴳ publish ⦂ ⟦ l low ⟧ (` Bool of l low) ⇒ (` Unit of l low) of l low
⊢publish = ⊢lam ⊢const

-- user-input : ⊤ → 𝔹 of high
user-input : Term
user-input = ƛ⟦ low ⟧ ` Unit of l low ˙ $ true of high {- let's hard-code this for now -} of low

⊢user-input : ∀ {Γ}
  → Γ ; l low ⊢ᴳ user-input ⦂ ⟦ l low ⟧ (` Unit of l low) ⇒ (` Bool of l high) of l low
⊢user-input = ⊢lam ⊢const

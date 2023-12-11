{- Algorithmic typing rules of the surface language -}
module Surface2.Typing where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Common.Utils
open import Common.Types
open import Surface2.Syntax

infix 4 _;_⊢ᴳ_⦂_

data _;_⊢ᴳ_⦂_ : Context → Label → Term → Type → Set where

  ⊢const : ∀ {Γ gc ι} {k : rep ι} {ℓ}
      ------------------------------------ Const
    → Γ ; gc ⊢ᴳ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢var : ∀ {Γ gc A x}
    → Γ ∋ x ⦂ A
      --------------------- Var
    → Γ ; gc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {Γ gc g A B N ℓ}
    → (A ∷ Γ) ; g ⊢ᴳ N ⦂ B
      --------------------------------------------------------- Lam
    → Γ ; gc ⊢ᴳ ƛ g , A ˙ N of ℓ ⦂ ⟦ g ⟧ A ⇒ B of l ℓ

  ⊢app : ∀ {Γ gc gc′ A A′ B L M g p}
    → Γ ; gc ⊢ᴳ L ⦂ ⟦ gc′ ⟧ A ⇒ B of g
    → Γ ; gc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ gc′
    → gc ≾ gc′
      ------------------------------------- App
    → Γ ; gc ⊢ᴳ L · M at p ⦂ stamp B g

  ⊢if : ∀ {Γ gc A B C L M N g p}
    → Γ ; gc     ⊢ᴳ L ⦂ ` Bool of g
    → Γ ; gc ⋎̃ g ⊢ᴳ M ⦂ A
    → Γ ; gc ⋎̃ g ⊢ᴳ N ⦂ B
    → A ∨̃ B ≡ just C
      ------------------------------------------------- If
    → Γ ; gc ⊢ᴳ if L then M else N at p ⦂ stamp C g

  ⊢ann : ∀ {Γ gc M A A′ p}
    → Γ ; gc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
      ---------------------------- Ann
    → Γ ; gc ⊢ᴳ M ∶ A at p ⦂ A

  ⊢let : ∀ {Γ gc A B M N}
    → Γ     ; gc ⊢ᴳ M ⦂ A
    → A ∷ Γ ; gc ⊢ᴳ N ⦂ B
      ------------------------------- Let
    → Γ ; gc ⊢ᴳ `let M `in N ⦂ B

  ⊢ref : ∀ {Γ gc M T g ℓ p}
    → Γ ; gc ⊢ᴳ M ⦂ T of g
    → T of g ≲ T of l ℓ
    → gc ≾ l ℓ
      --------------------------------------------------------- Ref
    → Γ ; gc ⊢ᴳ ref⟦ ℓ ⟧ M at p ⦂ Ref (T of l ℓ) of l low

  ⊢deref : ∀ {Γ gc M A g p}
    → Γ ; gc ⊢ᴳ M ⦂ (Ref A) of g
      -------------------------------- Deref
    → Γ ; gc ⊢ᴳ ! M at p ⦂ stamp A g

  ⊢assign : ∀ {Γ gc L M A T g ĝ p}
    → Γ ; gc ⊢ᴳ L ⦂ Ref (T of ĝ) of g
    → Γ ; gc ⊢ᴳ M ⦂ A
    → A ≲ T of ĝ
    → g ≾ ĝ
    → gc ≾ ĝ
      --------------------------------------------- Assign
    → Γ ; gc ⊢ᴳ L := M at p ⦂ ` Unit of l low

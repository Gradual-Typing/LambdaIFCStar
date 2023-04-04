{- Algorithmic typing rules of the surface language -}
module Surface2.Typing where

open import Data.Maybe
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Common.Utils
open import Common.Types
open import Surface.SurfaceSyntax


infix 4 _;_⊢ᴳ_⦂_;_

data _;_⊢ᴳ_⦂_;_ : Ctxt → Label → Term → (A : Type) → ⊢ A → Set where

  ⊢const : ∀ {Γ gc ι} {k : rep ι} {ℓ}
      ------------------------------------------------ Const
    → Γ ; gc ⊢ᴳ $ k of ℓ ⦂ ` ι of l ℓ ; ⊢ι ι (l ℓ)

  ⊢var : ∀ {Γ gc A x ⊢A}
    → Γ ∋ x ⦂ ⟨ A , ⊢A ⟩
      -------------------------- Var
    → Γ ; gc ⊢ᴳ ` x ⦂ A ; ⊢A

  ⊢lam : ∀ {Γ gc A B N ℓᶜ ℓ ⊢B}
    → (⊢A : ⊢ A)
    → ⟨ A , ⊢A ⟩ ∷ Γ ; l ℓᶜ ⊢ᴳ N ⦂ B ; ⊢B
    → (ℓ≼ℓᶜ : ℓ ≼ ℓᶜ)
      -------------------------------------------------------------------------------- Lam
    → Γ ; gc ⊢ᴳ ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ ⦂ ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ; ⊢fun ⊢A ⊢B (≾-l ℓ≼ℓᶜ)

  ⊢app : ∀ {Γ gc A A′ B L M gᶜ g p} {⊢A ⊢A′ ⊢B} {g≾gᶜ : g ≾ gᶜ}
    → Γ ; gc ⊢ᴳ L ⦂ ⟦ gᶜ ⟧ A ⇒ B of g ; ⊢fun ⊢A ⊢B g≾gᶜ
    → Γ ; gc ⊢ᴳ M ⦂ A′ ; ⊢A′
    → A′ ≲ A
    → gc ≾ gᶜ
    → (⊢B′ : ⊢ stamp B g)
      ------------------------------------------ App
    → Γ ; gc ⊢ᴳ L · M at p ⦂ stamp B g ; ⊢B′

  ⊢if : ∀ {Γ gc A B C L M N g p} {⊢A ⊢B}
    → Γ ; gc     ⊢ᴳ L ⦂ ` Bool of g ; ⊢ι Bool g
    → Γ ; gc ⋎̃ g ⊢ᴳ M ⦂ A ; ⊢A
    → Γ ; gc ⋎̃ g ⊢ᴳ N ⦂ B ; ⊢B
    → A ∨̃ B ≡ just C
    → (⊢C′ : ⊢ stamp C g)
      ------------------------------------------------------- If
    → Γ ; gc ⊢ᴳ if L then M else N at p ⦂ stamp C g ; ⊢C′

  ⊢ann : ∀ {Γ gc M A A′ p} {⊢A′}
    → (⊢A : ⊢ A)
    → Γ ; gc ⊢ᴳ M ⦂ A′ ; ⊢A′
    → A′ ≲ A
      ----------------------------------- Ann
    → Γ ; gc ⊢ᴳ M ∶ A at p ⦂ A ; ⊢A

  ⊢let : ∀ {Γ gc A B M N} {⊢A ⊢B}
    → Γ              ; gc ⊢ᴳ M ⦂ A ; ⊢A
    → ⟨ A , ⊢A ⟩ ∷ Γ ; gc ⊢ᴳ N ⦂ B ; ⊢B
      ----------------------------------- Let
    → Γ ; gc ⊢ᴳ `let M `in N ⦂ B ; ⊢B

  ⊢ref : ∀ {Γ gc M T g ℓ p} {⊢Tg : ⊢ T of g}
    → Γ ; gc ⊢ᴳ M ⦂ T of g ; ⊢Tg
    → T of g ≲ T of l ℓ
    → gc ≾ l ℓ
    → (⊢Tℓ : ⊢ T of l ℓ)
      ------------------------------------------------------------------------------------- Ref
    → Γ ; gc ⊢ᴳ ref⟦ ℓ ⟧ M at p ⦂ Ref (T of l ℓ) of l low ; ⊢ref ⊢Tℓ (≾-l (low≼ _))

  ⊢deref : ∀ {Γ gc M T ĝ g} {⊢Tg : ⊢ T of ĝ} {g≾ĝ}
    → Γ ; gc ⊢ᴳ M ⦂ Ref (T of ĝ) of g ; ⊢ref ⊢Tg g≾ĝ
    → (⊢A : ⊢ stamp (T of ĝ) g)
      -------------------------------------------- Deref
    → Γ ; gc ⊢ᴳ ! M ⦂ stamp (T of ĝ) g ; ⊢A

  ⊢assign : ∀ {Γ gc L M A T g ĝ p} {⊢Tg : ⊢ T of ĝ} {⊢A} {g≾ĝ}
    → Γ ; gc ⊢ᴳ L ⦂ Ref (T of ĝ) of g ; ⊢ref ⊢Tg g≾ĝ
    → Γ ; gc ⊢ᴳ M ⦂ A ; ⊢A
    → A ≲ T of ĝ
    → gc ≾ ĝ
      ----------------------------------------------------------------- Assign
    → Γ ; gc ⊢ᴳ L := M at p ⦂ ` Unit of l low ; ⊢ι Unit (l low)

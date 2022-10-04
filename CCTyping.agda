{- Typing rules of the cast calculus -}

open import Types

module CCTyping (Cast_⇒_ : Type → Type → Set) where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import HeapContext
open import CCSyntax Cast_⇒_

infix 4 _;_;_;_⊢_⦂_

data _;_;_;_⊢_⦂_ : Context → HeapContext → Label → StaticLabel → Term → Type → Set where

  ⊢const : ∀ {Γ Σ gc pc ι} {k : rep ι} {ℓ}
      -------------------------------------------- CCConst
    → Γ ; Σ ; gc ; pc ⊢ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢addr : ∀ {Γ Σ gc pc n T ℓ ℓ₁}
    → lookup-Σ Σ (a[ ℓ₁ ] n) ≡ just T
      ------------------------------------------------ CCAddr
    → Γ ; Σ ; gc ; pc ⊢ addr (a[ ℓ₁ ] n) of ℓ ⦂ Ref (T of l ℓ₁) of l ℓ

  ⊢var : ∀ {Γ Σ gc pc A x}
    → Γ ∋ x ⦂ A
      ----------------------------- CCVar
    → Γ ; Σ ; gc ; pc ⊢ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ gc pc pc′ A B N ℓ}
    → (∀ {pc} → A ∷ Γ ; Σ ; l pc′ ; pc ⊢ N ⦂ B)
      ------------------------------------------------------------------- CCLam
    → Γ ; Σ ; gc ; pc ⊢ ƛ[ pc′ ] A ˙ N of ℓ ⦂ [ l pc′ ] A ⇒ B of l ℓ

  ⊢app : ∀ {Γ Σ gc pc A B L M g}
    → Γ ; Σ ; gc ; pc ⊢ L ⦂ ([ gc ⋎̃ g ] A ⇒ B) of g
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
      --------------------------------------- CCApp
    → Γ ; Σ ; gc ; pc ⊢ L · M ⦂ stamp B g

  ⊢if : ∀ {Γ Σ gc pc A L M N g}
    → Γ ; Σ ; gc     ; pc ⊢ L ⦂ ` Bool of g
    → (∀ {pc} → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ M ⦂ A)
    → (∀ {pc} → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ N ⦂ A)
      --------------------------------------------------------- CCIf
    → Γ ; Σ ; gc ; pc ⊢ if L A M N ⦂ stamp A g

  ⊢let : ∀ {Γ Σ gc pc M N A B}
    → Γ       ; Σ ; gc ; pc ⊢ M ⦂ A
    → (∀ {pc} → A ∷ Γ ; Σ ; gc ; pc ⊢ N ⦂ B)
      ----------------------------------- CCLet
    → Γ ; Σ ; gc ; pc ⊢ `let M N ⦂ B

  ⊢ref : ∀ {Γ Σ pc pc′ M T ℓ}
    → Γ ; Σ ; l pc′ ; pc ⊢ M ⦂ T of l ℓ
    → pc′ ≼ ℓ
      ---------------------------------------------------------- CCRefStatic
    → Γ ; Σ ; l pc′ ; pc ⊢ ref[ ℓ ] M ⦂ Ref (T of l ℓ) of l low

  ⊢ref? : ∀ {Γ Σ gc pc M T ℓ}
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ T of l ℓ
      ---------------------------------------------------------- CCRefUnchecked
    → Γ ; Σ ; gc ; pc ⊢ ref?[ ℓ ] M ⦂ Ref (T of l ℓ) of l low

  ⊢ref✓ : ∀ {Γ Σ gc pc M T ℓ}
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ T of l ℓ
    → pc ≼ ℓ
      ---------------------------------------------------------- CCRefChecked
    → Γ ; Σ ; gc ; pc ⊢ ref✓[ ℓ ] M ⦂ Ref (T of l ℓ) of l low

  ⊢deref : ∀ {Γ Σ gc pc M A g}
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ Ref A of g
      ------------------------------------- CCDeref
    → Γ ; Σ ; gc ; pc ⊢ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ pc pc′ L M T ℓ}
    → Γ ; Σ ; l pc′ ; pc ⊢ L ⦂ Ref (T of l ℓ) of l ℓ
    → Γ ; Σ ; l pc′ ; pc ⊢ M ⦂ T of l ℓ
    → pc′ ≼ ℓ
      --------------------------------------------- CCAssignStatic
    → Γ ; Σ ; l pc′ ; pc ⊢ L := M ⦂ ` Unit of l low

  ⊢assign? : ∀ {Γ Σ gc pc L M T g}
    → Γ ; Σ ; gc ; pc ⊢ L ⦂ Ref (T of g) of g
    → (∀ {pc} → Γ ; Σ ; gc ; pc ⊢ M ⦂ T of g)
      --------------------------------------------- CCAssignUnchecked
    → Γ ; Σ ; gc ; pc ⊢ L :=? M ⦂ ` Unit of l low

  ⊢assign✓ : ∀ {Γ Σ gc pc L M T ℓ}
    → Γ ; Σ ; gc ; pc ⊢ L ⦂ Ref (T of l ℓ) of l ℓ
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ T of l ℓ
    → pc ≼ ℓ
      --------------------------------------------- CCAssignChecked
    → Γ ; Σ ; gc ; pc ⊢ L :=✓ M ⦂ ` Unit of l low

  ⊢prot : ∀ {Γ Σ gc pc A M ℓ}
    → Γ ; Σ ; gc ⋎̃ l ℓ ; pc ⋎ ℓ ⊢ M ⦂ A
      ----------------------------------------------- CCProt
    → Γ ; Σ ; gc ; pc ⊢ prot ℓ M ⦂ stamp A (l ℓ)

  ⊢cast : ∀ {Γ Σ gc pc A B M} {c : Cast A ⇒ B}
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
      ----------------------------------------- CCCast
    → Γ ; Σ ; gc ; pc ⊢ M ⟨ c ⟩ ⦂ B

  ⊢cast-pc : ∀ {Γ Σ gc pc A M g}
    → Γ ; Σ ; g ; pc ⊢ M ⦂ A
    → l pc ~ₗ g
      ----------------------------------------- CCCastPC
    → Γ ; Σ ; gc ; pc ⊢ cast-pc g M ⦂ A

  ⊢err : ∀ {Γ Σ gc pc A e}
      ------------------------------------ CCError
    → Γ ; Σ ; gc ; pc ⊢ error e ⦂ A

  ⊢sub : ∀ {Γ Σ gc pc A B M}
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
    → A <: B
      -------------------------- CCSub
    → Γ ; Σ ; gc ; pc ⊢ M ⦂ B

  ⊢sub-pc : ∀ {Γ Σ gc gc′ pc A M}
    → Γ ; Σ ; gc′ ; pc ⊢ M ⦂ A
    → gc <:ₗ gc′
      -------------------------- CCSubPC
    → Γ ; Σ ; gc  ; pc ⊢ M ⦂ A

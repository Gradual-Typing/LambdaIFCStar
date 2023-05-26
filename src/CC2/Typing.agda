{- Typing rules of CC2 -}

open import Common.Types

module CC2.Typing where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Common.Utils
open import Common.Types
open import Common.Coercions
open import Memory.HeapContext
open import CC2.Syntax


infix 4 _;_;_;_⊢_⇐_

data _;_;_;_⊢_⇐_ : Context → HeapContext → Label → StaticLabel → Term → Type → Set where

  ⊢const : ∀ {Γ Σ gc ℓv ι} {k : rep ι} {ℓ}
      -------------------------------------------- Const
    → Γ ; Σ ; gc ; ℓv ⊢ $ k ⇐ ` ι of ℓ


  ⊢addr : ∀ {Γ Σ gc ℓv n T ℓ ℓ̂}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
      ------------------------------------------------------------------- Addr
    → Γ ; Σ ; gc ; ℓv ⊢ addr n ⇐ Ref (T of l ℓ̂) of l ℓ


  ⊢var : ∀ {Γ Σ gc ℓv A x}
    → Γ ∋ x ⦂ A
      ----------------------------- Var
    → Γ ; Σ ; gc ; ℓv ⊢ ` x ⇐ A


  ⊢lam : ∀ {Γ Σ gc ℓv g A B N ℓ}
    → (∀ {ℓv} → A ∷ Γ ; Σ ; g ; ℓv ⊢ N ⇐ B)
      ------------------------------------------------------------------- Lambda
    → Γ ; Σ ; gc ; ℓv ⊢ ƛ N ⇐ ⟦ g ⟧ A ⇒ B of l ℓ


  ⊢app : ∀ {Γ Σ ℓc ℓv A B C L M ℓ}
    → Γ ; Σ ; l ℓc ; ℓv ⊢ L ⇐ ⟦ l (ℓc ⋎ ℓ) ⟧ A ⇒ B of l ℓ
    → Γ ; Σ ; l ℓc ; ℓv ⊢ M ⇐ A
    → C ≡ stamp B (l ℓ)
      ------------------------------------------------------ AppStatic
    → Γ ; Σ ; l ℓc ; ℓv ⊢ app L M A B ℓ ⇐ C


  ⊢app! : ∀ {Γ Σ gc ℓv A B C L M g}
    → Γ ; Σ ; gc ; ℓv ⊢ L ⇐ ⟦ ⋆ ⟧ A ⇒ B of g
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
    → C ≡ stamp B g
      ------------------------------------------------------ App!
    → Γ ; Σ ; gc ; ℓv ⊢ app! L M A B g ⇐ C


  ⊢if : ∀ {Γ Σ ℓc ℓv A B L M N ℓ}
    → Γ ; Σ ; l ℓc ; ℓv ⊢ L ⇐ ` Bool of l ℓ
    → (∀ {ℓv} → Γ ; Σ ; l (ℓc ⋎ ℓ) ; ℓv ⊢ M ⇐ A)
    → (∀ {ℓv} → Γ ; Σ ; l (ℓc ⋎ ℓ) ; ℓv ⊢ N ⇐ A)
    → B ≡ stamp A (l ℓ)
      --------------------------------------------------------- CCIf
    → Γ ; Σ ; l ℓc ; ℓv ⊢ if L A ℓ M N ⇐ B


  -- ⊢if⋆ : ∀ {Γ Σ gc pc A L M N}
  --   → Γ ; Σ ; gc ; pc ⊢ L ⇐ ` Bool of ⋆
  --   → (∀ {pc} → Γ ; Σ ; ⋆ ; pc ⊢ M ⇐ A)
  --   → (∀ {pc} → Γ ; Σ ; ⋆ ; pc ⊢ N ⇐ A)
  --     --------------------------------------------------------- CCIf⋆
  --   → Γ ; Σ ; gc ; pc ⊢ if⋆ L A M N ⇐ stamp A ⋆

  -- ⊢let : ∀ {Γ Σ gc pc M N A B}
  --   → Γ       ; Σ ; gc ; pc ⊢ M ⇐ A
  --   → (∀ {pc} → A ∷ Γ ; Σ ; gc ; pc ⊢ N ⇐ B)
  --     ----------------------------------- CCLet
  --   → Γ ; Σ ; gc ; pc ⊢ `let M A N ⇐ B

  -- ⊢ref : ∀ {Γ Σ pc pc′ M T ℓ}
  --   → Γ ; Σ ; l pc′ ; pc ⊢ M ⇐ T of l ℓ
  --   → pc′ ≼ ℓ
  --     ---------------------------------------------------------- CCRefStatic
  --   → Γ ; Σ ; l pc′ ; pc ⊢ ref⟦ ℓ ⟧ T M ⇐ Ref (T of l ℓ) of l low

  -- ⊢ref? : ∀ {Γ Σ gc pc M T ℓ p}
  --   → Γ ; Σ ; gc ; pc ⊢ M ⇐ T of l ℓ
  --     ---------------------------------------------------------- CCRefUnchecked
  --   → Γ ; Σ ; gc ; pc ⊢ ref?⟦ ℓ ⟧ T M p ⇐ Ref (T of l ℓ) of l low

  -- ⊢ref✓ : ∀ {Γ Σ gc pc M T ℓ}
  --   → Γ ; Σ ; gc ; pc ⊢ M ⇐ T of l ℓ
  --   → pc ≼ ℓ
  --     ---------------------------------------------------------- CCRefChecked
  --     → Γ ; Σ ; gc ; pc ⊢ ref✓⟦ ℓ ⟧ T M ⇐ Ref (T of l ℓ) of l low

  -- ⊢deref : ∀ {Γ Σ gc pc M A g}
  --   → Γ ; Σ ; gc ; pc ⊢ M ⇐ Ref A of g
  --     ------------------------------------- CCDeref
  --   → Γ ; Σ ; gc ; pc ⊢ ! M A g ⇐ stamp A g

  -- ⊢assign : ∀ {Γ Σ pc pc′ L M T ℓ ℓ̂}
  --   → Γ ; Σ ; l pc′ ; pc ⊢ L ⇐ Ref (T of l ℓ̂) of l ℓ
  --   → Γ ; Σ ; l pc′ ; pc ⊢ M ⇐ T of l ℓ̂
  --   → ℓ ≼ ℓ̂ → pc′ ≼ ℓ̂
  --     --------------------------------------------- CCAssignStatic
  --   → Γ ; Σ ; l pc′ ; pc ⊢ assign L M T ℓ̂ ℓ ⇐ ` Unit of l low

  -- ⊢assign? : ∀ {Γ Σ gc pc L M T p}
  --   → Γ ; Σ ; gc ; pc ⊢ L ⇐ Ref (T of ⋆) of ⋆
  --   → (∀ {pc} → Γ ; Σ ; gc ; pc ⊢ M ⇐ T of ⋆)
  --     --------------------------------------------- CCAssignUnchecked
  --   → Γ ; Σ ; gc ; pc ⊢ assign? L M T p ⇐ ` Unit of l low

  -- ⊢assign✓ : ∀ {Γ Σ gc pc L M T ℓ ℓ̂}
  --   → Γ ; Σ ; gc ; pc ⊢ L ⇐ Ref (T of l ℓ̂) of l ℓ
  --   → Γ ; Σ ; gc ; pc ⊢ M ⇐ T of l ℓ̂
  --   → ℓ ≼ ℓ̂ → pc ≼ ℓ̂
  --     --------------------------------------------- CCAssignChecked
  --   → Γ ; Σ ; gc ; pc ⊢ assign✓ L M T ℓ̂ ℓ ⇐ ` Unit of l low

  -- ⊢prot : ∀ {Γ Σ gc pc A M g ℓ}
  --   → Γ ; Σ ; g ⋎̃ l ℓ ; pc ⋎ ℓ ⊢ M ⇐ A
  --   → l pc ~ₗ g
  --     ----------------------------------------------- CCProt
  --   → Γ ; Σ ; gc ; pc ⊢ prot g ℓ A M ⇐ stamp A (l ℓ)

  -- ⊢cast : ∀ {Γ Σ gc pc A B C M} {c : Cast A ⇒ B}
  --   → Γ ; Σ ; gc ; pc ⊢ M ⇐ A
  --   → B <: C
  --     ----------------------------------------- CCCast
  --   → Γ ; Σ ; gc ; pc ⊢ M ⟨ c ⟩ ⇐ C

  -- ⊢err : ∀ {Γ Σ gc pc A e p}
  --     ------------------------------------ CCError
  --   → Γ ; Σ ; gc ; pc ⊢ blame e p ⇐ A

  -- -- ⊢sub : ∀ {Γ Σ gc pc A B M}
  -- --   → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  -- --   → A <: B
  -- --     -------------------------- CCSub
  -- --   → Γ ; Σ ; gc ; pc ⊢ M ⦂ B

  -- -- ⊢sub-pc : ∀ {Γ Σ gc gc′ pc A M}
  -- --   → Γ ; Σ ; gc′ ; pc ⊢ M ⦂ A
  -- --   → gc <:ₗ gc′
  -- --     -------------------------- CCSubPC
  -- --   → Γ ; Σ ; gc  ; pc ⊢ M ⦂ A

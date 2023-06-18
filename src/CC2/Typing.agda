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
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ)
open import Memory.HeapContext
open import CC2.Syntax


infix 4 _;_;_;_⊢_⇐_

data _;_;_;_⊢_⇐_ : Context → HeapContext → Label → StaticLabel → Term → Type → Set where

  ⊢const : ∀ {Γ Σ gc ℓv ι} {k : rep ι} {ℓ}
      -------------------------------------------- Const
    → Γ ; Σ ; gc ; ℓv ⊢ $ k ⇐ ` ι of l ℓ


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
      --------------------------------------------------------- If
    → Γ ; Σ ; l ℓc ; ℓv ⊢ if L A ℓ M N ⇐ B


  ⊢if! : ∀ {Γ Σ gc ℓv A B L M N g}
    → Γ ; Σ ; gc ; ℓv ⊢ L ⇐ ` Bool of g
    → (∀ {ℓv} → Γ ; Σ ; ⋆ ; ℓv ⊢ M ⇐ A)
    → (∀ {ℓv} → Γ ; Σ ; ⋆ ; ℓv ⊢ N ⇐ A)
    → B ≡ stamp A g
      --------------------------------------------------------- If!
    → Γ ; Σ ; gc ; ℓv ⊢ if! L A g M N ⇐ B


  ⊢let : ∀ {Γ Σ gc ℓv M N A B}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
    → (∀ {ℓv} → A ∷ Γ ; Σ ; gc ; ℓv ⊢ N ⇐ B)
      --------------------------------------------- Let
    → Γ ; Σ ; gc ; ℓv ⊢ `let M A N ⇐ B


  ⊢ref : ∀ {Γ Σ ℓc ℓv M T ℓ}
    → Γ ; Σ ; l ℓc ; ℓv ⊢ M ⇐ T of l ℓ
    → ℓc ≼ ℓ
      ---------------------------------------------------------------- RefStatic
    → Γ ; Σ ; l ℓc ; ℓv ⊢ ref⟦ ℓ ⟧ M ⇐ Ref (T of l ℓ) of l low


  ⊢ref? : ∀ {Γ Σ gc ℓv M T ℓ p}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ T of l ℓ
      ---------------------------------------------------------------- Ref?
    → Γ ; Σ ; gc ; ℓv ⊢ ref?⟦ ℓ ⟧ M p ⇐ Ref (T of l ℓ) of l low


  ⊢deref : ∀ {Γ Σ gc ℓv M A B g}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ Ref A of g
    → B ≡ stamp A g
      ------------------------------------- Deref
    → Γ ; Σ ; gc ; ℓv ⊢ ! M A g ⇐ B


  ⊢assign : ∀ {Γ Σ ℓc ℓv L M T ℓ ℓ̂}
    → Γ ; Σ ; l ℓc ; ℓv ⊢ L ⇐ Ref (T of l ℓ̂) of l ℓ
    → Γ ; Σ ; l ℓc ; ℓv ⊢ M ⇐ T of l ℓ̂
    → ℓc ≼ ℓ̂ → ℓ ≼ ℓ̂
      ------------------------------------------------------------- AssignStatic
    → Γ ; Σ ; l ℓc ; ℓv ⊢ assign L M T ℓ̂ ℓ ⇐ ` Unit of l low


  ⊢assign? : ∀ {Γ Σ gc ℓv L M T g ĝ p}
    → Γ ; Σ ; gc ; ℓv ⊢ L ⇐ Ref (T of ĝ) of g
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ T of ĝ
      ------------------------------------------------------------- Assign?
    → Γ ; Σ ; gc ; ℓv ⊢ assign? L M T ĝ g p ⇐ ` Unit of l low


  ⊢prot : ∀ {Γ Σ gc gc′ ℓv ℓv′ A B M ℓ} {PC : LExpr} {v : LVal PC}
    → Γ ; Σ ; gc′ ; ℓv′ ⊢ M ⇐ A
    → ⊢ PC ⇐ gc′
    → ∥ PC ∥ v ≡ ℓv′
    → ℓv ⋎ ℓ ≼ ℓv′
    → B ≡ stamp A (l ℓ)
      ------------------------------------------- Prot
    → Γ ; Σ ; gc ; ℓv ⊢ prot PC v ℓ M A ⇐ B


  -- ⊢prot-cast : ∀ {Γ Σ gc gc′ gc″ ℓv A B M ℓ} {c̅ : CoercionExp gc″ ⇒ gc′}
  --   → (∀ {ℓv} → Γ ; Σ ; gc′ ; ℓv ⊢ M ⇐ A)
  --   → gc ⋎̃ l ℓ ≾ gc″
  --   → NotProj (gc ⋎̃ l ℓ) gc″
  --   → B ≡ stamp A (l ℓ)
  --     ---------------------------------------------------- ProtCast
  --   → Γ ; Σ ; gc ; ℓv ⊢ prot-cast c̅ ℓ M A ⇐ B


  ⊢cast : ∀ {Γ Σ gc ℓv A B M} {c : Cast A ⇒ B}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
      ----------------------------------------- Cast
    → Γ ; Σ ; gc ; ℓv ⊢ M ⟨ c ⟩ ⇐ B


  ⊢err : ∀ {Γ Σ gc ℓv A p}
      ------------------------------------ Blame
    → Γ ; Σ ; gc ; ℓv ⊢ blame p ⇐ A

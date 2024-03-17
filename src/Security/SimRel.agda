{- The security simulation relation between CC2 and Dyn -}

open import Common.Types

module Security.SimRel where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils

open import Common.Coercions
open import Memory.Addr
open import CC2.Statics
  renaming (Term to CCTerm; `_ to var; $_ to const; ƛ to lam; addr to adrs; if to `if;
            ref⟦_⟧ to refer; ref?⟦_⟧ to refer?; prot to protect; ! to deref; !⋆ to deref⋆)
open import Dyn.Syntax


infix 4 _≤_⇐_

data _≤_⇐_ : Term → CCTerm → Type → Set where

  ≤-var : ∀ {x A}
      -----------------------
    → ` x ≤ var x ⇐ A

  ≤-const : ∀ {ι} {k : rep ι} {ℓ ℓ′}
    → ℓ′ ≼ ℓ
      ---------------------------------------
    → ($ k of ℓ′) ≤ const k ⇐ ` ι of l ℓ

  ≤-wrapped-const : ∀ {ι} {k : rep ι} {g ℓ ℓ′} {c̅ : CExpr l ℓ ⇒ g}
    → (𝓋 : CVal c̅)
    → l ℓ ≢ g
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      --------------------------------------------------------------------
    → ($ k of ℓ′) ≤ (const k) ⟨ cast (Castᵣ_⇒_.id ι) c̅ ⟩ ⇐ ` ι of g

  ≤-lam : ∀ {N N′ g A B ℓ ℓ′}
    → N′ ≤ N ⇐ B
    → ℓ′ ≼ ℓ
      -------------------------------------------
    → (ƛ N′ of ℓ′) ≤ lam N ⇐ ⟦ g ⟧ A ⇒ B of l ℓ

  ≤-wrapped-lam : ∀ {N N′ g₁ g₂ g₃ A B C D ℓ ℓ′}
                    {c̅ : CExpr l ℓ ⇒ g₂} {d̅ : CExpr g₁ ⇒ g₃} {c : Cast A ⇒ C} {d : Cast D ⇒ B}
    → N′ ≤ N ⇐ B
    → (𝓋 : CVal c̅)
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      --------------------------------------------
    → (ƛ N′ of ℓ′) ≤ (lam N) ⟨ cast (fun d̅ c d) c̅ ⟩ ⇐ ⟦ g₁ ⟧ A ⇒ B of g₂

  ≤-addr : ∀ {n T ℓ ℓ′ ℓ̂}
    → ℓ′ ≼ ℓ
      ------------------------------------------------------------
    → (addr (a⟦ ℓ̂ ⟧ n) of ℓ′) ≤ adrs n ⇐ Ref (T of l ℓ̂) of l ℓ

  ≤-wrapped-addr : ∀ {n g₁ g₂ S T ℓ ℓ′ ℓ̂}
                     {c̅ : CExpr l ℓ ⇒ g₂} {c : Cast T of g₁ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of g₁}
    → (𝓋 : CVal c̅)
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      ------------------------------------------------------------
    → (addr (a⟦ ℓ̂ ⟧ n) of ℓ′) ≤ (adrs n) ⟨ cast (ref c d) c̅ ⟩ ⇐ Ref (T of g₁) of g₂

  ≤-app : ∀ {M M′ N N′} {g A B C ℓ}
    → M′ ≤ M ⇐ ⟦ g ⟧ A ⇒ B of l ℓ
    → N′ ≤ N ⇐ A
      ------------------------------------
    → M′ · N′ ≤ app M N A B ℓ ⇐ C

  ≤-app⋆ : ∀ {M M′ N N′} {A T}
    → M′ ≤ M ⇐ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆
    → N′ ≤ N ⇐ A
      ------------------------------------
    → M′ · N′ ≤ app⋆ M N A T ⇐ T of ⋆

  ≤-if : ∀ {L L′ M M′ N N′} {A B ℓ}
    → L′ ≤ L ⇐ ` Bool of l ℓ
    → M′ ≤ M ⇐ A
    → N′ ≤ N ⇐ A
      ----------------------------------------
    → if L′ M′ N′ ≤ `if L A ℓ M N ⇐ B

  ≤-if⋆ : ∀ {L L′ M M′ N N′} {T}
    → L′ ≤ L ⇐ ` Bool of ⋆
    → M′ ≤ M ⇐ T of ⋆
    → N′ ≤ N ⇐ T of ⋆
      ------------------------------------
    → if L′ M′ N′ ≤ if⋆ L T M N ⇐ T of ⋆

  ≤-ref : ∀ {M M′ T ℓ}
    → M′ ≤ M ⇐ T of l ℓ
      --------------------------------------------------------
    → ref?⟦ ℓ ⟧ M′ ≤ refer ℓ M ⇐ Ref (T of l ℓ) of l low

  ≤-ref? : ∀ {M M′ T ℓ} {p}
    → M′ ≤ M ⇐ T of l ℓ
      -----------------------------------------------------------
    → ref?⟦ ℓ ⟧ M′ ≤ refer? ℓ M p ⇐ Ref (T of l ℓ) of l low

  ≤-deref : ∀ {M M′ A B ℓ}
    → M′ ≤ M ⇐ Ref A of l ℓ
      --------------------------------
    → ! M′ ≤ deref M A ℓ ⇐ B

  ≤-deref⋆ : ∀ {M M′ T}
    → M′ ≤ M ⇐ Ref (T of ⋆) of ⋆
      --------------------------------
    → ! M′ ≤ deref⋆ M T ⇐ T of ⋆

  ≤-assign : ∀ {L L′ M M′} {T ℓ ℓ̂}
    → L′ ≤ L ⇐ Ref (T of l ℓ̂) of l ℓ
    → M′ ≤ M ⇐ T of l ℓ̂
      ------------------------------------------------
    → L′ :=? M′ ≤ assign L M T ℓ̂ ℓ ⇐ ` Unit of l low

  ≤-assign? : ∀ {L L′ M M′} {T g p}
    → L′ ≤ L ⇐ Ref (T of g) of ⋆
    → M′ ≤ M ⇐ T of g
      ------------------------------------------------
    → L′ :=? M′ ≤ assign? L M T g p ⇐ ` Unit of l low

  ≤-prot : ∀ {M M′ ℓ ℓ′ A B} {PC : LExpr} {v : LVal PC}
    → ℓ′ ≼ ℓ
    → M′ ≤ M ⇐ A
      --------------------------------------------
    → prot ℓ′ M′ ≤ protect PC v ℓ M A ⇐ B

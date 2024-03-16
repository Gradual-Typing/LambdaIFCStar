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
open import CC2.Statics renaming (Term to CCTerm; `_ to var; $_ to const; ƛ to lam; addr to adrs)
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

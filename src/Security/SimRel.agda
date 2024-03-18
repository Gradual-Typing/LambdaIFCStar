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


infix 4 _⊢_≤_⇐_

data _⊢_≤_⇐_ : Label → Term → CCTerm → Type → Set where

  ≤-var : ∀ {gc x A}
      -----------------------
    → gc ⊢ ` x ≤ var x ⇐ A

  ≤-const : ∀ {gc} {ι} {k : rep ι} {ℓ ℓ′}
    → ℓ′ ≼ ℓ
      ---------------------------------------
    → gc ⊢ ($ k of ℓ′) ≤ const k ⇐ ` ι of l ℓ

  ≤-wrapped-const : ∀ {gc} {ι} {k : rep ι} {g ℓ ℓ′} {c̅ : CExpr l ℓ ⇒ g}
    → (𝓋 : CVal c̅)
    → l ℓ ≢ g
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      --------------------------------------------------------------------
    → gc ⊢ ($ k of ℓ′) ≤ (const k) ⟨ cast (Castᵣ_⇒_.id ι) c̅ ⟩ ⇐ ` ι of g

  ≤-lam : ∀ {gc N N′ g A B ℓ ℓ′}
    → g ⊢ N′ ≤ N ⇐ B
    → ℓ′ ≼ ℓ
      -------------------------------------------
    → gc ⊢ (ƛ N′ of ℓ′) ≤ lam N ⇐ ⟦ g ⟧ A ⇒ B of l ℓ

  ≤-wrapped-lam : ∀ {gc N N′ g₁ g₂ g₃ A B C D ℓ ℓ′}
                    {c̅ : CExpr l ℓ ⇒ g₂} {d̅ : CExpr g₁ ⇒ g₃} {c : Cast A ⇒ C} {d : Cast D ⇒ B}
    → g₃ ⊢ N′ ≤ N ⇐ D
    → (𝓋 : CVal c̅)
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      --------------------------------------------
    → gc ⊢ (ƛ N′ of ℓ′) ≤ (lam N) ⟨ cast (fun d̅ c d) c̅ ⟩ ⇐ ⟦ g₁ ⟧ A ⇒ B of g₂

  ≤-addr : ∀ {gc n T ℓ ℓ′ ℓ̂}
    → ℓ′ ≼ ℓ
      ------------------------------------------------------------
    → gc ⊢ (addr (a⟦ ℓ̂ ⟧ n) of ℓ′) ≤ adrs n ⇐ Ref (T of l ℓ̂) of l ℓ

  ≤-wrapped-addr : ∀ {gc n g₁ g₂ S T ℓ ℓ′ ℓ̂}
                     {c̅ : CExpr l ℓ ⇒ g₂} {c : Cast T of g₁ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of g₁}
    → (𝓋 : CVal c̅)
    → ℓ′ ≼ ∥ c̅ ∥ₗ 𝓋
      ------------------------------------------------------------
    → gc ⊢ (addr (a⟦ ℓ̂ ⟧ n) of ℓ′) ≤ (adrs n) ⟨ cast (ref c d) c̅ ⟩ ⇐ Ref (T of g₁) of g₂

  ≤-app : ∀ {ℓc M M′ N N′} {A B C ℓ}
    → l ℓc ⊢ M′ ≤ M ⇐ ⟦ l (ℓc ⋎ ℓ) ⟧ A ⇒ B of l ℓ
    → l ℓc ⊢ N′ ≤ N ⇐ A
      ------------------------------------
    → l ℓc ⊢ M′ · N′ ≤ app M N A B ℓ ⇐ C

  ≤-app⋆ : ∀ {gc M M′ N N′} {A T}
    → gc ⊢ M′ ≤ M ⇐ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆
    → gc ⊢ N′ ≤ N ⇐ A
      ------------------------------------
    → gc ⊢ M′ · N′ ≤ app⋆ M N A T ⇐ T of ⋆

  ≤-if : ∀ {ℓc L L′ M M′ N N′} {A B ℓ}
    → l ℓc ⊢ L′ ≤ L ⇐ ` Bool of l ℓ
    → l (ℓc ⋎ ℓ) ⊢ M′ ≤ M ⇐ A
    → l (ℓc ⋎ ℓ) ⊢ N′ ≤ N ⇐ A
      ----------------------------------------
    → l ℓc ⊢ if L′ M′ N′ ≤ `if L A ℓ M N ⇐ B

  ≤-if⋆ : ∀ {gc L L′ M M′ N N′} {T}
    → gc ⊢ L′ ≤ L ⇐ ` Bool of ⋆
    → ⋆ ⊢ M′ ≤ M ⇐ T of ⋆
    → ⋆ ⊢ N′ ≤ N ⇐ T of ⋆
      ------------------------------------
    → gc ⊢ if L′ M′ N′ ≤ if⋆ L T M N ⇐ T of ⋆

  ≤-ref : ∀ {ℓc M M′ T ℓ}
    → l ℓc ⊢ M′ ≤ M ⇐ T of l ℓ
      --------------------------------------------------------
    → l ℓc ⊢ ref?⟦ ℓ ⟧ M′ ≤ refer ℓ M ⇐ Ref (T of l ℓ) of l low

  ≤-ref? : ∀ {M M′ T ℓ} {p}
    → ⋆ ⊢ M′ ≤ M ⇐ T of l ℓ
      -----------------------------------------------------------
    → ⋆ ⊢ ref?⟦ ℓ ⟧ M′ ≤ refer? ℓ M p ⇐ Ref (T of l ℓ) of l low

  ≤-deref : ∀ {gc M M′ A B ℓ}
    → gc ⊢ M′ ≤ M ⇐ Ref A of l ℓ
      --------------------------------
    → gc ⊢ ! M′ ≤ deref M A ℓ ⇐ B

  ≤-deref⋆ : ∀ {gc M M′ T}
    → gc ⊢ M′ ≤ M ⇐ Ref (T of ⋆) of ⋆
      --------------------------------
    → gc ⊢ ! M′ ≤ deref⋆ M T ⇐ T of ⋆

  ≤-assign : ∀ {ℓc L L′ M M′} {T ℓ ℓ̂}
    → l ℓc ⊢ L′ ≤ L ⇐ Ref (T of l ℓ̂) of l ℓ
    → l ℓc ⊢ M′ ≤ M ⇐ T of l ℓ̂
      ------------------------------------------------
    → l ℓc ⊢ L′ :=? M′ ≤ assign L M T ℓ̂ ℓ ⇐ ` Unit of l low

  ≤-assign? : ∀ {gc L L′ M M′} {T g p}
    → gc ⊢ L′ ≤ L ⇐ Ref (T of g) of ⋆
    → gc ⊢ M′ ≤ M ⇐ T of g
      ------------------------------------------------
    → gc ⊢ L′ :=? M′ ≤ assign? L M T g p ⇐ ` Unit of l low

  ≤-cast : ∀ {gc M M′ A B} {c : Cast A ⇒ B}
    → gc ⊢ M′ ≤ M ⇐ A
      ------------------------------------
    → gc ⊢ M′ ≤ M ⟨ c ⟩ ⇐ B

  ≤-prot : ∀ {g₁ g₂ M M′ ℓ ℓ′ A B} {PC : LExpr} {v : LVal PC}
    → ℓ′ ≼ ℓ
    → g₂ ⊢ M′ ≤ M ⇐ A
    → ⊢ PC ⇐ g₂
      --------------------------------------------
    → g₁ ⊢ prot ℓ′ M′ ≤ protect PC v ℓ M A ⇐ B


≤-value-pc : ∀ {g₁ g₂ M V A}
  → g₁ ⊢ M ≤ V ⇐ A
  → Value V
    --------------------------------
  → g₂ ⊢ M ≤ V ⇐ A
≤-value-pc (≤-addr x) (V-raw V-addr) = ≤-addr x
≤-value-pc (≤-lam x y) (V-raw V-ƛ) = ≤-lam x y
≤-value-pc (≤-const x) (V-raw V-const) = ≤-const x
≤-value-pc (≤-wrapped-addr 𝓋 x) (V-cast V-addr x₁) = ≤-wrapped-addr 𝓋 x
≤-value-pc (≤-cast (≤-addr x)) (V-cast V-addr i) = ≤-cast (≤-addr x)
≤-value-pc (≤-wrapped-lam M≤V 𝓋 x) (V-cast V-ƛ i) = ≤-wrapped-lam M≤V 𝓋 x
≤-value-pc (≤-cast (≤-lam M≤V x)) (V-cast V-ƛ i) = ≤-cast (≤-lam M≤V x)
≤-value-pc (≤-wrapped-const 𝓋 x y) (V-cast V-const x₁) = ≤-wrapped-const 𝓋 x y
≤-value-pc (≤-cast (≤-const x)) (V-cast V-const x₁) = ≤-cast (≤-const x)

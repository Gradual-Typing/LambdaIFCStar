{- Precision relation of CC2 -}

open import Common.Types

module CC2.Precision where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils
open import Common.CoercionPrecision public

open import Memory.HeapContext
open import CC2.Statics
open import CC2.HeapContextPrecision public


infix 4 _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_

data _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_ : (Γ Γ′ : Context) (Σ Σ′ : HeapContext)
  (g g′ : Label) (ℓ ℓ′ : StaticLabel) (M M′ : Term) (A A′ : Type) → Set where

  ⊑-var : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ x}
    → Γ  ∋ x ⦂ A
    → Γ′ ∋ x ⦂ A′
      ---------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ` x ⊑ ` x ⇐ A ⊑ A′


  ⊑-const : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ ι ℓ} {k : rep ι}
      ---------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ $ k ⊑ $ k
         ⇐ ` ι of l ℓ ⊑ ` ι of l ℓ


  ⊑-addr : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {n ℓ ℓ̂ T T′}
    → lookup-Σ Σ  (a⟦ ℓ̂ ⟧ n) ≡ just T
    → lookup-Σ Σ′ (a⟦ ℓ̂ ⟧ n) ≡ just T′
      -------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ addr n ⊑ addr n
         ⇐ Ref (T of l ℓ̂) of l ℓ ⊑ Ref (T′ of l ℓ̂) of l ℓ


  ⊑-lam : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {N N′} {g g′ A A′ B B′ ℓ}
    → g ⊑ₗ g′
    → A ⊑  A′
    → (∀ {ℓv ℓv′} → A ∷ Γ ; A′ ∷ Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ B ⊑ B′)
      --------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ƛ N ⊑ ƛ N′
         ⇐ ⟦ g ⟧ A ⇒ B of l ℓ ⊑ ⟦ g′ ⟧ A′ ⇒ B′ of l ℓ


  ⊑-app : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′} {A A′ B B′ C C′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ l (ℓc ⋎ ℓ) ⟧ A ⇒ B of l ℓ ⊑ ⟦ l (ℓc ⋎ ℓ) ⟧ A′ ⇒ B′ of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → C  ≡ stamp B  (l ℓ)
    → C′ ≡ stamp B′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ app L M A B ℓ ⊑ app L′ M′ A′ B′ ℓ ⇐ C ⊑ C′


  ⊑-app! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′} {A A′ T T′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆ ⊑ ⟦ ⋆ ⟧ A′ ⇒ (T′ of ⋆) of ⋆
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ app! L M A T ⊑ app! L′ M′ A′ T′ ⇐ T of ⋆ ⊑ T′ of ⋆


  ⊑-app!l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′} {A A′ T B′ C′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆ ⊑ ⟦ l (ℓc ⋎ ℓ) ⟧ A′ ⇒ B′ of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → C′ ≡ stamp B′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ app! L M A T ⊑ app L′ M′ A′ B′ ℓ ⇐ T of ⋆ ⊑ C′


  ⊑-if : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′ N N′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of l ℓ ⊑ ` Bool of l ℓ
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l (ℓc ⋎ ℓ) ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l (ℓc ⋎ ℓ) ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ A ⊑ A′)
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ if L A ℓ M N ⊑ if L′ A′ ℓ M′ N′ ⇐ B ⊑ B′


  ⊑-if! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′ N N′} {T T′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of ⋆ ⊑ ` Bool of ⋆
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ⋆ ⊑ T′ of ⋆)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ T of ⋆ ⊑ T′ of ⋆)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ if! L T M N ⊑ if! L′ T′ M′ N′ ⇐ T of ⋆ ⊑ T′ of ⋆


  ⊑-if!l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′ N N′} {T A′ B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of ⋆ ⊑ ` Bool of l ℓ
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ⋆ ⊑ A′)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ T of ⋆ ⊑ A′)
    → B′ ≡ stamp A′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ if! L T M N ⊑ if L′ A′ ℓ M′ N′ ⇐ T of ⋆ ⊑ B′


  ⊑-let : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′ N N′} {A A′ B B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′
    → (∀ {ℓv ℓv′} → A ∷ Γ ; A′ ∷ Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ B ⊑ B′)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ `let M A N ⊑ `let M′ A′ N′ ⇐ B ⊑ B′


  ⊑-ref : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {M M′} {T T′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
    → ℓc ≼ ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ ref⟦ ℓ ⟧ M ⊑ ref⟦ ℓ ⟧ M′
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-ref? : ∀ {Γ Γ′ Σ Σ′ ℓv ℓv′} {M M′} {T T′ ℓ} {p q}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ ref?⟦ ℓ ⟧ M p ⊑ ref?⟦ ℓ ⟧ M′ q
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-ref?l : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {M M′} {T T′ ℓ} {p}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
    → ℓc ≼ ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l ℓc ∣ ℓv ; ℓv′ ⊢ ref?⟦ ℓ ⟧ M p ⊑ ref⟦ ℓ ⟧ M′
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-deref : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref A of l ℓ ⊑ Ref A′ of l ℓ
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ! M A ℓ ⊑ ! M′ A′ ℓ ⇐ B ⊑ B′


  ⊑-deref! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {T T′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref (T of ⋆) of ⋆ ⊑ Ref (T′ of ⋆) of ⋆
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ !! M T ⊑ !! M′ T′ ⇐ T of ⋆ ⊑ T′ of ⋆


  ⊑-deref!l : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {T A′ B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref (T of ⋆) of ⋆ ⊑ Ref A′ of l ℓ
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ !! M T ⊑ ! M′ A′ ℓ ⇐ T of ⋆ ⊑ B′


  ⊑-assign : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′} {T T′ ℓ̂ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of l ℓ̂) of l ℓ ⊑ Ref (T′ of l ℓ̂) of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of l ℓ̂ ⊑ T′ of l ℓ̂
    → ℓc ≼ ℓ̂ → ℓ ≼ ℓ̂
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ assign L M T ℓ̂ ℓ ⊑ assign L′ M′ T′ ℓ̂ ℓ
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-assign? : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′} {T T′ ĝ ĝ′} {p q}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of ĝ) of ⋆ ⊑ Ref (T′ of ĝ′) of ⋆
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ĝ ⊑ T′ of ĝ′
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ assign? L M T ĝ p ⊑ assign? L′ M′ T′ ĝ′ q
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-assign?l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′} {T T′ ĝ ℓ̂ ℓ} {p}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of ĝ) of ⋆ ⊑ Ref (T′ of l ℓ̂) of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ĝ ⊑ T′ of l ℓ̂
    → ℓc ≼ ℓ̂ → ℓ ≼ ℓ̂
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ assign? L M T ĝ p ⊑ assign L′ M′ T′ ℓ̂ ℓ
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-prot : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {A A′ B B′ g g′ ℓ} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ ≼ ℓv₂′
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot PC vc ℓ M A ⊑ prot PC′ vc′ ℓ M′ A′ ⇐ B ⊑ B′


  ⊑-prot! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {T T′ g g′ ℓ ℓ′} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ T of ⋆ ⊑ T′ of ⋆
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ  ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ′ ≼ ℓv₂′
    → ℓ ≼ ℓ′
      --------------------------------------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot PC vc ℓ M (T of ⋆) ⊑ prot PC′ vc′ ℓ′ M′ (T′ of ⋆) ⇐ T of ⋆ ⊑ T′ of ⋆


  ⊑-prot!l : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {T A′ B′ g g′ ℓ ℓ′} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ T of ⋆ ⊑ A′
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ  ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ′ ≼ ℓv₂′
    → B′ ≡ stamp A′ (l ℓ′)
    → ℓ ≼ ℓ′
      -----------------------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot PC vc ℓ M (T of ⋆) ⊑ prot PC′ vc′ ℓ′ M′ A′ ⇐ T of ⋆ ⊑ B′


  ⊑-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′}
             {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → ⟨ c ⟩⊑⟨ c′ ⟩
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⇐ B ⊑ B′


  ⊑-castl : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B} {c : Cast A ⇒ B}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → ⟨ c ⟩⊑ A′
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⟨ c ⟩ ⊑ M′ ⇐ B ⊑ A′


  ⊑-castr : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B′} {c′ : Cast A′ ⇒ B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → A ⊑⟨ c′ ⟩
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⟨ c′ ⟩ ⇐ A ⊑ B′


  ⊑-blame : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M A A′ p}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
    → A ⊑ A′
      ------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ blame p ⇐ A ⊑ A′


{- The term precision relation implies that both terms are well-typed.
   Furthermore, their types are related by type precision. -}
cc-prec-inv : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    -------------------------------------------------------------
  → Γ  ; Σ  ; gc  ; ℓv  ⊢ M  ⇐ A    ×
     Γ′ ; Σ′ ; gc′ ; ℓv′ ⊢ M′ ⇐ A′   ×
     A ⊑ A′
cc-prec-inv Γ⊑Γ′ _ (⊑-var Γ∋x Γ′∋x) = ⟨ ⊢var Γ∋x , ⊢var Γ′∋x , ⊑*→⊑ Γ⊑Γ′ Γ∋x Γ′∋x ⟩
cc-prec-inv _ _ ⊑-const = ⟨ ⊢const , ⊢const , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv _ Σ⊑Σ′ (⊑-addr {n = n} {ℓ} {ℓ̂} Σa≡T Σ′a≡T′) =
  ⟨ ⊢addr Σa≡T , ⊢addr Σ′a≡T′ , ⊑-ty l⊑l (⊑-ref (⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ Σa≡T Σ′a≡T′))) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-lam g⊑g′ A⊑A′ N⊑N′) =
  let prec* = ⊑*-∷ A⊑A′ Γ⊑Γ′ in
  ⟨ ⊢lam (proj₁        (cc-prec-inv {ℓv′ = low} prec* Σ⊑Σ′ N⊑N′))  ,
    ⊢lam (proj₁ (proj₂ (cc-prec-inv {ℓv  = low} prec* Σ⊑Σ′ N⊑N′))) ,
    ⊑-ty l⊑l (⊑-fun g⊑g′ A⊑A′ (proj₂ (proj₂ (cc-prec-inv {ℓv = low} {low} prec* Σ⊑Σ′ N⊑N′)))) ⟩
{- Application -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app {C = C} {C′} L⊑L′ M⊑M′ eq eq′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty l⊑l (⊑-fun l⊑l A⊑A′ B⊑B′)) →
    let C⊑C′ : C ⊑ C′
        C⊑C′ = subst₂ _⊑_ (sym eq) (sym eq′) (stamp-⊑ B⊑B′ l⊑l) in
    ⟨ ⊢app ⊢L ⊢M eq , ⊢app ⊢L′ ⊢M′ eq′ , C⊑C′ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app! {T = T} {T′} L⊑L′ M⊑M′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A⊑A′ B⊑B′)) → ⟨ ⊢app! ⊢L ⊢M , ⊢app! ⊢L′ ⊢M′ , B⊑B′ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app!l {T = T} {C′ = C′} L⊑L′ M⊑M′ eq′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A⊑A′ B⊑B′)) →
    let C⊑C′ = subst (_ ⊑_) (sym eq′) (stamp-⊑ B⊑B′ l⊑l) in
    ⟨ ⊢app! ⊢L ⊢M , ⊢app ⊢L′ ⊢M′ eq′ , C⊑C′ ⟩
{- If -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if L⊑L′ M⊑M′ N⊑N′ eq eq′) rewrite eq | eq′ =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢if ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) refl ,
    ⊢if ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) refl ,
    stamp-⊑ (proj₂ (proj₂ (ihm low low))) l⊑l ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if! L⊑L′ M⊑M′ N⊑N′) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  case ihm low low of λ where
  ⟨ _ , _ , T⋆⊑T′⋆ ⟩ →
    ⟨ ⊢if! ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) ,
      ⊢if! ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) ,
      T⋆⊑T′⋆ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if!l L⊑L′ M⊑M′ N⊑N′ eq′) rewrite eq′ =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢if! ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) ,
    ⊢if  ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) refl ,
    stamp-⊑ (proj₂ (proj₂ (ihm low low))) ⋆⊑ ⟩
{- Let -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-let M⊑M′ N⊑N′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ih = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} (⊑*-∷ A⊑A′ Γ⊑Γ′) Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢let ⊢M (proj₁ (ih _ low)) ,
    ⊢let ⊢M′ (proj₁ (proj₂ (ih low _))) ,
    proj₂ (proj₂ (ih low low)) ⟩
{- Reference creation -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref M⊑M′ ℓc≼ℓ) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref ⊢M ℓc≼ℓ , ⊢ref ⊢M′ ℓc≼ℓ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref? M⊑M′) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref? ⊢M , ⊢ref? ⊢M′ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref?l M⊑M′ ℓc≼ℓ) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref? ⊢M , ⊢ref ⊢M′ ℓc≼ℓ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
{- Dereference -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref M⊑M′ eq eq′) rewrite eq | eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref A⊑A′) ⟩ →
    ⟨ ⊢deref ⊢M refl , ⊢deref ⊢M′ refl , stamp-⊑ A⊑A′ l⊑l ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref! M⊑M′) =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref T⋆⊑T′⋆) ⟩ →
    ⟨ ⊢deref! ⊢M , ⊢deref! ⊢M′ , T⋆⊑T′⋆ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref!l M⊑M′ eq′) rewrite eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref A⊑A′) ⟩ →
    ⟨ ⊢deref! ⊢M , ⊢deref ⊢M′ refl , stamp-⊑ A⊑A′ ⋆⊑ ⟩
{- Assignment -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign L⊑L′ M⊑M′ ℓc≼ℓ̂ ℓ≼ℓ̂) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign ⊢L ⊢M ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊢assign ⊢L′ ⊢M′ ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign? L⊑L′ M⊑M′) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign? ⊢L ⊢M , ⊢assign? ⊢L′ ⊢M′ , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign?l L⊑L′ M⊑M′  ℓc≼ℓ̂ ℓ≼ℓ̂) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign? ⊢L ⊢M , ⊢assign ⊢L′ ⊢M′ ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊑-ty l⊑l ⊑-ι ⟩
{- Protection -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot M⊑M′ PC⊑PC′ x x′ eq eq′) rewrite eq | eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ →
    let prec = prec→⊑ PC⊑PC′ in
    let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
    ⟨ ⊢prot ⊢M ⊢PC x refl , ⊢prot ⊢M′ ⊢PC′ x′ refl , stamp-⊑ A⊑A′ ⊑ₗ-refl ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot! M⊑M′ PC⊑PC′ x x′ ℓ≼ℓ′) =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ T⊑T′ ⟩ →
    let prec = prec→⊑ PC⊑PC′ in
    let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
    ⟨ ⊢prot ⊢M ⊢PC x refl , ⊢prot ⊢M′ ⊢PC′ x′ refl , ⊑-ty ⋆⊑ T⊑T′ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot!l M⊑M′ PC⊑PC′ x x′ eq′ ℓ≼ℓ′) rewrite eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ T⊑T′ ⟩ →
    let prec = prec→⊑ PC⊑PC′ in
    let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
    ⟨ ⊢prot ⊢M ⊢PC x refl , ⊢prot ⊢M′ ⊢PC′ x′ refl , ⊑-ty ⋆⊑ T⊑T′ ⟩
{- Cast -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-cast M⊑M′ c⊑c′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢cast ⊢M′ , proj₂ (coercion-prec→⊑ c⊑c′) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-castl M⊑M′ c⊑A′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢M′ , proj₂ (coercion-prec-left→⊑ c⊑A′) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-castr M⊑M′ A⊑c′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢M , ⊢cast ⊢M′ , proj₂ (coercion-prec-right→⊑ A⊑c′) ⟩
{- Blame -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-blame ⊢M A⊑A′) =
  ⟨ ⊢M , ⊢blame , A⊑A′ ⟩


cast-prec-inv : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ B B′ C C′ V W}
                  {c : Cast A ⇒ B} {d : Cast A′ ⇒ B′}
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⟨ c ⟩ ⊑ W ⟨ d ⟩ ⇐ C ⊑ C′
  → RawValue V
  → RawValue W
    ---------------------------------------------------------------------------
  → (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ W ⇐ A ⊑ A′) ×
     (⟨ c ⟩⊑⟨ d ⟩) × (B ≡ C) × (B′ ≡ C′)
cast-prec-inv (⊑-cast M⊑N c⊑d) v w = ⟨ M⊑N , c⊑d , refl , refl ⟩
cast-prec-inv (⊑-castl (⊑-castr V⊑W A⊑d) c⊑B′) v w =
  ⟨ V⊑W , comp-pres-prec-rl A⊑d c⊑B′ , refl , refl ⟩
cast-prec-inv (⊑-castr (⊑-castl V⊑W c⊑A′) B⊑d) v w =
  ⟨ V⊑W , comp-pres-prec-lr c⊑A′ B⊑d , refl , refl ⟩


{- ● is not in the precision relation -}
_⋤● : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′} M
  → ¬ (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ ● ⇐ A ⊑ A′)
((M ⟨ c ⟩) ⋤●) (⊑-castl M⊑● c⊑A′) = (M ⋤●) M⊑●

●⋤_ : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′} M
  → ¬ (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ● ⊑ M ⇐ A ⊑ A′)
(●⋤ (M ⟨ c ⟩)) (⊑-castr ●⊑M A⊑c) = (●⋤ M) ●⊑M


value-⊑-pc : ∀ {Γ Γ′ Σ Σ′ gc₁ gc₁′ gc₂ gc₂′ ℓv₁ ℓv₁′ ℓv₂ ℓv₂′} {A B} {V W}
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc₁ ; gc₁′ ∣ ℓv₁ ; ℓv₁′ ⊢ V ⊑ W ⇐ A ⊑ B
  → Value V
  → Value W
    -------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc₂ ; gc₂′ ∣ ℓv₂ ; ℓv₂′ ⊢ V ⊑ W ⇐ A ⊑ B
value-⊑-pc ⊑-const (V-raw V-const) (V-raw V-const) = ⊑-const
value-⊑-pc (⊑-addr x y) (V-raw V-addr) (V-raw V-addr) = ⊑-addr x y
value-⊑-pc (⊑-lam x y z) (V-raw V-ƛ) (V-raw V-ƛ) = ⊑-lam x y z
value-⊑-pc (⊑-castr V⊑W A⊑c′) (V-raw v) (V-cast v′ _) =
  ⊑-castr (value-⊑-pc V⊑W (V-raw v) (V-raw v′)) A⊑c′
value-⊑-pc (⊑-castl V⊑W c⊑B) (V-cast v _) (V-raw w) =
  ⊑-castl (value-⊑-pc V⊑W (V-raw v) (V-raw w)) c⊑B
value-⊑-pc (⊑-cast V⊑W c⊑c′) (V-cast v _) (V-cast w _) =
  ⊑-cast (value-⊑-pc V⊑W (V-raw v) (V-raw w)) c⊑c′
value-⊑-pc (⊑-castl V⊑W c⊑B) (V-cast v _) (V-cast w i) =
  ⊑-castl (value-⊑-pc V⊑W (V-raw v) (V-cast w i)) c⊑B
value-⊑-pc (⊑-castr V⊑W A⊑c′) (V-cast v i) (V-cast w _) =
  ⊑-castr (value-⊑-pc V⊑W (V-cast v i) (V-raw w)) A⊑c′
value-⊑-pc V⊑W v V-● = contradiction V⊑W (_ ⋤●)
value-⊑-pc V⊑W V-● w = contradiction V⊑W (●⋤ _)

module Simulator.Experiment where

open import Data.Unit
open import Data.Nat
open import Data.List
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Maybe
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import Memory.Addr
open import CC.CCStatics

open import Simulator.AST
open import Simulator.CheckPrecision

M M′ : Term
-- M = (addr a⟦ high ⟧ 0 of low) ⟨ cast (Ref (` Bool of l high) of l low) (Ref (` Bool of ⋆) of ⋆) (pos 0) (~-ty ~⋆ (~-ref (~-ty ~⋆ ~-ι))) ⟩
-- M′ = ((addr a⟦ high ⟧ 0 of low) ⟨ cast (Ref (` Bool of l high) of l low) (Ref (` Bool of l high) of ⋆) (pos 0) (~-ty ~⋆ ~ᵣ-refl) ⟩)
--      ⟨ cast (Ref (` Bool of l high) of ⋆) (Ref (` Bool of l high) of l high) (pos 0) (~-ty ⋆~ ~ᵣ-refl) ⟩

-- ⊢M : [] ; ⟨ [] ,  ⟨ 0 , ` Bool ⟩ ∷ [] ⟩ ; l low ; low ⊢ M ⦂ Ref (` Bool of ⋆) of ⋆
-- ⊢M = ⊢cast (⊢addr refl)

-- ⊢M′ : [] ; ⟨ [] ,  ⟨ 0 , ` Bool ⟩ ∷ [] ⟩ ; l low ; low ⊢ M′ ⦂ Ref (` Bool of l high) of l high
-- ⊢M′ = ⊢cast (⊢cast (⊢addr refl))

-- result = check-⊑? (to-ast M ⊢M (Ref (` Bool of ⋆) of ⋆)) (to-ast M′ ⊢M′ (Ref (` Bool of l high) of l high))

M =
  `let (prot high ((addr a⟦ high ⟧ 0 of low) :=✓
                   ((($ false of low) ⟨ cast (` Bool of l low) (` Bool of ⋆) (pos 0) (~-ty ~⋆ ~-ι) ⟩)
                                      ⟨ cast (` Bool of ⋆) (` Bool of l high) (pos 0) (~-ty ⋆~ ~-ι) ⟩)))
  (! ((addr a⟦ high ⟧ 0 of low)
      ⟨ cast (Ref (` Bool of l high) of l low) (Ref (` Bool of ⋆) of ⋆) (pos 0) (~-ty ~⋆ (~-ref (~-ty ~⋆ ~-ι))) ⟩))
M′ =
  `let (prot high ((((addr a⟦ high ⟧ 0 of low)
                     ⟨ cast (Ref (` Bool of l high) of l low) (Ref (` Bool of l high) of ⋆) (pos 0) (~-ty ~⋆ ~ᵣ-refl) ⟩)
                     ⟨ cast (Ref (` Bool of l high) of ⋆) (Ref (` Bool of l high) of l high) (pos 0) (~-ty ⋆~ ~ᵣ-refl) ⟩) :=✓ ($ false of low)))
  (! ((addr a⟦ high ⟧ 0 of low) ⟨ cast (Ref (` Bool of l high) of l low) (Ref (` Bool of l high) of ⋆) (pos 0) (~-ty ~⋆ ~ᵣ-refl) ⟩))

⊢M : [] ; ⟨ [] ,  ⟨ 0 , ` Bool ⟩ ∷ [] ⟩ ; l low ; low ⊢ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢prot (⊢assign✓ (⊢sub (⊢addr refl) (<:-ty (<:-l l≼h) <:ᵣ-refl)) (⊢cast (⊢cast ⊢const)) h≼h)) (⊢deref (⊢cast (⊢addr refl)))

⊢M′ : [] ; ⟨ [] ,  ⟨ 0 , ` Bool ⟩ ∷ [] ⟩ ; l low ; low ⊢ M′ ⦂ ` Bool of ⋆
⊢M′ =
  ⊢let (⊢prot (⊢assign✓ (⊢cast (⊢cast (⊢addr refl))) (⊢sub ⊢const (<:-ty (<:-l l≼h) <:-ι)) h≼h))
  (⊢deref (⊢cast (⊢addr refl)))

result = check-⊑? (to-ast M ⊢M (` Bool of ⋆)) (to-ast M′ ⊢M′ (` Bool of ⋆))

module Simulator.Simulator where

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
open import Surface.SurfaceLang
open import Surface.Precision
open import CC.CCStatics renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ⟦_⟧_˙_of_ to lam⟦_⟧_˙_of_; !_ to *_)
open import CC.Compile renaming (compile to 𝒞; compilation-preserves-type to 𝒞-pres)
open import CC.Reduction
open import CC.TypeSafety
open import CC.BigStep
open import Memory.Heap CCTerm Value

open import Simulator.AST
open import Simulator.CheckPrecision


magic-num = 42

sim-helper : ∀ {Σ gc A} M μ
  → [] ; Σ ; gc ; low ⊢ M ⦂ A
  → Σ ⊢ μ → (t : AST) → (k : ℕ)
    ------------------------------------------
  → Maybe (∃[ N ] ∃[ μ′ ] (M ∣ μ ∣ low —↠ N ∣ μ′))
sim-helper M μ ⊢M ⊢μ t 0 =
  if (check-⊑? (to-ast M ⊢M) t) then just ⟨ M , μ , M ∣ μ ∣ _ ∎ ⟩ else nothing
sim-helper M μ ⊢M ⊢μ t (suc k-1) =
  if (check-⊑? (to-ast M ⊢M) t) then just ⟨ M , μ , M ∣ μ ∣ _ ∎ ⟩
    else
    (case progress low M ⊢M μ ⊢μ of λ where
      (step {N} {μ′} M→N) →
        let ⟨ Σ′ , Σ′⊇Σ , ⊢N , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (low≾ _) M→N in
        do
          ⟨ N′ , μ″ , N↠N′ ⟩ ← sim-helper N μ′ ⊢N ⊢μ′ t k-1
          just ⟨ N′ , μ″ , M ∣ _ ∣ _ —→⟨ M→N ⟩ N↠N′ ⟩
      (done v)      {- M is value already -} → nothing
      (err E-error) {- M is an error -}      → nothing)

{-
  𝒞M′ —→ N′
  ⊔|       ⊔|
  𝒞M  —↠ N
-}
simulator : ∀ {A A′} (M M′ : Term)
  → [] ; l low ⊢ᴳ M  ⦂ A
  → [] ; l low ⊢ᴳ M′ ⦂ A′
  → Maybe (∃[ N₁ ] ∃[ N₂ ] ∃[ μ ] (N₁ ∣ ∅ ∣ low —↠ N₂ ∣ μ))
simulator M M′ ⊢M ⊢M′ =
  let 𝒞M  = 𝒞 M ⊢M   ; ⊢𝒞M  = 𝒞-pres M ⊢M   in
  let 𝒞M′ = 𝒞 M′ ⊢M′ ; ⊢𝒞M′ = 𝒞-pres M′ ⊢M′ in
  -- make the more precise side step once
  case progress low 𝒞M′ ⊢𝒞M′ ∅ ⊢μ-nil of λ where
  (step {N′} {μ′} 𝒞M′→N′) →
    let ⟨ Σ′ , Σ′⊇Σ , ⊢N′ , ⊢μ′ ⟩ = preserve ⊢𝒞M′ ⊢μ-nil (low≾ _) 𝒞M′→N′ in
    do
      ⟨ N , μ , 𝒞M↠N ⟩ ← sim-helper 𝒞M ∅ ⊢𝒞M ⊢μ-nil (to-ast N′ ⊢N′) magic-num
      just ⟨ 𝒞M , N , μ , 𝒞M↠N ⟩
  _ → nothing

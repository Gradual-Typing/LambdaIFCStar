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
open import CC.MultiStep renaming (multi-trans to _↠_)
open import Memory.Heap CCTerm Value

open import Simulator.AST
open import Simulator.CheckPrecision


sim-helper : ∀ {Σ gc A} M μ
  → [] ; Σ ; gc ; low ⊢ M ⦂ A
  → Σ ⊢ μ → (t : AST) → (k : ℕ)
    ------------------------------------------
  → Maybe (ℕ × ∃[ N ] ∃[ μ′ ] (M ∣ μ ∣ low —↠ N ∣ μ′))
sim-helper M μ ⊢M ⊢μ t 0 =
  if (check-⊑? (to-ast M ⊢M _ <:-refl) t) then just ⟨ 0 , M , μ , M ∣ μ ∣ _ ∎ ⟩ else nothing
sim-helper M μ ⊢M ⊢μ t (suc k-1) =
  if (check-⊑? (to-ast M ⊢M _ <:-refl) t) then just ⟨ 0 , M , μ , M ∣ μ ∣ _ ∎ ⟩
    else
    (case progress low M ⊢M μ ⊢μ of λ where
      (step {N} {μ′} M→N) →
        let ⟨ Σ′ , Σ′⊇Σ , ⊢N , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (low≾ _) M→N in
        do
          ⟨ n , N′ , μ″ , N↠N′ ⟩ ← sim-helper N μ′ ⊢N ⊢μ′ t k-1
          just ⟨ 1 + n , N′ , μ″ , M ∣ _ ∣ _ —→⟨ M→N ⟩ N↠N′ ⟩
      (done v)      {- M is value already -} → nothing
      (err E-error) {- M is an error -}      → nothing)

{-
          M′
          ⊔|
  M —↠ₙ N
-}
step-left : ∀ {Σ Σ′ gc gc′ A A′} M M′ μ₁
  → (⊢M  : [] ; Σ  ; gc  ; low ⊢ M  ⦂ A)
  → (⊢M′ : [] ; Σ′ ; gc′ ; low ⊢ M′ ⦂ A′)
  → (⊢μ₁ : Σ ⊢ μ₁)
    ---------------------------------------------------
  → Maybe (ℕ × ∃[ N ] ∃[ μ₂ ] (M ∣ μ₁ ∣ low —↠ N ∣ μ₂))
step-left M M′ μ₁ ⊢M ⊢M′ ⊢μ₁ = sim-helper M μ₁ ⊢M ⊢μ₁ (to-ast M′ ⊢M′ _ <:-refl) magic-num

step-right : ∀ {Σ Σ′ gc gc′ A A′} M M′ μ₁ μ₁′
  → (⊢M  : [] ; Σ  ; gc  ; low ⊢ M  ⦂ A)
  → (⊢M′ : [] ; Σ′ ; gc′ ; low ⊢ M′ ⦂ A′)
  → (⊢μ₁  : Σ  ⊢ μ₁)
  → (⊢μ₁′ : Σ′ ⊢ μ₁′)
  → (k : ℕ)  -- gas: steps left for the right side
  → (n : ℕ)  -- steps taken on the left side
  → (n′ : ℕ) -- steps taken on the right side
    ------------------------------------------------------------
  → (ℕ × ∃[ N ]  ∃[ μ₂  ] (M  ∣ μ₁  ∣ low —↠ N  ∣ μ₂ )) ×
     (ℕ × ∃[ N′ ] ∃[ μ₂′ ] (M′ ∣ μ₁′ ∣ low —↠ N′ ∣ μ₂′)) ×
     (List (ℕ × ℕ))
step-right M M′ μ₁ μ₁′ ⊢M ⊢M′ ⊢μ ⊢μ₁′ 0 n n′ =
  -- we run out of gas and can't further proceed on the more precise side,
  -- - or either side
  ⟨ ⟨ 0 , M , μ₁ , _ ∣ _ ∣ _ ∎ ⟩ , ⟨ 0 , M′ , μ₁′ , _ ∣ _ ∣ _ ∎ ⟩ , [] ⟩
step-right M M′ μ₁ μ₁′ ⊢M ⊢M′ ⊢μ₁ ⊢μ₁′ (suc k-1) n₀ n₀′ =
  -- the more precise side (right) takes one step
  case progress low M′ ⊢M′ μ₁′ ⊢μ₁′ of λ where
  (step {N′} {μ₂′} M′→N′) →
    let ⟨ _ , _ , ⊢N′ , ⊢μ₂′ ⟩ = preserve ⊢M′ ⊢μ₁′ (low≾ _) M′→N′ in
    case step-left M N′ μ₁ ⊢M ⊢N′ ⊢μ₁ of λ where
    -- `step-left` recursively steps on the less precise side
    {-
      M′ —→  N′
      ⊔|       ⊔|
      M  —↠ₙ N
    -}
    (just ⟨ n , N , μ₂ , M↠N ⟩) →
      let ⟨ _ , _ , ⊢N , ⊢μ₂ ⟩ = multi-pres ⊢M ⊢μ₁ (low≾ _) M↠N in
      let ⟨ ⟨ n₁ , N₁ , μ₃ , N↠N₁ ⟩ ,
            ⟨ n₁′ , N₁′ , μ₃′ , N′↠N₁′ ⟩ ,
            s ⟩ = step-right N N′ μ₂ μ₂′ ⊢N ⊢N′ ⊢μ₂ ⊢μ₂′ k-1 (n + n₀) (1 + n₀′) in
      ⟨ ⟨ n + n₁ , N₁ , μ₃ , M↠N ↠ N↠N₁ ⟩ ,
        ⟨ 1 + n₁′ , N₁′ , μ₃′ , _ ∣ _ ∣ _ —→⟨ M′→N′ ⟩ N′↠N₁′ ⟩ ,
        ⟨ n + n₀ , 1 + n₀′ ⟩ ∷ s ⟩
    nothing →
      -- if we can't find N to stay in simulation
      -- we don't go anywhere else
      ⟨ ⟨ 0 , M , μ₁ , _ ∣ _ ∣ _ ∎ ⟩ ,
        ⟨ 1 , N′ , μ₂′ , _ ∣ _ ∣ _ —→⟨ M′→N′ ⟩ _ ∣ _ ∣ _ ∎ ⟩ ,
        [] ⟩
  _ → -- if M′ is a value or an error
    ⟨ ⟨ 0 , M , μ₁ , _ ∣ _ ∣ _ ∎ ⟩ ,
      ⟨ 0 , M′ , μ₁′ , _ ∣ _ ∣ _ ∎ ⟩ ,
      [] ⟩

simulator : ∀ {A A′} (M M′ : Term)
  → [] ; l low ⊢ᴳ M  ⦂ A
  → [] ; l low ⊢ᴳ M′ ⦂ A′
    -------------------------------------------------------------------
  → (ℕ × ∃[ N₁  ] ∃[ N₂  ] ∃[ μ  ] (N₁  ∣ ∅ ∣ low —↠ N₂  ∣ μ )) ×
     (ℕ × ∃[ N₁′ ] ∃[ N₂′ ] ∃[ μ′ ] (N₁′ ∣ ∅ ∣ low —↠ N₂′ ∣ μ′)) ×
     (List (ℕ × ℕ))
simulator M M′ ⊢M ⊢M′ =
  let N₁  = 𝒞 M ⊢M   ; ⊢N₁  = 𝒞-pres M ⊢M   in
  let N₁′ = 𝒞 M′ ⊢M′ ; ⊢N₁′ = 𝒞-pres M′ ⊢M′ in
  if check-⊑? (to-ast N₁ ⊢N₁ _ <:-refl) (to-ast N₁′ ⊢N₁′ _ <:-refl) then
    (let ⟨ ⟨ n , N₂ , μ , N₁↠N₂ ⟩ ,
           ⟨ n′ , N₂′ , μ′ , N₁′↠N₂′ ⟩ ,
           s ⟩ = step-right N₁ N₁′ ∅ ∅ ⊢N₁ ⊢N₁′ ⊢μ-nil ⊢μ-nil magic-num 0 0 in
     ⟨ ⟨ n , N₁ , N₂ , μ , N₁↠N₂ ⟩ , ⟨ n′ , N₁′ , N₂′ , μ′ , N₁′↠N₂′ ⟩ , ⟨ 0 , 0 ⟩ ∷ s ⟩)
    else ⟨ ⟨ 0 , N₁ , N₁ , ∅ , _ ∣ _ ∣ _ ∎ ⟩ , ⟨ 0 , N₁′ , N₁′ , ∅ , _ ∣ _ ∣ _ ∎ ⟩ , [] ⟩

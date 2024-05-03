module Surface2.GradualGuarantee where

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils

open import Surface2.Typing
open import Surface2.Precision

open import CC2.Statics
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision using (∅⊑∅)
open import CC2.GG using (gg)

open import Compile.Compile
open import Compile.Precision.CompilationPresPrecision


the-gradual-guarantee : ∀ {A A′ M M′ V′ μ′}
  → ⊢ M ⊑ᴳ M′
  → (⊢M  : [] ; l low ⊢ᴳ M  ⦂ A )
  → (⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ A′)
  → compile M′ ⊢M′ ∣ ∅ ∣ l low —↠ V′ ∣ μ′
  → Value V′
    ----------------------------------------------
  → ∃[ V ] ∃[ μ ] ∃[ Σ₂ ] ∃[ Σ₂′ ]
       (compile M ⊢M ∣ ∅ ∣ l low —↠ V ∣ μ) ×
       (Value V) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ A ⊑ A′)
the-gradual-guarantee M⊑M′ ⊢M ⊢M′ 𝒞M′↠V′ v′ =
  gg (compilation-preserves-precision M⊑M′ ⊢M ⊢M′) ⟨ ⊑-∅ , ⊑-∅ ⟩ ∅⊑∅ ⟨ refl , refl ⟩ 𝒞M′↠V′ v′

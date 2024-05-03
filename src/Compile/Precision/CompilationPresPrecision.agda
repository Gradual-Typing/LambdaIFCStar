module Compile.Precision.CompilationPresPrecision where

open import Data.List using ([])

open import Common.Utils
open import Common.Types
open import Surface2.Typing
open import Surface2.Precision
open import CC2.Precision

open import Compile.Compile
open import Compile.Precision.CompilePrecision using (compile-pres-precision)


{- Theorem: compilation preserves precision -}
compilation-preserves-precision : ∀ {M M′ A A′}
  → ⊢ M ⊑ᴳ M′
  → (⊢M  : [] ; l low ⊢ᴳ M  ⦂ A )
  → (⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ A′)
    --------------------------------------------------------------------------------------------
  → [] ; [] ∣ ∅ ; ∅ ∣ l low ; l low ∣ low ; low ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′
compilation-preserves-precision M⊑M′ ⊢M ⊢M′ = compile-pres-precision ⊑*-∅ l⊑l M⊑M′ ⊢M ⊢M′

module Proofs where

{- For CC, just sticky but non-coercive -}
open import CC.TypeSafety                 using (progress; preserve)
open import CC.BigStepPreservation        using (⇓-preserve)
open import CC.BigStepErasedDeterministic using (⇓ₑ-deterministic)
open import CC.Noninterference            using (noninterference)
open import CC.Compile                    using (compilation-preserves-type)

{- For CC2, both sticky and coercive -}
open import CC2.Progress                  using (progress)
open import CC2.Preservation              using (pres)
open import CC2.GradualGuarantee          using (gradual-guarantee)
open import CC2.Compile                   using (compilation-preserves-type)

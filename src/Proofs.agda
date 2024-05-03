module Proofs where

{- λSECc: a type-based cast calculus that is vigilant
          without type-guided classification -}
open import CC.TypeSafety                 using (progress; preserve)
open import CC.BigStepPreservation        using (⇓-preserve)
open import CC.BigStepErasedDeterministic using (⇓ₑ-deterministic)
open import CC.Noninterference            using (noninterference)
open import CC.Compile                    using (compilation-preserves-type)

{- λIFCc : a coercion-based cast calculus that is vigilant
           with type-guided classification -}
open import CC2.Progress                  using (progress)
open import CC2.Preservation              using (pres)
open import Compile.CompilationPresTypes  using (compilation-preserves-type)
open import Surface2.GradualGuarantee     using (the-gradual-guarantee)

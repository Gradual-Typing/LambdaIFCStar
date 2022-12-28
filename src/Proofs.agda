module Proofs where

open import CC.TypeSafety                 using (progress; preserve)
open import CC.BigStepPreservation        using (⇓-preserve)
open import CC.BigStepErasedDeterministic using (⇓ₑ-deterministic)
open import CC.Noninterference            using (noninterference)
open import CC.Compile                    using (compilation-preserves-type)

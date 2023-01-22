module PrettyPrinter.Console.MultiStep where

open import Agda.Builtin.String
open import Text.Printf
open import PrettyPrinter.Console.RedRules
open import PrettyPrinter.Console.CC


{- Pretty printing multi-step reduction -}
open import CC.MultiStep

pprint : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —↠ M′ ∣ μ′ → String
pprint (M ∣ μ ∣ pc ∎) =
  printf "%s\n  \ESC[90m∎\ESC[0m" (pprint-cc M)
pprint {L} {N} (L ∣ μ ∣ pc —→⟨ L→M ⟩ M↠N) =
  printf "%s\n  \ESC[90m↓ ⟨ %s ⟩\ESC[0m\n%s"
    (pprint-cc L) (print-red-rule L→M) (pprint M↠N)

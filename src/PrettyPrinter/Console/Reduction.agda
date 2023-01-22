module PrettyPrinter.Console.Reduction where

open import Agda.Builtin.String
open import Text.Printf
open import PrettyPrinter.Console.RedRules
open import PrettyPrinter.Console.CC


{- Pretty printing single-step reduction -}
open import CC.Reduction

pprint : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —→ M′ ∣ μ′ → String
pprint {M} {M′} M→M′ =
  printf "(%s —→⟨ %s ⟩ %s)" (pprint-cc M) (print-red-rule M→M′) (pprint-cc M′)

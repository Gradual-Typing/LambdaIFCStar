module PrettyPrinter.GraphViz.MultiStep where

open import Data.Nat
open import Agda.Builtin.String
open import Text.Printf
open import PrettyPrinter.GraphViz.RedRules
open import PrettyPrinter.GraphViz.CC


{- Pretty printing multi-step reduction -}
open import CC.MultiStep

pprint-multi : ∀ {M₁ M₂ μ₁ μ₂ pc}
  → (prefix : String) → M₁ ∣ μ₁ ∣ pc —↠ M₂ ∣ μ₂ → ℕ → String
pprint-multi prefix (M ∣ μ ∣ pc ∎) n = printf "    %s%u [texlbl=\"$\\begin{aligned}&%s\\end{aligned}$\"];\n" prefix n (pprint-cc M)
pprint-multi prefix (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠) n =
  primStringAppend
    (printf "    %s%u -> %s%u [texlbl=\"%s\"];\n" prefix n prefix (suc n) (print-red-rule M₁→M₂))
    (primStringAppend
     (printf "    %s%u [texlbl=\"$\\begin{aligned}&%s\\end{aligned}$\"];\n" prefix n (pprint-cc M₁))
     (pprint-multi prefix M₂↠ (suc n)))

pprint : ∀ {M₁ M₂ μ₁ μ₂ pc}
  → (prefix : String) → M₁ ∣ μ₁ ∣ pc —↠ M₂ ∣ μ₂ → String
pprint prefix M₁↠M₂ = pprint-multi prefix M₁↠M₂ 0

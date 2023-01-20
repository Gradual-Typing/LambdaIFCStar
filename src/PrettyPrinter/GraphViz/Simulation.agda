module PrettyPrinter.GraphViz.Simulation where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.String
open import Text.Printf

open import Common.Types
open import CC.MultiStep
open import PrettyPrinter.GraphViz.MultiStep renaming (pprint to pprint-↠)

print-sim-diagram : ∀ {M₁ M₁′ M₂ M₂′ μ₁ μ₁′ μ₂ μ₂′}
  → M₁ ∣ μ₁ ∣ low —↠ M₂ ∣ μ₂
  → M₁′ ∣ μ₁′ ∣ low —↠ M₂′ ∣ μ₂′
  → (List (ℕ × ℕ))
  → String
print-sim-diagram M₁↠M₂ M₁′↠M₂′ s =
  printf
  "digraph {
  node[shape=plaintext];
  subgraph left {
    rankdir=\"TB\";
%s
  }
  subgraph right {
    rankdir=\"TB\";
%s
  }
  edge[style=dotted, constraint=false, arrowhead=none, minlen=3];
}\n" (pprint-↠ "left" M₁↠M₂) (pprint-↠ "right" M₁′↠M₂′)

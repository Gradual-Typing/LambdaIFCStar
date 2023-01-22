module PrettyPrinter.GraphViz.Simulation where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.String
open import Text.Printf

open import Common.Types
open import CC.MultiStep
open import PrettyPrinter.GraphViz.MultiStep renaming (pprint to pprint-↠)


print-sim-edges : List (ℕ × ℕ) → String
print-sim-edges [] = ""
print-sim-edges (⟨ n , m ⟩ ∷ rest) =
  let l_node = printf "left%u"  n
      r_node = printf "right%u" m in
  primStringAppend
  (printf "%s -> %s; { rank=\"same\"; %s; %s; }\n"
         l_node r_node l_node r_node)
  (print-sim-edges rest)

print-sim-diagram : ∀ {M₁ M₁′ M₂ M₂′ μ₁ μ₁′ μ₂ μ₂′}
  → M₁  ∣ μ₁  ∣ low —↠ M₂  ∣ μ₂   {- reduction seq on the left   -}
  → M₁′ ∣ μ₁′ ∣ low —↠ M₂′ ∣ μ₂′  {- reduction seq on the right  -}
  → List (ℕ × ℕ)                    {- edges between two subgraphs -}
    ---------------
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

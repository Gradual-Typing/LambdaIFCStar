module PrettyPrinter.GraphViz.Simulation where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable using (isYes)
open import Agda.Builtin.String
open import Text.Printf

open import Common.Utils using (magic-num)
open import Common.Types
open import CC.MultiStep
open import PrettyPrinter.GraphViz.MultiStep renaming (pprint to pprint-↠)


print-sim-edges : List (ℕ × ℕ) → (last-n : ℕ) → String
print-sim-edges [] last = ""
print-sim-edges (⟨ n , m ⟩ ∷ rest) last =
  let l_node = printf "left%u"  n
      r_node = printf "right%u" m in
  primStringAppend
  (if isYes (n ≟ last)
    then (printf "  %s -> %s;\n" l_node r_node)
    else (printf "  %s -> %s; { rank=\"same\"; %s; %s; }\n" l_node r_node l_node r_node))
  (print-sim-edges rest n)

print-sim-diagram : ∀ {M₁ M₁′ M₂ M₂′ μ₁ μ₁′ μ₂ μ₂′}
  → M₁  ∣ μ₁  ∣ low —↠ M₂  ∣ μ₂   {- reduction seq on the left   -}
  → M₁′ ∣ μ₁′ ∣ low —↠ M₂′ ∣ μ₂′  {- reduction seq on the right  -}
  → List (ℕ × ℕ)                    {- edges between two subgraphs -}
    ---------------
  → String
print-sim-diagram M₁↠M₂ M₁′↠M₂′ s =
  printf
  -- NOTE: use the `splines` option to draw straight lines
  -- - see https://graphviz.org/docs/attrs/splines/
  "digraph {
  splines=line;
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
%s
}\n" (pprint-↠ "left" M₁↠M₂) (pprint-↠ "right" M₁′↠M₂′) (print-sim-edges s magic-num)

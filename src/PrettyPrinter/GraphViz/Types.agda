module PrettyPrinter.GraphViz.Types where

open import Agda.Builtin.String
open import Text.Printf


{- Pretty printing types -}
open import Common.Types

pprint-label : Label → String
pprint-label ⋆        = printf "⋆"
pprint-label (l low)  = printf "L"
pprint-label (l high) = printf "H"

pprint-raw-type : RawType → String
pprint-type : Type → String

pprint-raw-type (` Bool) = "𝔹"
pprint-raw-type (` Unit) = "⊤"
pprint-raw-type (Ref A)  = printf "Ref (%s)" (pprint-type A)
pprint-raw-type (⟦ gc ⟧ A ⇒ B) =
  printf "⟦%s⟧ (%s) ⇒ (%s)" (pprint-label gc) (pprint-type A) (pprint-type B)

pprint-type (T of g) = printf "%s of %s" (pprint-raw-type T) (pprint-label g)

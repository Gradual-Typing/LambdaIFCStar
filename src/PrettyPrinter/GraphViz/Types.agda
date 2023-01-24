module PrettyPrinter.GraphViz.Types where

open import Agda.Builtin.String
open import Text.Printf


{- Pretty printing types -}
open import Common.Types

pprint-label : Label → String
pprint-label ⋆        = printf "\\unk"
pprint-label (l low)  = printf "\\low"
pprint-label (l high) = printf "\\high"

pprint-raw-type : RawType → String
pprint-type : Type → String

pprint-raw-type (` Bool) = "\\Bool"
pprint-raw-type (` Unit) = "\\Unit"
pprint-raw-type (Ref A)  = printf "(\\Refer{%s})" (pprint-type A)
pprint-raw-type (⟦ gc ⟧ A ⇒ B) =
  printf "(\\Fun{%s}{%s}{%s})" (pprint-type A) (pprint-label gc) (pprint-type B)

pprint-type (T of g) = printf "%s_{%s}" (pprint-raw-type T) (pprint-label g)

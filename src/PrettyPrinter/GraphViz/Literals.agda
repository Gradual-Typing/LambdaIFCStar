module PrettyPrinter.GraphViz.Literals where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Agda.Builtin.String
open import Text.Printf

open import Common.Types


pprint-const : ∀ {ι} (k : rep ι) → String
pprint-const {Bool} true  = "\\true"
pprint-const {Bool} false = "\\false"
pprint-const {Unit} tt    = "\\unit"

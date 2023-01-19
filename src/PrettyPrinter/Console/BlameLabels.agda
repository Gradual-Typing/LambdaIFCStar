module PrettyPrinter.Console.BlameLabels where

open import Agda.Builtin.String
open import Text.Printf


{- Pretty printing blame labels -}
open import Common.BlameLabels

pprint-blame-label : BlameLabel → String
pprint-blame-label (pos x) = printf "\ESC[90m@%u\ESC[0m" x
pprint-blame-label (neg x) = printf "\ESC[90m@%u\ESC[0m" x

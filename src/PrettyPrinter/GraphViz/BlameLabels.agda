module PrettyPrinter.GraphViz.BlameLabels where

open import Agda.Builtin.String
open import Text.Printf


{- Pretty printing blame labels -}
open import Common.BlameLabels

pprint-blame-label : BlameLabel → String
pprint-blame-label (pos x) = printf "%u" x
pprint-blame-label (neg x) = printf "%u" x

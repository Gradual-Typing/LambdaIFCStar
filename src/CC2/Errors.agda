{- Runtime errors -}

module CC2.Errors where

open import Common.BlameLabels

data Error : Set where
  cast-error : Error    {- casts on values -}
  nsu-error  : Error    {- NSU checks      -}

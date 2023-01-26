{- Runtime errors -}

module CC.Errors where

open import Common.BlameLabels

data Error : Set where
  blame      : BlameLabel → Error
  nsu-error  : Error

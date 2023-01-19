module PrettyPrinter.Console.Surface where

open import Agda.Builtin.String
open import Text.Printf
open import Common.Types
open import PrettyPrinter.Literals
open import PrettyPrinter.Console.Types
open import PrettyPrinter.Console.BlameLabels


{- Pretty printing the surface language -}
open import Surface.SurfaceLang

pprint-term : Term → String
pprint-term (` x)      = printf "\ESC[4m%u\ESC[0m" x
pprint-term ($ k of ℓ) = printf "%s of %s" (pprint-const k) (pprint-label (l ℓ))
pprint-term (ƛ⟦ pc ⟧ A ˙ N of ℓ) =
  printf "λ⟦%s⟧ %s. %s of %s" (pprint-label (l pc)) (pprint-type A) (pprint-term N) (pprint-label (l ℓ))
pprint-term (L · M at p) =
  printf "(%s) (%s) %s" (pprint-term L) (pprint-term M) (pprint-blame-label p)
pprint-term (if L then M else N at p) =
  printf "\ESC[1mif\ESC[0m (%s) \ESC[1mthen\ESC[0m (%s) \ESC[1melse\ESC[0m (%s) %s"
    (pprint-term L) (pprint-term M) (pprint-term N) (pprint-blame-label p)
pprint-term (M ∶ A at p) =
  printf "(%s) \ESC[1m:\ESC[0m %s %s" (pprint-term M) (pprint-type A) (pprint-blame-label p)
pprint-term (`let M `in N) =
  printf "\ESC[1mlet\ESC[0m %s \ESC[1min\ESC[0m\n%s" (pprint-term M) (pprint-term N)
pprint-term (ref⟦ ℓ ⟧ M at p) =
  printf "\ESC[1mref\ESC[0m %s (%s) %s" (pprint-label (l ℓ)) (pprint-term M) (pprint-blame-label p)
pprint-term (! M) = printf "\ESC[1m!\ESC[0m (%s)" (pprint-term M)
pprint-term (L := M at p) =
  printf "(%s) \ESC[1m:=\ESC[0m (%s) %s" (pprint-term L) (pprint-term M) (pprint-blame-label p)

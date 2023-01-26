module PrettyPrinter.GraphViz.CC where

open import Agda.Builtin.String
open import Text.Printf
open import Common.Types
open import PrettyPrinter.GraphViz.Literals
open import PrettyPrinter.GraphViz.Types
open import PrettyPrinter.GraphViz.BlameLabels


{- Pretty printing the cast calculus -}
open import CC.CCStatics renaming (Term to CCTerm)
open import Memory.Heap CCTerm Value

pprint-addr : Addr → String
pprint-addr (a⟦ ℓ̂ ⟧ n) = printf "%u_{%s}" n (pprint-label (l ℓ̂))

pprint-cast : ∀ {A B} → Cast A ⇒ B → String
pprint-cast (cast A B p A~B) =
  printf "\\Cast{%s}{%s}{%s}" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.CCStatics.Error → String
pprint-error (blame p) = printf "\\blame{%s}" (pprint-blame-label p)
pprint-error nsu-error = "\\key{nsu{-}error}"

pprint-cc : CCTerm → String
pprint-cc (` x) = printf "\\ccvar{%u}" x
pprint-cc (addr a of ℓ) = printf "\\ccaddr{%s}{%s}" (pprint-addr a) (pprint-label (l ℓ))
pprint-cc ($ k of ℓ) = printf "\\ccconst{%s}{%s}" (pprint-const k) (pprint-label (l ℓ))
pprint-cc (ƛ⟦ pc ⟧ A ˙ N of ℓ) =
  printf "\\cclam{%s}{%s}{%s}{%s}" (pprint-label (l pc)) (pprint-type A) (pprint-cc N) (pprint-label (l ℓ))
pprint-cc (L · M) =
  printf "(%s)\\;(%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (if L A M N) =
  -- not sure if it's a good idea to hard-code those parentheses
  printf "\\ccif{(%s)}{}{(%s)}{(%s)}" (pprint-cc L) (pprint-cc M) (pprint-cc N)
pprint-cc (`let M N) =
  -- always generate one line break here; good enough for now
  printf "\\cclet{%s}{} \\\\ &%s" (pprint-cc M) (pprint-cc N)
pprint-cc (ref⟦ ℓ ⟧ M) =
  printf "\\ccref{}{%s}{(%s)}" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref?⟦ ℓ ⟧ M) =
  printf "\\ccref{?}{%s}{(%s)}" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref✓⟦ ℓ ⟧ M) =
  printf "\\ccref{\\checkmark}{%s}{(%s)}" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (! M) = printf "\\ccderef{(%s)}" (pprint-cc M)
pprint-cc (L := M)   = printf "\\ccassign{(%s)}{}{(%s)}" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=? M)  = printf "\\ccassign{(%s)}{?}{(%s)}" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=✓ M) = printf "\\ccassign{(%s)}{\\checkmark}{(%s)}" (pprint-cc L) (pprint-cc M)
pprint-cc (prot ℓ M) = printf "\\ccprot{%s}{(%s)}" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (M ⟨ c ⟩)  = printf "\\cccast{(%s)}{%s}" (pprint-cc M) (pprint-cast c)
pprint-cc (cast-pc g M) = printf "\\cccastpc{%s}{(%s)}" (pprint-label g) (pprint-cc M)
pprint-cc (error e) = printf "\\ccerr{%s}" (pprint-error e)
-- should never encounter this
pprint-cc ● = ""

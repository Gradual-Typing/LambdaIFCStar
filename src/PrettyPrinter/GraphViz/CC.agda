module PrettyPrinter.GraphViz.CC where

open import Agda.Builtin.String
open import Text.Printf
open import Common.Types
open import PrettyPrinter.Literals
open import PrettyPrinter.GraphViz.Types
open import PrettyPrinter.GraphViz.BlameLabels


{- Pretty printing the cast calculus -}
open import CC.CCStatics renaming (Term to CCTerm)
open import Memory.Heap CCTerm Value

pprint-addr : Addr → String
pprint-addr (a⟦ ℓ̂ ⟧ n) = printf "⟦%s⟧ %u" (pprint-label (l ℓ̂)) n

pprint-cast : ∀ {A B} → Cast A ⇒ B → String
pprint-cast (cast A B p A~B) =
  printf "%s ⇒ %s %s" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.CCStatics.Error → String
pprint-error (blame p) = printf "blame %s" (pprint-blame-label p)
pprint-error nsu-error = "nsu-error"

pprint-cc : CCTerm → String
pprint-cc (` x) = printf "%u" x
pprint-cc (addr a of ℓ) = printf "%s of %s" (pprint-addr a) (pprint-label (l ℓ))
pprint-cc ($ k of ℓ) = printf "%s of %s" (pprint-const k) (pprint-label (l ℓ))
pprint-cc (ƛ⟦ pc ⟧ A ˙ N of ℓ) =
  printf "λ⟦%s⟧ %s. %s of %s" (pprint-label (l pc)) (pprint-type A) (pprint-cc N) (pprint-label (l ℓ))
pprint-cc (L · M) =
  printf "(%s) (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (if L A M N) =
  printf "if (%s) then (%s) else (%s)" (pprint-cc L) (pprint-cc M) (pprint-cc N)
pprint-cc (`let M N) =
  printf "let %s in<br/>%s" (pprint-cc M) (pprint-cc N)
pprint-cc (ref⟦ ℓ ⟧ M) =
  printf "ref %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref?⟦ ℓ ⟧ M) =
  printf "ref? %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref✓⟦ ℓ ⟧ M) =
  printf "ref✓ %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (! M) = printf "! (%s)" (pprint-cc M)
pprint-cc (L := M)   = printf "(%s) := (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=? M)  = printf "(%s) :=? (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=✓ M) = printf "(%s) :=✓ (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (prot ℓ M) = printf "prot %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (M ⟨ c ⟩)  = printf "(%s) ⟨ %s ⟩" (pprint-cc M) (pprint-cast c)
pprint-cc (cast-pc g M) = printf "cast-pc %s (%s)" (pprint-label g) (pprint-cc M)
pprint-cc (error e) = printf "error %s" (pprint-error e)
pprint-cc ● = "●"

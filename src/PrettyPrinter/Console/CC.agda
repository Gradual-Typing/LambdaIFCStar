module PrettyPrinter.Console.CC where

open import Agda.Builtin.String
open import Text.Printf
open import Common.Types
open import PrettyPrinter.Console.Literals
open import PrettyPrinter.Console.Types
open import PrettyPrinter.Console.BlameLabels


{- Pretty printing the cast calculus -}
open import CC.CCStatics renaming (Term to CCTerm)
open import Memory.Heap CCTerm Value

pprint-addr : Addr → String
pprint-addr (a⟦ ℓ̂ ⟧ n) = printf "⟦%s⟧ \ESC[7m%u\ESC[0m" (pprint-label (l ℓ̂)) n

pprint-cast : ∀ {A B} → Cast A ⇒ B → String
pprint-cast (cast A B p A~B) = printf "%s ⇒ %s %s" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.CCStatics.Error → String
pprint-error (blame p) = printf "\ESC[93mblame\ESC[0m %s" (pprint-blame-label p)
pprint-error nsu-error = "\ESC[93mnsu-error\ESC[0m"

pprint-cc : CCTerm → String
pprint-cc (` x) = printf "\ESC[4m%u\ESC[0m" x
pprint-cc (addr a of ℓ) = printf "%s of %s" (pprint-addr a) (pprint-label (l ℓ))
pprint-cc ($ k of ℓ) = printf "%s of %s" (pprint-const k) (pprint-label (l ℓ))
pprint-cc (ƛ⟦ pc ⟧ A ˙ N of ℓ) =
  printf "λ⟦%s⟧ %s. %s of %s" (pprint-label (l pc)) (pprint-type A) (pprint-cc N) (pprint-label (l ℓ))
pprint-cc (L · M) =
  printf "(%s) (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (if L A M N) =
  printf "\ESC[1mif\ESC[0m (%s) \ESC[1mthen\ESC[0m (%s) \ESC[1melse\ESC[0m (%s)"
    (pprint-cc L) (pprint-cc M) (pprint-cc N)
pprint-cc (`let M N) =
  printf "\ESC[1mlet\ESC[0m %s \ESC[1min\ESC[0m\n%s" (pprint-cc M) (pprint-cc N)
pprint-cc (ref⟦ ℓ ⟧ M) =
  printf "\ESC[1mref\ESC[0m %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref?⟦ ℓ ⟧ M) =
  printf "\ESC[1mref?\ESC[0m %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (ref✓⟦ ℓ ⟧ M) =
  printf "\ESC[1mref✓\ESC[0m %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (! M) =
 printf "\ESC[1m!\ESC[0m (%s)" (pprint-cc M)
pprint-cc (L := M) =
  printf "(%s) \ESC[1m:=\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=? M) =
  printf "(%s) \ESC[1m:=?\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=✓ M) =
  printf "(%s) \ESC[1m:=✓\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (prot ℓ M) =
  printf "\ESC[1mprot\ESC[0m %s (%s)" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (M ⟨ c ⟩) =
  printf "(%s) \ESC[1m⟨\ESC[0m %s \ESC[1m⟩\ESC[0m" (pprint-cc M) (pprint-cast c)
pprint-cc (cast-pc g M) =
  printf "\ESC[1mcast-pc\ESC[0m %s (%s)" (pprint-label g) (pprint-cc M)
pprint-cc (error e) =
  printf "\ESC[1merror\ESC[0m %s" (pprint-error e)
pprint-cc ● = "●"

module PrettyPrint where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Agda.Builtin.String
open import Text.Printf

{- Pretty printing types -}
open import Types
open import BlameLabels

pprint-label : Label → String
pprint-label ⋆ = printf "\ESC[35m%s\ESC[0m" "⋆"
pprint-label (l low) = printf "\ESC[32m%s\ESC[0m" "L"
pprint-label (l high) = printf "\ESC[31m%s\ESC[0m" "H"

pprint-blame-label : BlameLabel → String
pprint-blame-label (pos x) = printf "\ESC[90m@%u\ESC[0m" x
pprint-blame-label (neg x) = printf "\ESC[90m@%u\ESC[0m" x

pprint-raw-type : RawType → String
pprint-type : Type → String

pprint-raw-type (` Bool) = "𝔹"
pprint-raw-type (` Unit) = "⊤"
pprint-raw-type (Ref A) = printf "Ref (%s)" (pprint-type A)
pprint-raw-type (⟦ gc ⟧ A ⇒ B) = printf "⟦%s⟧ (%s) ⇒ (%s)" (pprint-label gc) (pprint-type A) (pprint-type B)

pprint-type (T of g) = printf "%s of %s" (pprint-raw-type T) (pprint-label g)

{- Pretty printing the surface language -}
open import SurfaceLang

pprint-const : ∀ {ι} (k : rep ι) → String
pprint-const {Bool} true  = "true"
pprint-const {Bool} false = "false"
pprint-const {Unit} tt    = "()"

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

open import CC renaming (Term to CCTerm)
open import Heap
open import TypeBasedCast

pprint-addr : Addr → String
pprint-addr (a⟦ ℓ̂ ⟧ n) = printf "\ESC[7m⟦%s⟧ %u\ESC[0m" (pprint-label (l ℓ̂)) n

pprint-cast : ∀ {A B} → Cast A ⇒ B → String
pprint-cast (cast A B p A~B) = printf "%s ⇒ %s %s" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.Error → String
pprint-error (blame p) = printf "\ESC[93mblame\ESC[0m %s" (pprint-blame-label p)
pprint-error nsu-error = printf "\ESC[93mnsu-error\ESC[0m"

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
  printf "\ESC[1mprot\ESC[0m %s %s" (pprint-label (l ℓ)) (pprint-cc M)
pprint-cc (M ⟨ c ⟩) =
  printf "%s \ESC[1m⟨\ESC[0m %s \ESC[1m⟩\ESC[0m" (pprint-cc M) (pprint-cast c)
pprint-cc (cast-pc g M) =
  printf "\ESC[1mcast-pc\ESC[0m %s %s" (pprint-label g) (pprint-cc M)
pprint-cc (error e) =
  printf "\ESC[1merror\ESC[0m %s" (pprint-error e)
pprint-cc ● = printf "●"

-- private
--   print-rd-rule : ∀ {M N} → M —→ N → String
--   print-rd-rule (ξ₁ _)   = "ξ₁"
--   print-rd-rule (ξ₂ _ _) = "ξ₂"
--   print-rd-rule (β _)    = "β"

-- pprint-reduction : ∀ {M N} → M —→ N → String
-- pprint-reduction {M} {N} M→N =
--   printf "(%s —→⟨ %s ⟩ %s)" (pprint-term M) (print-rd-rule M→N) (pprint-term N)

-- pprint-mult-reduction : ∀ {M N} → M —↠ N → String
-- pprint-mult-reduction {M} {M} (_ ∎) = printf "%s\n  ∎" (pprint-term M)
-- pprint-mult-reduction {L} {N} (L —→⟨ L→M ⟩ M↠N) =
--   printf "%s\n  ↓ ⟨ %s ⟩\n%s"
--     (pprint-term L) (print-rd-rule L→M) (pprint-mult-reduction M↠N)

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

{- Pretty printing the cast calculus -}
open import CC renaming (Term to CCTerm)
open import Heap
open import TypeBasedCast

pprint-addr : Addr → String
pprint-addr (a⟦ ℓ̂ ⟧ n) = printf "\ESC[7m⟦%s⟧ %u\ESC[0m" (pprint-label (l ℓ̂)) n

pprint-cast : ∀ {A B} → Cast A ⇒ B → String
pprint-cast (cast A B p A~B) = printf "%s ⇒ %s %s" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.Error → String
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


{- Pretty printing single and multi step reductions -}
open import Reduction

print-red-rule : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —→ M′ ∣ μ′ → String
print-red-rule (ξ M→M′)           = printf "ξ(%s)" (print-red-rule M→M′)
print-red-rule ξ-err               = "ξ-err"
print-red-rule (prot-val _)        = "prot-val"
print-red-rule (prot-ctx M→M′)    = printf "prot-ctx(%s)" (print-red-rule M→M′)
print-red-rule prot-err            = "prot-err"
print-red-rule (β _)               = "β"
print-red-rule β-if-true           = "β-if-true"
print-red-rule β-if-false          = "β-if-false"
print-red-rule (β-let _)           = "β-let"
print-red-rule ref-static          = "ref-static"
print-red-rule (ref?-ok _)         = "ref?-ok"
print-red-rule (ref?-fail _)       = "ref?-fail"
print-red-rule (ref _ _)           = "ref"
print-red-rule (deref _)           = "deref"
print-red-rule assign-static       = "assign-static"
print-red-rule (assign?-ok _)      = "assign?-ok"
print-red-rule (assign?-fail _)    = "assign?-fail"
print-red-rule (assign _)          = "assign"
print-red-rule (cast _ _ _)        = "cast"
print-red-rule (if-cast-true _)    = "if-cast-true"
print-red-rule (if-cast-false _)   = "if-cast-false"
print-red-rule (fun-cast _ _ _)    = "fun-cast"
print-red-rule (deref-cast _ _)    = "deref-cast"
print-red-rule (assign?-cast _ _)  = "assign?-cast"
print-red-rule (assign-cast _ _ _) = "assign-cast"
print-red-rule (β-cast-pc _)       = "β-cast-pc"

pprint-reduction : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —→ M′ ∣ μ′ → String
pprint-reduction {M} {M′} M→M′ =
  printf "(%s —→⟨ %s ⟩ %s)" (pprint-cc M) (print-red-rule M→M′) (pprint-cc M′)

pprint-mult-reduction : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —↠ M′ ∣ μ′ → String
pprint-mult-reduction (M ∣ μ ∣ pc ∎) = printf "%s\n  ∎" (pprint-cc M)
pprint-mult-reduction {L} {N} (L ∣ μ ∣ pc —→⟨ L→M ⟩ M↠N) =
  printf "%s\n  ↓ ⟨ %s ⟩\n%s"
    (pprint-cc L) (print-red-rule L→M) (pprint-mult-reduction M↠N)

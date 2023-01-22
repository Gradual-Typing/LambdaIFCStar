module PrettyPrinter.Console.RedRules where

open import Agda.Builtin.String
open import Text.Printf

open import CC.Reduction


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

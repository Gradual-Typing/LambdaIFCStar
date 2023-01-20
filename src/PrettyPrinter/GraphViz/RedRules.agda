module PrettyPrinter.GraphViz.RedRules where

open import Agda.Builtin.String
open import Text.Printf

open import CC.Reduction


print-red-rule : ∀ {M M′ μ μ′ pc} → M ∣ μ ∣ pc —→ M′ ∣ μ′ → String
print-red-rule (ξ M→M′)           = printf "$\\xi$(%s)" (print-red-rule M→M′)
print-red-rule ξ-err               = "$\\xi$\\textit{-err}"
print-red-rule (prot-val _)        = "\\textit{prot-val}"
print-red-rule (prot-ctx M→M′)    = printf "\\textit{prot-ctx}(%s)" (print-red-rule M→M′)
print-red-rule prot-err            = "prot-err"
print-red-rule (β _)               = "$\\beta$"
print-red-rule β-if-true           = "$\\beta$\\textit{-if-true}"
print-red-rule β-if-false          = "β-if-false"
print-red-rule (β-let _)           = "$\\beta$\\textit{-let}"
print-red-rule ref-static          = "\\textit{ref-static}"
print-red-rule (ref?-ok _)         = "\\textit{ref?-ok}"
print-red-rule (ref?-fail _)       = "\\textit{ref?-fail}"
print-red-rule (ref _ _)           = "\\textit{ref}"
print-red-rule (deref _)           = "\\textit{deref}"
print-red-rule assign-static       = "\\textit{assign-static}"
print-red-rule (assign?-ok _)      = "\\textit{assign?-ok}"
print-red-rule (assign?-fail _)    = "\\textit{assign?-fail}"
print-red-rule (assign _)          = "\\textit{assign}"
print-red-rule (cast _ _ _)        = "\\textit{cast}"
print-red-rule (if-cast-true _)    = "\\textit{if-cast-true}"
print-red-rule (if-cast-false _)   = "\\textit{if-cast-false}"
print-red-rule (fun-cast _ _ _)    = "\\textit{fun-cast}"
print-red-rule (deref-cast _ _)    = "\\textit{deref-cast}"
print-red-rule (assign?-cast _ _)  = "\\textit{assign?-cast}"
print-red-rule (assign-cast _ _ _) = "\\textit{assign-cast}"
print-red-rule (β-cast-pc _)       = "$\\beta$\\textit{-cast-pc}"

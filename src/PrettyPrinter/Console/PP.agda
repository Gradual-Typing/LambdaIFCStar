module PrettyPrinter.Console.PP where

open import PrettyPrinter.Console.BlameLabels    public
open import PrettyPrinter.Console.Types          public
open import PrettyPrinter.Console.Surface        public
open import PrettyPrinter.Console.CC             public
open import PrettyPrinter.Console.Reduction
    renaming (pprint to pprint-→)               public
open import PrettyPrinter.Console.MultiStep
    renaming (pprint to pprint-↠)               public

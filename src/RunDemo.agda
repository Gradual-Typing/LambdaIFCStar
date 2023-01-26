{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.String
open import Text.Printf
open import IO

open import Common.Utils
open import Common.Types
open import Surface.SurfaceLang
open import CC.CCStatics renaming (Term to CCTerm)
open import CC.HeapTyping
open import CC.Interp

open import ExamplePrograms.Demo.Examples
open import PrettyPrinter.Console.PP


main =
  run {Agda.Primitive.lzero}
    (do
      (putStrLn (foldr run-cfg "" cfgs))
      (putStrLn "\ESC[101mEND\ESC[0m"))
  where
  run-cfg : Cfg → String → String
  run-cfg ⟨ M , 𝒞M , _ , ⊢𝒞M ⟩ rest =
    (printf "%s\n\n%s\n%s"
      (printf "\ESC[7m**** Running λSEC* program: ****\ESC[0m\n%s" (pprint-term M))
      (printf "\ESC[7m**** Reduction of the compiled λSEC⇒ term: ****\ESC[0m\n%s\n"
        (let ⟨ _ , _ , R ⟩ = interp 𝒞M ⊢𝒞M 42 in pprint-↠ R))
      rest)

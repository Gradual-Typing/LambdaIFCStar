{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.String
open import Text.Printf
open import IO

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

open import ExamplePrograms.Simulation.Examples
open import Simulator.Simulator
open import PrettyPrinter.GraphViz.Simulation


dir = "plot/"

main = run {Agda.Primitive.lzero} (foldr run-cfg (return tt) cfgs)
  where
  run-cfg : Cfg → IO ⊤ → IO ⊤
  run-cfg ⟨ name , M , M′ , _ , _ , ⊢M , ⊢M′ ⟩ rest =
    do
    (putStrLn (primStringAppend "Running example: " name))
    (let ⟨ ⟨ n , _ , _ , _ , N₁↠N₂ ⟩ ,
           ⟨ m , _ , _ , _ , N₁′↠N₂′ ⟩ ,
           edges ⟩ = simulator M M′ ⊢M ⊢M′ in
     let output-file = primStringAppend dir (primStringAppend name ".dot") in
       writeFile output-file (print-sim-diagram N₁↠N₂ N₁′↠N₂′ edges))
    rest

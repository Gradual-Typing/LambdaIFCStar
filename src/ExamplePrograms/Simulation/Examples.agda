module ExamplePrograms.Simulation.Examples where

open import Data.List
open import Data.Product using (_×_; ∃-syntax; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

open import Agda.Builtin.String
open import Common.Utils
open import Common.Types
open import Surface.SurfaceLang
open import ExamplePrograms.Simulation.SubInj as SubInj

Cfg = String ×
  ∃[ M ] ∃[ M′ ] ∃[ A ] ∃[ A′ ]
  ([] ; l low ⊢ᴳ M ⦂ A) × ([] ; l low ⊢ᴳ M′ ⦂ A′)

cfgs : List Cfg
cfgs = [
    ⟨ "SubInj" , SubInj.M , SubInj.M′ , _ , _ , SubInj.⊢M , SubInj.⊢M′ ⟩
  ]

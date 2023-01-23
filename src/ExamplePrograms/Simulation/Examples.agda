module ExamplePrograms.Simulation.Examples where

open import Data.List
open import Data.Product using (_×_; ∃-syntax; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

open import Common.Utils
open import Common.Types
open import Surface.SurfaceLang
open import ExamplePrograms.Simulation.SubInj as SubInj

cfgs : List (∃[ M ] ∃[ M′ ] ∃[ A ] ∃[ A′ ]
             ([] ; l low ⊢ᴳ M ⦂ A) × ([] ; l low ⊢ᴳ M′ ⦂ A′))
cfgs = [ ⟨ SubInj.M , SubInj.M′ , _ , _ , SubInj.⊢M , SubInj.⊢M′ ⟩ ]

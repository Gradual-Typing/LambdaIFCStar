module ExamplePrograms.Simulation.Examples where

open import Data.List
open import Data.Product using (_×_; ∃-syntax; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

open import Agda.Builtin.String
open import Common.Utils
open import Common.Types
open import Surface.SurfaceLang

Cfg = String ×
  ∃[ M ] ∃[ M′ ] ∃[ A ] ∃[ A′ ]
  ([] ; l low ⊢ᴳ M ⦂ A) × ([] ; l low ⊢ᴳ M′ ⦂ A′)

open import ExamplePrograms.Simulation.SubInj as SubInj
open import ExamplePrograms.Simulation.IfAssign as IfAssign

cfgs : List Cfg
cfgs = [
    ⟨ "SubInj"   , SubInj.M   , SubInj.M′   , _ , _ , SubInj.⊢M   , SubInj.⊢M′   ⟩ ,
    ⟨ "IfAssign" , IfAssign.M , IfAssign.M′ , _ , _ , IfAssign.⊢M , IfAssign.⊢M′ ⟩
  ]

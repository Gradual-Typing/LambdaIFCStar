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
open import ExamplePrograms.Simulation.IfTrueAssign as IfTrueAssign
open import ExamplePrograms.Simulation.IfFalseAssign as IfFalseAssign

cfgs : List Cfg
cfgs = [
    ⟨ "SubInj"        , SubInj.M        , SubInj.M′        , _ , _ , SubInj.⊢M        , SubInj.⊢M′        ⟩ ,
    ⟨ "IfTrueAssign"  , IfTrueAssign.M  , IfTrueAssign.M′  , _ , _ , IfTrueAssign.⊢M  , IfTrueAssign.⊢M′  ⟩ ,
    ⟨ "IfFalseAssign" , IfFalseAssign.M , IfFalseAssign.M′ , _ , _ , IfFalseAssign.⊢M , IfFalseAssign.⊢M′ ⟩
  ]

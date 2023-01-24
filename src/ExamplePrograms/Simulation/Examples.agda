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

open import ExamplePrograms.Simulation.FunInjArg      as FunInjArg
open import ExamplePrograms.Simulation.AppFunProxy    as AppFunProxy
open import ExamplePrograms.Simulation.SubInj         as SubInj
open import ExamplePrograms.Simulation.IfTrueAssign   as IfTrueAssign
open import ExamplePrograms.Simulation.IfFalseAssign  as IfFalseAssign
open import ExamplePrograms.Simulation.WrongAnn1      as WrongAnn1

cfgs : List Cfg
cfgs =
  ⟨ "AppFunProxy"   , AppFunProxy.M   , AppFunProxy.M′   , _ , _ , AppFunProxy.⊢M   , AppFunProxy.⊢M′   ⟩ ∷
  ⟨ "FunInjArg"     , FunInjArg.M     , FunInjArg.M′     , _ , _ , FunInjArg.⊢M     , FunInjArg.⊢M′     ⟩ ∷
  ⟨ "SubInj"        , SubInj.M        , SubInj.M′        , _ , _ , SubInj.⊢M        , SubInj.⊢M′        ⟩ ∷
  ⟨ "IfTrueAssign"  , IfTrueAssign.M  , IfTrueAssign.M′  , _ , _ , IfTrueAssign.⊢M  , IfTrueAssign.⊢M′  ⟩ ∷
  ⟨ "IfFalseAssign" , IfFalseAssign.M , IfFalseAssign.M′ , _ , _ , IfFalseAssign.⊢M , IfFalseAssign.⊢M′ ⟩ ∷
  ⟨ "WrongAnn1"     , WrongAnn1.M     , WrongAnn1.M′     , _ , _ , WrongAnn1.⊢M     , WrongAnn1.⊢M′     ⟩ ∷ []

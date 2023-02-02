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

open import ExamplePrograms.Simulation.Values         as Values
open import ExamplePrograms.Simulation.FunInjArg      as FunInjArg
open import ExamplePrograms.Simulation.AppFunProxy    as AppFunProxy
open import ExamplePrograms.Simulation.DerefRefProxy  as DerefRefProxy
open import ExamplePrograms.Simulation.RefAndImplicitFlow as RefImpFlow
open import ExamplePrograms.Simulation.RefNSU1        as RefNSU1
open import ExamplePrograms.Simulation.RefNSU2        as RefNSU2
open import ExamplePrograms.Simulation.RefNSU3        as RefNSU3
open import ExamplePrograms.Simulation.SubInj1        as SubInj1
open import ExamplePrograms.Simulation.SubInj2        as SubInj2
open import ExamplePrograms.Simulation.InjProj1       as InjProj1
open import ExamplePrograms.Simulation.InjProj2       as InjProj2
open import ExamplePrograms.Simulation.IfTrueAssign   as IfTrueAssign
open import ExamplePrograms.Simulation.IfFalseAssign  as IfFalseAssign
open import ExamplePrograms.Simulation.WrongAnn1      as WrongAnn1
open import ExamplePrograms.Simulation.WrongAnn2      as WrongAnn2

cfgs : List Cfg
cfgs =
  ⟨ "Values"        , Values.M        , Values.M′        , _ , _ , Values.⊢M        , Values.⊢M′        ⟩ ∷
  ⟨ "AppFunProxy"   , AppFunProxy.M   , AppFunProxy.M′   , _ , _ , AppFunProxy.⊢M   , AppFunProxy.⊢M′   ⟩ ∷
  ⟨ "DerefRefProxy" , DerefRefProxy.M , DerefRefProxy.M′ , _ , _ , DerefRefProxy.⊢M , DerefRefProxy.⊢M′ ⟩ ∷
  ⟨ "RefImpFlow"    , RefImpFlow.M    , RefImpFlow.M′    , _ , _ , RefImpFlow.⊢M    , RefImpFlow.⊢M′    ⟩ ∷
  ⟨ "RefNSU1"       , RefNSU1.M       , RefNSU1.M′       , _ , _ , RefNSU1.⊢M       , RefNSU1.⊢M′       ⟩ ∷
  ⟨ "RefNSU2"       , RefNSU2.M       , RefNSU2.M′       , _ , _ , RefNSU2.⊢M       , RefNSU2.⊢M′       ⟩ ∷
  ⟨ "RefNSU3"       , RefNSU3.M       , RefNSU3.M′       , _ , _ , RefNSU3.⊢M       , RefNSU3.⊢M′       ⟩ ∷
  ⟨ "FunInjArg"     , FunInjArg.M     , FunInjArg.M′     , _ , _ , FunInjArg.⊢M     , FunInjArg.⊢M′     ⟩ ∷
  ⟨ "SubInj1"       , SubInj1.M       , SubInj1.M′       , _ , _ , SubInj1.⊢M       , SubInj1.⊢M′       ⟩ ∷
  ⟨ "SubInj2"       , SubInj2.M       , SubInj2.M′       , _ , _ , SubInj2.⊢M       , SubInj2.⊢M′       ⟩ ∷
  ⟨ "InjProj1"      , InjProj1.M      , InjProj1.M′      , _ , _ , InjProj1.⊢M      , InjProj1.⊢M′      ⟩ ∷
  ⟨ "InjProj2"      , InjProj2.M      , InjProj2.M′      , _ , _ , InjProj2.⊢M      , InjProj2.⊢M′      ⟩ ∷
  ⟨ "IfTrueAssign"  , IfTrueAssign.M  , IfTrueAssign.M′  , _ , _ , IfTrueAssign.⊢M  , IfTrueAssign.⊢M′  ⟩ ∷
  ⟨ "IfFalseAssign" , IfFalseAssign.M , IfFalseAssign.M′ , _ , _ , IfFalseAssign.⊢M , IfFalseAssign.⊢M′ ⟩ ∷
  ⟨ "WrongAnn1"     , WrongAnn1.M     , WrongAnn1.M′     , _ , _ , WrongAnn1.⊢M     , WrongAnn1.⊢M′     ⟩ ∷
  ⟨ "WrongAnn2"     , WrongAnn2.M     , WrongAnn2.M′     , _ , _ , WrongAnn2.⊢M     , WrongAnn2.⊢M′     ⟩ ∷
  []

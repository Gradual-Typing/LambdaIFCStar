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
open import ExamplePrograms.Simulation.AppFunProxy1   as AppFunProxy1
open import ExamplePrograms.Simulation.AppFunProxy2   as AppFunProxy2
open import ExamplePrograms.Simulation.FunCast1       as FunCast1
open import ExamplePrograms.Simulation.FunCast2       as FunCast2
open import ExamplePrograms.Simulation.FunCast3       as FunCast3
open import ExamplePrograms.Simulation.FunCast4       as FunCast4
open import ExamplePrograms.Simulation.DerefRefProxy  as DerefRefProxy
open import ExamplePrograms.Simulation.AssignRefProxy as AssignRefProxy
open import ExamplePrograms.Simulation.RefAndImplicitFlow as RefImpFlow
open import ExamplePrograms.Simulation.RefNSU1        as RefNSU1
open import ExamplePrograms.Simulation.RefNSU2        as RefNSU2
open import ExamplePrograms.Simulation.RefNSU3        as RefNSU3
open import ExamplePrograms.Simulation.AssignNSU1     as AssignNSU1
open import ExamplePrograms.Simulation.AssignNSU2     as AssignNSU2
open import ExamplePrograms.Simulation.AssignNSU3     as AssignNSU3
open import ExamplePrograms.Simulation.AssignNSU4     as AssignNSU4
open import ExamplePrograms.Simulation.RefCast1       as RefCast1
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
  ⟨ "AppFunProxy1"  , AppFunProxy1.M  , AppFunProxy1.M′  , _ , _ , AppFunProxy1.⊢M  , AppFunProxy1.⊢M′  ⟩ ∷
  ⟨ "AppFunProxy2"  , AppFunProxy2.M  , AppFunProxy2.M′  , _ , _ , AppFunProxy2.⊢M  , AppFunProxy2.⊢M′  ⟩ ∷
  ⟨ "FunCast1"      , FunCast1.M      , FunCast1.M′      , _ , _ , FunCast1.⊢M      , FunCast1.⊢M′      ⟩ ∷
  ⟨ "FunCast2"      , FunCast2.M      , FunCast2.M′      , _ , _ , FunCast2.⊢M      , FunCast2.⊢M′      ⟩ ∷
  ⟨ "FunCast3"      , FunCast3.M      , FunCast3.M′      , _ , _ , FunCast3.⊢M      , FunCast3.⊢M′      ⟩ ∷
  ⟨ "FunCast4"      , FunCast4.M      , FunCast4.M′      , _ , _ , FunCast4.⊢M      , FunCast4.⊢M′      ⟩ ∷
  ⟨ "DerefRefProxy" , DerefRefProxy.M , DerefRefProxy.M′ , _ , _ , DerefRefProxy.⊢M , DerefRefProxy.⊢M′ ⟩ ∷
  ⟨ "AssignRefProxy" , AssignRefProxy.M , AssignRefProxy.M′ , _ , _ , AssignRefProxy.⊢M , AssignRefProxy.⊢M′ ⟩ ∷
  ⟨ "RefImpFlow"    , RefImpFlow.M    , RefImpFlow.M′    , _ , _ , RefImpFlow.⊢M    , RefImpFlow.⊢M′    ⟩ ∷
  ⟨ "RefNSU1"       , RefNSU1.M       , RefNSU1.M′       , _ , _ , RefNSU1.⊢M       , RefNSU1.⊢M′       ⟩ ∷
  ⟨ "RefNSU2"       , RefNSU2.M       , RefNSU2.M′       , _ , _ , RefNSU2.⊢M       , RefNSU2.⊢M′       ⟩ ∷
  ⟨ "RefNSU3"       , RefNSU3.M       , RefNSU3.M′       , _ , _ , RefNSU3.⊢M       , RefNSU3.⊢M′       ⟩ ∷
  ⟨ "AssignNSU1"    , AssignNSU1.M    , AssignNSU1.M′    , _ , _ , AssignNSU1.⊢M    , AssignNSU1.⊢M′    ⟩ ∷
  ⟨ "AssignNSU2"    , AssignNSU2.M    , AssignNSU2.M′    , _ , _ , AssignNSU2.⊢M    , AssignNSU2.⊢M′    ⟩ ∷
  ⟨ "AssignNSU3"    , AssignNSU3.M    , AssignNSU3.M′    , _ , _ , AssignNSU3.⊢M    , AssignNSU3.⊢M′    ⟩ ∷
  ⟨ "AssignNSU4"    , AssignNSU4.M    , AssignNSU4.M′    , _ , _ , AssignNSU4.⊢M    , AssignNSU4.⊢M′    ⟩ ∷
  ⟨ "RefCast1"      , RefCast1.M      , RefCast1.M′      , _ , _ , RefCast1.⊢M      , RefCast1.⊢M′      ⟩ ∷
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

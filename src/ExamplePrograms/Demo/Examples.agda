module ExamplePrograms.Demo.Examples where

open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

open import Common.Utils
open import Common.Types
open import Surface.SurfaceLang
open import CC.CCStatics renaming (Term to CCTerm)

open import ExamplePrograms.Demo.Example1 public
open import ExamplePrograms.Demo.Example2 public
open import ExamplePrograms.Demo.Example3 public

Cfg = Term × ∃[ M ] ∃[ A ] [] ; ∅ ; l low ; low ⊢ M ⦂ A

cfgs : List Cfg
cfgs =
  -- Example 1 --
  ⟨ N    , 𝒞N    , _ , ⊢𝒞N  ⟩   ∷ ⟨ M*   , 𝒞M*   , _ , ⊢𝒞M*   ⟩ ∷
  -- Example 2 --
  ⟨ N₁   , 𝒞N₁   , _ , ⊢𝒞N₁ ⟩   ∷ ⟨ N₂   , 𝒞N₂   , _ , ⊢𝒞N₂   ⟩ ∷
  -- Example 3 --
                    {- fully annotated     : -}
  ⟨ M₁   , 𝒞M₁   , _ , ⊢𝒞M₁   ⟩ ∷ ⟨ M₂   , 𝒞M₂   , _ , ⊢𝒞M₂   ⟩ ∷
                    {- partially annotated : -}
  ⟨ M*₁  , 𝒞M*₁  , _ , ⊢𝒞M*₁  ⟩ ∷ ⟨ M*₂  , 𝒞M*₂  , _ , ⊢𝒞M*₂  ⟩ ∷
                    {- partially annotated : -}
  ⟨ M*₁′ , 𝒞M*₁′ , _ , ⊢𝒞M*₁′ ⟩ ∷ ⟨ M*₂′ , 𝒞M*₂′ , _ , ⊢𝒞M*₂′ ⟩ ∷ []

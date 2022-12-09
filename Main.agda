{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.String
open import Text.Printf
open import IO

open import Utils
open import Types
open import HeapTyping
open import Interp

open import SurfaceLang
open import CC renaming (Term to CCTerm)
open import Examples
open import PrettyPrint renaming (pprint-mult-reduction to pprint)

main =
  run {Agda.Primitive.lzero}
    (do
      (putStrLn (foldr format "" example1-cfgs))
      (putStrLn (foldr format "" example2-cfgs))
      (putStrLn (foldr format "" example3-cfgs))
      (putStrLn "\ESC[101mEND\ESC[0m"))
  where
  example1-cfgs = [ ⟨ N  , 𝒞N  , ⊢𝒞N  ⟩ , ⟨ M* , 𝒞M* , ⊢𝒞M* ⟩ ]
  example2-cfgs = [ ⟨ N₁ , 𝒞N₁ , ⊢𝒞N₁ ⟩ , ⟨ N₂ , 𝒞N₂ , ⊢𝒞N₂ ⟩ ]
  example3-cfgs =
    [ {- fully annotated     : -} ⟨ M₁   , 𝒞M₁   , ⊢𝒞M₁   ⟩ , ⟨ M₂   , 𝒞M₂   , ⊢𝒞M₂   ⟩ ,
      {- partially annotated : -} ⟨ M*₁  , 𝒞M*₁  , ⊢𝒞M*₁  ⟩ , ⟨ M*₂  , 𝒞M*₂  , ⊢𝒞M*₂  ⟩ ,
      {- partially annotated : -} ⟨ M*₁′ , 𝒞M*₁′ , ⊢𝒞M*₁′ ⟩ , ⟨ M*₂′ , 𝒞M*₂′ , ⊢𝒞M*₂′ ⟩ ]
  format : ∀ {A} → (Term × Σ[ M ∈ CCTerm ] [] ; ∅ ; l low ; low ⊢ M ⦂ A) → String → String
  format ⟨ M , 𝒞M , ⊢𝒞M ⟩ rest =
    (printf "%s\n\n%s\n%s"
      (printf "\ESC[7m**** Running λSEC* program: ****\ESC[0m\n%s" (pprint-term M))
      (printf "\ESC[7m**** Reduction of the compiled λSEC⇒ term: ****\ESC[0m\n%s\n"
        (let ⟨ _ , _ , R ⟩ = interp 𝒞M ⊢𝒞M 42 in pprint R))
      rest)

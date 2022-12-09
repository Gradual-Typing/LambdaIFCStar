{-# OPTIONS --guardedness #-}

open import Data.List using ([])
open import Data.Product using (∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO

open import Utils
open import Types
open import PrettyPrint
open import HeapTyping
open import Interp

open import Examples

main =
  run {Agda.Primitive.lzero}
    (do
      (putStrLn (pprint-type A₁))
      (putStrLn "")
      (putStrLn (pprint-type A₂))
      (putStrLn "")
      (putStrLn (pprint-term M*))
      (putStrLn "")
      (putStrLn (pprint-cc M*⇒))
      (putStrLn "")
      (putStrLn (pprint-mult-reduction Rd))
      (putStrLn "")
      (putStrLn (let ⟨ _ , R ⟩ = RdN₁ in pprint-mult-reduction R))
      (putStrLn "")
      (putStrLn (let ⟨ _ , R ⟩ = RdN₂ in pprint-mult-reduction R))
      (putStrLn "")
      (putStrLn (let ⟨ _ , _ , R ⟩ = interp low 𝒞N₂ ⊢𝒞N₂ ∅ ⊢μ-nil (≾-l l≼l) 42 in pprint-mult-reduction R))
      )

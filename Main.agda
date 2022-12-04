{-# OPTIONS --guardedness #-}

open import Data.List using ([])
open import Data.Product using (∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO

open import Types
open import PrettyPrint

open import Example1

main =
  run {Agda.Primitive.lzero}
    (do (putStrLn (pprint-type (⟦ ⋆ ⟧ Ref (` Bool of l high) of l low ⇒ (` Bool of l high) of l low)))
        (putStrLn (pprint-term M*))
        (putStrLn "END"))

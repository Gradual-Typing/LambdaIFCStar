module CC where

open import SecurityLabels
open import TypeBasedCast using (Cast_⇒_)

open import CCSyntax Cast_⇒_ public
open import CCTyping Cast_⇒_ public

open import Values            public
open import ApplyCast         public
open import ApplyCastRelation public
open import ProxyElimination  public


{- There are 3 forms of reference creation: static, unchecked, and checked -}
data RefCreation : (StaticLabel → Term → Term) → Set where
  static    : RefCreation ref[_]_
  unchecked : RefCreation ref?[_]_
  checked   : RefCreation ref✓[_]_

{- There are 3 forms of reference assignment: static, unchecked, and checked -}
data RefAssign : (Term → Term → Term) → Set where
  static    : RefAssign _:=_
  unchecked : RefAssign _:=?_
  checked   : RefAssign _:=✓_

module Data.Unit.Finite where

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (refl)

open import Finite

instance
  ⊤-IsFinite : IsFinite ⊤
  ⊤-IsFinite = finite [ tt ] λ where tt → here refl

module Data.Maybe.Finite where

open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality
open import Level

open import Finite

instance
  Maybe-IsFinite : {ℓ : Level} {A : Set ℓ} ⦃ af : IsFinite A ⦄ → IsFinite (Maybe A)
  Maybe-IsFinite ⦃ af = finite es _∈es ⦄ =
    record { membership = maybe (there ∘ ∈-map⁺ _ ∘ _∈es) (here refl) }

module Data.Vec.Finite where

open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Level

open import Finite
open IsFinite

instance
  Vec-IsFinite : {ℓ : Level} {A : Set ℓ} {n : ℕ} ⦃ af : IsFinite A ⦄ → IsFinite (Vec A n)
  elements (Vec-IsFinite {n = 0    }       ) = List.[ [] ]
  elements (Vec-IsFinite {n = suc n} ⦃ af ⦄) = toList (Vec.map (uncurry _∷_) (allPairs (elementsVec af) (elementsVec (Vec-IsFinite))))

  membership Vec-IsFinite [] = here refl
  membership (Vec-IsFinite ⦃ af ⦄) (a ∷ as) =
    ∈-toList⁺
      (∈-map⁺ _
        (∈-allPairs⁺
          (∈-fromList⁺ (membership af a))
          (∈-fromList⁺ (membership Vec-IsFinite as))))

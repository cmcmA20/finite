module Data.Product.Finite where

open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.Product
open import Data.Vec.Properties
open import Finite
open import Function

open IsFinite

instance
  Σ-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    {af : IsFinite A} → {bf : ∀ a → IsFinite (B a)} →
    IsFinite (∃ B)
  Σ-IsFinite {af = af} {bf = bf} =
    finite _ λ where
      (a , b) →
        ∈-concat⁺′
          (∈-map⁺ _ (membership (bf a) b))
          (∈-map⁺ _ (membership af a))

  ×-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → {af : IsFinite A} → {bf : IsFinite B} → IsFinite (A × B)
  ×-IsFinite {af = af} {bf = bf} = Σ-IsFinite {af = af} {bf = const bf}

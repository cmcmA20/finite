module Finite where

open import Data.List.Base as List using (List; []; _∷_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product as Σ using (_×_; _,_; -,_; _,′_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_; fromList)
open import Function.Base using (_∘_; id; case_of_)
open import Function.Equality using (_⟨$⟩_; cong)
open import Function.LeftInverse using (LeftInverse; _↞_)
open import Level using (Level)
open import Relation.Binary using (IsDecStrictPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; subst)
open import Relation.Nullary.Decidable using (Dec; no; yes; fromWitness; toWitness; True)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : Set ℓ₂

fromWitness∘toWitness≗id : {A? : Dec A} → fromWitness {Q = A?} ∘ toWitness ≗ id
fromWitness∘toWitness≗id {A? = A?} with A?
… | yes _ = λ { tt → refl }
… | no  _ = λ ()

FiniteRec : (A → List A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec {A = A} P B = (xs ys : List A) → ((a : A) → (a ∈ xs × P a xs) ⊎ (a ∈ ys)) → B

record IsFinite (A : Set ℓ) : Set ℓ where
  constructor finite
  field
    elements : List A
    membership : (a : A) → a ∈ elements

  size = length elements
  elementsVec = fromList elements

  private
    variable
      xs as : List A
      a     : A

  finite-⊆ : xs ⊆ elements
  finite-⊆ {x = x} _ = membership x

  finiteRec : {Q : A → List A → Set ℓ₁} → FiniteRec Q B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

  dec : Dec A
  dec with elements | membership
  ... | []    | _∈[] = no λ a → case a ∈[] of λ ()
  ... | a ∷ _ | _    = yes a

  module _ {P : A → Set ℓ₁} (P? : (a : A) → Dec (P a)) where
    ∃? : Dec (∃ P)
    ∃? = finiteRec go
      where
        go : FiniteRec (λ a _ → ¬ P a) _
        go xs [] elem = no λ where
          (a , pa) → case elem a of λ where
            (inj₁ (_ , ¬pa)) → ¬pa pa
            (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (yes py) → yes (-, py)
          (no ¬py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , ¬pa)) → inj₁ (there a∈xs , ¬pa)
              (inj₂ (here  refl)) → inj₁ (here refl , ¬py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    ∀? : Dec ((x : A) → P x)
    ∀? = finiteRec go
      where
        go : FiniteRec (λ a _ → P a) _
        go xs [] elem = yes λ a → case elem a of λ where
          (inj₁ (_ , pa)) → pa
          (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (no ¬py) → no λ py → ¬py (py _)
          (yes py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , pa )) → inj₁ (there a∈xs , pa)
              (inj₂ (here  refl)) → inj₁ (here refl , py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    filter-∃ : List A → List (∃ P)
    filter-∃ [] = []
    filter-∃ (a ∷ as) =
      case P? a of λ where
        (yes pa) → (-, pa) ∷ filter-∃ as
        (no ¬pa) → filter-∃ as

    filter-∃-∈ : a ∈ as → (pa : True (P? a)) → (a , toWitness pa) ∈ filter-∃ as
    filter-∃-∈ {as = a ∷ as} (here refl) pa with P? a
    ... | yes pa′ = here refl
    filter-∃-∈ {as = a ∷ as} (there e) pa with P? a
    ... | yes pa′ = there (filter-∃-∈ e pa)
    ... | no ¬pa  = filter-∃-∈ e pa

    filter-∃-True : List A → List (∃ (True ∘ P?))
    filter-∃-True = List.map (Σ.map₂ fromWitness) ∘ filter-∃

    filter-∃-True-∈ : a ∈ as → (pa : True (P? a)) → (a , pa) ∈ filter-∃-True as
    filter-∃-True-∈ {a} e pa =
      subst
        (λ pa′ → (a , pa′) ∈ _)
        (fromWitness∘toWitness≗id _)
        (∈-map⁺ _ (filter-∃-∈ e pa))

    filter : IsFinite (∃ (True ∘ P?))
    filter = record
      { elements = filter-∃-True elements
      ; membership = λ where (a , pa) → filter-∃-True-∈ (membership a) pa
      }

  module Ordered {_≈_ : A → A → Set ℓ₁} {_<_ : A → A → Set ℓ₂}
                 (<-po : IsDecStrictPartialOrder _≈_ _<_)
    where
    open IsDecStrictPartialOrder <-po

    _≮_ : A → A → Set ℓ₂
    a ≮ b = ¬ (a < b)

    maxOf : A → (as : List A) → ∃ λ a → {x : A} → x ∈ as → a ≮ x
    maxOf p [] = p , λ ()
    maxOf p (a ∷ as) =
      let x , f = maxOf p as in
        case (a <? x) ,′ (x <? a) of λ where
          (yes a<x , _) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → asym x<y a<x
              (there y∈as) → f y∈as x<y
          (_ , yes x<a) → a , λ {y} y∈a∷as a<y →
            case y∈a∷as of λ where
              (here refl) → irrefl Eq.refl a<y
              (there y∈as) → f y∈as (trans x<a a<y)
          (no a≮x , no x≮a) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → x≮a x<y
              (there y∈as) → f y∈as x<y

    max : (¬ A) ⊎ (∃ λ a → ∀ x → a ≮ x)
    max with dec
    ... | yes a = let x , m = maxOf a elements in inj₂ (x , (m ∘ membership))
    ... | no ¬a = inj₁ ¬a

    pointedMax : A → ∃ λ a → ∀ x → a ≮ x
    pointedMax x with max
    ... | inj₁ ¬a = contradiction x ¬a
    ... | inj₂ a  = a

open IsFinite

via-left-inverse : (A ↞ B) → IsFinite B → IsFinite A
via-left-inverse f finB = record
  { elements = List.map (from ⟨$⟩_) (elements finB)
  ; membership = λ a → subst (_∈ _) (left-inverse-of a) (∈-map⁺ _ (membership finB (to ⟨$⟩ a)))
  } where open LeftInverse f

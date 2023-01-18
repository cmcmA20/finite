module Finite.Pigeonhole where

open import Data.Fin.Base using (Fin; zero; suc) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using () renaming (pigeonhole to Fin-pigeonhole)
open import Data.Nat.Base using (ℕ; _<_; _>_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (∃₂; _×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; fromList)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Membership.Propositional.Properties using (∈-lookup; ∈-fromList⁺; ∈-toList⁺)
open import Data.Vec.Relation.Unary.Any using (Any; here; there; index)
open import Function.Base using (_∘_; flip)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)
open import Relation.Nullary using (Dec; no; yes)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import Finite
open IsFinite

private variable ℓ : Level

data Repeats {A : Set ℓ} : {n : ℕ} → Vec A n → Set ℓ where
  here  : {x : A} {n : ℕ} {xs : Vec A n} → x ∈ xs     → Repeats (x ∷ xs)
  there : {x : A} {n : ℕ} {xs : Vec A n} → Repeats xs → Repeats (x ∷ xs)

private
  variable
    A   : Set ℓ
    m n : ℕ

Acyclic : Vec A n → Set _
Acyclic xs = ¬ Repeats xs

module _ (_≟_ : (a b : A) → Dec (a ≡ b)) where
  infix 4 _∈?_
  _∈?_ : (a : A) (as : Vec A n) → Dec (a ∈ as)
  a ∈? [] = no λ ()
  a ∈? b ∷ as with a ≟ b
  ... | yes refl = yes (here refl)
  ... | no a≢b with a ∈? as
  ... | yes a∈as = yes (there a∈as)
  ... | no  a∉as = no λ where
    (here refl ) → a≢b  refl
    (there a∈as) → a∉as a∈as

  repeats? : (as : Vec A n) → Dec (Repeats as)
  repeats? [] = no λ ()
  repeats? (a ∷ as) with a ∈? as
  ... | yes a∈as = yes (here a∈as)
  ... | no  a∉as with repeats? as
  ... | yes r = yes (there r)
  ... | no ¬r = no λ where
    (here a∈as) → a∉as a∈as
    (there r) → ¬r r

infix 4 _⊆_
_⊆_ : Vec A m → Vec A n → Set _
xs ⊆ ys = {x : _} → x ∈ xs → x ∈ ys

⊆-inject : (xs : Vec A m) (ys : Vec A n) → xs ⊆ ys → Fin m → Fin n
⊆-inject xs ys f = index ∘ f ∘ flip ∈-lookup xs

pigeonholeVec : (xs : Vec A m) (ys : Vec A n) →
                n < m →
                (f : Fin m → Fin n) →
                (g : (i : Fin m) → lookup xs i ≡ lookup ys (f i)) →
                ∃₂ λ i j → i <ᶠ j × lookup xs i ≡ lookup xs j
pigeonholeVec xs ys p f g with Fin-pigeonhole p f
… | i , j , i<j , q =
      i , j , i<j ,
        (begin
          lookup xs i
        ≡⟨ g i ⟩
          lookup ys (f i)
        ≡⟨ cong (lookup ys) q ⟩
          lookup ys (f j)
        ≡⟨ sym (g j) ⟩
          lookup xs j
        ∎) where open ≡-Reasoning

lookup-repeats : (xs : Vec A n) (i j : Fin n) →
                 i <ᶠ j → lookup xs i ≡ lookup xs j →
                 Repeats xs
lookup-repeats (x ∷ xs) zero    zero    i<j   p    = contradiction i<j λ ()
lookup-repeats (x ∷ xs) zero    (suc j) i<j   refl = here (∈-lookup j xs)
lookup-repeats (x ∷ xs) (suc i) zero    i<j   refl = here (∈-lookup i xs)
lookup-repeats (x ∷ xs) (suc i) (suc j) si<sj p    = there (lookup-repeats xs i j (≤-pred si<sj) p)

lookup-⊆ : (xs : Vec A m) (ys : Vec A n) →
           (f : Fin m → Fin n) →
           ((i : Fin m) → lookup xs i ≡ lookup ys (f i)) →
           xs ⊆ ys
lookup-⊆ .(_ ∷ _) ys f g (here refl) rewrite g zero = ∈-lookup (f zero) ys
lookup-⊆ .(_ ∷ _) ys f g (there i) = lookup-⊆ _ ys (f ∘ suc) (g ∘ suc) i

lookup-index : {x : A} {xs : Vec A n} (i : x ∈ xs) → x ≡ lookup xs (index i)
lookup-index (here refl) = refl
lookup-index (there i) = lookup-index i

lookup-⊆-≡ : (xs : Vec A m) (ys : Vec A n)
             (f : xs ⊆ ys) →
             (i : Fin m) → lookup xs i ≡ lookup ys (⊆-inject xs ys f i)
lookup-⊆-≡ xs ys f = lookup-index ∘ f ∘ flip ∈-lookup xs

pigeonhole : (xs : Vec A m) (ys : Vec A n) →
             n < m → xs ⊆ ys →
             Repeats xs
pigeonhole xs ys p f =
  let i , j , i≢j , q = pigeonholeVec xs ys p (⊆-inject xs ys f) (lookup-⊆-≡ xs ys f)
  in lookup-repeats xs i j i≢j q

finitePigeonhole : (af : IsFinite A) (xs : Vec A n) →
                   n > size af →
                   Repeats xs
finitePigeonhole af xs p =
  pigeonhole xs (fromList (elements af)) p (∈-fromList⁺ ∘ finite-⊆ af ∘ ∈-toList⁺)

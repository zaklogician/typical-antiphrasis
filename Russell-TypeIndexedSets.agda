{-# OPTIONS --type-in-type #-}

module Russell-TypeIndexedSets where

open import Agda.Primitive
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

{-
  Russell’s paradox, the most well-known of the logical paradoxes, highlighted the inconsistency of the
  set theory of Cantor and Frege. The ordinary formulation of Russell's paradox requires that sets
  have a membership relation _∈_ defined over them. At first it may seem that such a relation has no
  straightforward analogue in type theory. However, inductive types allow us to define "type-indexed sets",
  whose behavior closely resembles that of sets in "pure" set theories (such as the naive set theory of 
  Cantor and Frege, and even Zermelo-Fraenkel Set Theory).
  
  A type-indexed set (TIS) consists of an indexing type I, and a type-indexed set f(x) for each x : I.
  We can regard the type-indexed sets that belong to the range  of the function f as the elements of the
  type-indexed set.
-}

record TIS : Set₁ where
  inductive
  constructor tis
  field
    IndexType : Set
    elements : IndexType → TIS
open TIS

{-
  We obtain a membership relation (_∈_) that relates type-indexed sets to other type-indexed sets.
-}

_∈_ : TIS → TIS → Set₁
x ∈ y = ∃ λ i → elements y i ≡ x

{-
  Enabling `--type-in-type` allows us to define a comprehension principle, analogous to the unrestricted
  comprehension principle of Cantor-Frege-style naive set theory.

  Given a property φ that a type-indexed set may have, we can consider the type `Σ(x ∈ TIS).φ(x)`. 
  Recall that this type consists of pairs (x,p) where x is some type-indexed set, and `p` constitutes a
  proof that x satisfies the property φ. Equipping this type with the obivous projection function of 
  signature `(Σ(x ∈ TIS).φ(x)) → TIS` yields a type-indexed set whose members satisfy the property φ.
  We write ⟦φ⟧ to denote this type-indexed set.
-}

⟦_⟧ : (TIS → Set) → TIS
⟦ φ ⟧ = tis (∃ λ (x : TIS) → φ x) proj₁

{-
  The Russell TIS contains precisely those type-indexed sets that do not contain themselves as elements.
  So elements of R do not contain themselves, and type-indexed sets that do not contain themselves always
  belong to R. 
-}

R : TIS
R = ⟦ (λ x → x ∈ x → ⊥) ⟧

element-of-R-does-not-contain-itself : ∀ x → x ∈ R → x ∈ x → ⊥
element-of-R-does-not-contain-itself x ((.x , k-notin-k) , refl) = k-notin-k

does-not-contain-itself-belongs-to-R : ∀ x → (x ∈ x → ⊥) → x ∈ R
does-not-contain-itself-belongs-to-R x x-notin-x = (x , x-notin-x) , refl

{-
  Now assume that the TIS R contains itself. Since elements of R do not contain themselves, and R ∈ R
  by assumption, we conclude that R does not contain itself, a contradiction. Our assumption must have
  been faulty, so we conclude that R does not contain itself.
-}

R-notin-R : R ∈ R → ⊥
R-notin-R R-in-R = element-of-R-does-not-contain-itself R R-in-R R-in-R

{-
  Since R does not contain itself, it must belong to R, a contradiction.
-}

R-in-R : R ∈ R
R-in-R = does-not-contain-itself-belongs-to-R R R-notin-R

paradox : ⊥
paradox = R-notin-R R-in-R

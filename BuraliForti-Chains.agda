{-
  A paradox of the Burali-Forti type, using infinite chains qua functions ℕ → X.
  Similar to the argument given by Per Martin-Löf for the first version of his type theory.
  
  The nomenclature is (deliberately) unusual, for didactic reasons.
-}

{-# OPTIONS --type-in-type #-}

module BuraliForti-Chains where

open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Agda.Primitive

{-
  Given a set P and any binary relation ≻ between elements of P, we can define the class of ≺-chains
  as functions f : ℕ → P satisfying the following:
  * the 2nd element of the chain, f(1), is related to the 1st element, f(0), as f(1) ≺ f(0)
  * the 3rd element, f(2), is related to the 2nd, f(1), as f(2) ≺ f(1)
  * the 4th, f(3) is related to f(2), as f(3) ≺ f(2)
  * f(4) is related to f(3), as f(4) ≺ f(3)
  * f(5) ≺ f(4),
  * and so on...
  
  Diagrammatically, we can represent this situation as

  ... ≺ f(4) ≺ f(3) ≺ f(2) ≺ f(1) ≺ f(0), for indices 
  ... >   4  >   3  >   2  >   1  >   0

-}

record Chain {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (R : A → A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    _at_ : ℕ → A
    is-chain : ∀ n → R (_at_ (suc n)) (_at_ n)
open Chain

{-
  We call a relation _transitive_ if whenever it relates some x to y and y to z, then it also relates x to z.

  The usual order relation "less than" is transitive: if x is less than y, and y is less than
  z, then we can safely conclude that x itself is less than z.

  An example of a non-transitive relation would be fatherhood: if x is the father of y, and y is the father
  of z, then x is usually _not_ the father of z.

  In what follows, we will consider a set P equipped with a transitive relation ≺.
  If there are no ≺-chains, then we will call that the structure (P,≺) a _django_ (since it is _unchained_).

  For example, the natural numbers equipped with the usual order relation < ("less than") form a django.
  However, the integers (positive, negative, and zero) do not form a django when equipped with the same
  order relation, since they contain e.g. the chain

  ... < -16 < -8  < -4 < -2  < -1   for indices
  ... >   4 >  3  >  2 >  1  >  0

  Exercise: convince yourself that ℕ does not contain any such chain.
-}

record IsDjango {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (R : A → A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    Django-is-transitive : ∀ {x y z} → R x y → R y z → R x z
    Django-is-unchained : Chain R → ⊥

record Django {ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set ℓ₁
    order : Carrier → Carrier → Set ℓ₂
    is-Django : IsDjango Carrier order
  open IsDjango is-Django public
open Django

{-
  Given a django (P,≺), and an element t ∈ P, the "lower set" P↓t = {x ∈ P | x ≺ t} inherits the 
  django structure: if the relation ≺ is transitive on all of P, then of course it is transitive on the 
  subset P↓t as well. Moreover, P↓t cannot contain any ≺-chains.

  In our previous example, we would have ℕ↓5 = {4,3,2,1}.

  We call djangoes of the form (P↓t,≺) the _prefixes_ of the django (P,≺). You can think of P↓t
  as the structure you get from P by removing everything "above" the element t ∈ P.
-}

record LowerSet {ℓ₁} {ℓ₂} (P : Django {ℓ₁} {ℓ₂}) (t : Carrier P) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _suchThat_
  field
    element : Carrier P
    proof : order P element t

LowerSet-inherited-order :
  {ℓ₁ ℓ₂ : Level} → (P : Django {ℓ₁} {ℓ₂}) (t : Carrier P) →
  LowerSet P t → LowerSet P t → Set ℓ₂
LowerSet-inherited-order P t (x suchThat x-below-t) (y suchThat y-below-t) = order P x y

Prefix : {ℓ₁ : Level} → (P : Django {ℓ₁} {ℓ₁}) → Carrier P → Django {ℓ₁} {ℓ₁}
Prefix {ℓ₁} P t = record
  { Carrier = LowerSet P t
  ; order = LowerSet-inherited-order P t
  ; is-Django = record
    { Django-is-transitive = λ {x y z} → <Pt-is-transitive {x} {y} {z}
    ; Django-is-unchained = <Pt-is-unchained
    }
  } where
  open Django P renaming
    ( Carrier to P'
    ; order to _<P_
    ; Django-is-transitive to <P-is-transitive
    ; Django-is-unchained to <P-is-unchained
    )
  _<Pt_ : LowerSet P t → LowerSet P t → Set ℓ₁
  _<Pt_ = LowerSet-inherited-order P t
  <Pt-is-transitive : ∀ {x y z} → x <Pt y → y <Pt z → x <Pt z
  <Pt-is-transitive {x} {y} {z} x-below-y y-below-z = <P-is-transitive x-below-y y-below-z
  <Pt-is-unchained : Chain _<Pt_ → ⊥
  <Pt-is-unchained F = <P-is-unchained G where
    G : Chain _<P_
    G = record
      { _at_ = λ n → LowerSet.element (F at n)
      ; is-chain = λ n → is-chain F n
      }

_↓_ : {ℓ₁ : Level} → (P : Django {ℓ₁} {ℓ₁}) → Carrier P → Django {ℓ₁} {ℓ₁}
P ↓ t = Prefix P t

{-
  A homomorphism of djangoes f: P → Q is simply a monotone map between the underlying sets.
  If there is a homomorphism f: P → Q, we call P a _subdjango_ of the django Q.
  
  Exercise: verify that this terminology makes sense by proving that all django homomorphisms are injective,
  i.e. they send distinct elements of their domain to distinct elements of their codomain.
-}

record IsSubdjango {ℓ₁ ℓ₂} (A B : Django {ℓ₁} {ℓ₂})
  (inj : Carrier A → Carrier B) : Set (ℓ₁ ⊔ ℓ₂) where
  open Django A renaming (order to _<A_)
  open Django B renaming (order to _<B_)
  field
    inj-is-monotone : ∀ x y → x <A y → inj x <B inj y

record Subdjango {ℓ₁ ℓ₂} (A B : Django {ℓ₁} {ℓ₂}) : Set (ℓ₁ ⊔ ℓ₂) where
  open Django A renaming (Carrier to A')
  open Django B renaming (Carrier to B')
  field
    inj : A' → B'
    isSubdjango : IsSubdjango A B inj
  open IsSubdjango isSubdjango public

{-
  We say that A is a _subprefix_ of B if A is a subdjango of some prefix B↓t of B.
-}

record SubPrefix {ℓ₁} (A B : Django {ℓ₁} {ℓ₁}) : Set ℓ₁ where
  open Django A renaming (Carrier to A')
  open Django B renaming (Carrier to B')
  field
    bound : B'
  open Django (Prefix B bound) renaming (Carrier to Bt')
  field
    inj : A' → Bt'
    isSubdjango : IsSubdjango A (Prefix B bound) inj
  open IsSubdjango isSubdjango public

{-
  If the django A is a subprefix of the django B, we write "A subpr B". Needless to say, every prefix of B
  is also a subprefix of B, via the trivial homomorphism x ↦ x.
-}

_subpr_ : Django → Django → Set
A subpr B = SubPrefix A B

Prefix-is-subpr : ∀ P → ∀ (b : Carrier P) → (P ↓ b) subpr P
Prefix-is-subpr P b = record
  { bound = b
  ; inj = λ z → z
  ; isSubdjango = record { inj-is-monotone = λ _ _ z → z }
  }

{-
  Moreover, taking prefixes is monotone: if a ≺ b, then the prefix P↓a is a subprefix of P↓b.
  (Note: If you know some sheaf theory or some order theory, you may recognize this as an instance of a 
  covariant regular representation.) 
-}
Prefix-is-monotone : ∀ P → ∀ (a b : Carrier P) → order P a b → (P ↓ a) subpr (P ↓ b)
Prefix-is-monotone P a b a-below-b = record
  { bound = a suchThat a-below-b
  ; inj = f
  ; isSubdjango = record { inj-is-monotone = f-is-monotone }
  } where
    open Django P renaming (Carrier to P'; order to _<P_; Django-is-transitive to <P-is-transitive)
    open Django (Prefix P a) renaming (Carrier to Pa'; order to _<Pa_)
    open Django (Prefix (Prefix P b) (a suchThat a-below-b)) renaming (Carrier to Pb'; order to _<Pb_)
    f : Pa' → Pb'
    f (x suchThat x-below-a) = (x suchThat <P-is-transitive x-below-a a-below-b) suchThat x-below-a
    f-is-monotone : ∀ x y → x <Pa y → f x <Pb f y
    f-is-monotone x y x-below-y = x-below-y

{-
  We shall see that the relation "P is a subprefix of Q" is both transitive and unchained.
  
  Transitivity of the subprefix relation is easy to prove:
  If P is a subprefix of Q, then we have a homomorphism f : P → Q↓t for some t∈Q. Since Q↓t is a subset
  of the set Q, we can regard this homomorphism as a map f : P → Q. Moreover, if Q is a subprefix of R,
  then we also have a homomorphism g : Q → R↓s. The composite function g ∘ f is therefore
  a homomorphism g∘f : P → R↓s.
-}

subpr-is-transitive : ∀ {P Q R} → P subpr Q → Q subpr R → P subpr R
subpr-is-transitive {P} {Q} {R} P-subpr-Q Q-subpr-R = record
  { bound = R-bound
  ; inj = f
  ; isSubdjango = record { inj-is-monotone = f-is-monotone }
  } where
  open LowerSet renaming (element to forget-bound)
  open SubPrefix
  open Django P renaming (Carrier to P'; order to _<P_)
  open Django Q renaming (Carrier to Q'; order to _<Q_)
  open Django R renaming (Carrier to R'; order to _<R_)
  R-bound : R'
  R-bound = bound Q-subpr-R
  open Django (Prefix R R-bound) renaming (Carrier to Rb'; order to _<Rb_)
  f : P' → Rb'
  f x = inj Q-subpr-R (forget-bound (inj P-subpr-Q x))
  f-is-monotone : ∀ x y → x <P y → f x <Rb f y
  f-is-monotone x y x-below-y =
    inj-is-monotone Q-subpr-R x' y' (inj-is-monotone P-subpr-Q x y x-below-y) where
    x' : Q'
    x' = forget-bound (inj P-subpr-Q x)
    y' : Q'
    y' = forget-bound (inj P-subpr-Q y)

{-
  Now imagine that we are given infinitely many djangoes, arranged in a chain F such that:
  * the 2nd element of the chain, F(1), is a subprefix of the 1st element, F(0)
  * the 3rd element, F(2), is a subprefix of the 2nd, F(1)
  * the 4th, F(3) is a subprefix of F(2),
  * F(4) is a subprefix of F(3),
  * and so on...

  Diagrammatically, we have

           b₄        b₃        b₂        b₁        b₀
                f₃        f₂        f₁        f₀
  ... --> F(4) ---> F(3) ---> F(2) ---> F(1) ---> F(0), for 
  ... >     4     >   3     >   2     >   1     >   0

  where the bₙ ∈ F(n) are bounds, and the arrows fₙ are django homomorphisms embedding the django F(n+1)
  into the django F(n)↓bₙ, a prefix of F(n). 

  Since the subprefix relation is transitive, each element of my chain is in fact a subprefix of F(0), via
  the "collapse" homomorphism cₙ = fₙ ∘ fₙ₋₁ ∘ ... ∘ f₀ : F(n+1) → F(0).

  Moreover, since fₙ(bₙ₊₁) < bₙ always holds, a simple diagonalization allows us to construct the chain

  ... R c₃(b₄) R c₂(b₃) R c₁(b₂) R c₀(b₁) R b₀, for indices
  ... >     4  >     3  >     2  >     1  >  0

  inside F(0). But that is impossible: F(0) is a django, so it is unchained! Since we could construct a
  chain inside F(0) using a chain F as above, we can conclude that such chains F cannot exist.
-}

subpr-is-unchained : Chain _subpr_ → ⊥
subpr-is-unchained F = <P-is-unchained Diagonal where
  open SubPrefix
  F' : ℕ → Set
  F' n = Carrier (F at n)
  F-is-chain : ∀ n → (F at suc n) subpr (F at n)
  F-is-chain = is-chain F
  open Django (F at zero) renaming
    ( Carrier to P'; order to _<P_
    ; Django-is-transitive to <P-is-transitive
    ; Django-is-unchained to <P-is-unchained
    )
  collapse : ∀ n → (F at suc n) subpr (F at zero)
  collapse zero = F-is-chain zero
  collapse (suc n) = subpr-is-transitive Fssn-below-Fsn (collapse n) where
    Fssn-below-Fsn : (F at suc (suc n)) subpr (F at suc n)
    Fssn-below-Fsn = F-is-chain (suc n)
  collapse-is-monotone : ∀ n → ∀ x y →
    order (F at suc n) x y →
    order (Prefix (F at zero) (bound (collapse n))) (inj (collapse n) x) (inj (collapse n) y)
  collapse-is-monotone zero x y x-below-y = inj-is-monotone (F-is-chain zero) x y x-below-y
  collapse-is-monotone (suc n) x y x-below-y = by-induction _ _ fx-below-fy where
    by-induction :
      ∀ x y → order (F at suc n) x y →
      LowerSet-inherited-order (F at zero) (bound (collapse n)) (inj (collapse n) x) (inj (collapse n) y)
    by-induction = collapse-is-monotone n
    fx-below-fy : order (Prefix (F at suc n) (bound (F-is-chain (suc n))))
      (inj (F-is-chain (suc n)) x) (inj (F-is-chain (suc n)) y)
    fx-below-fy = inj-is-monotone (F-is-chain (suc n)) x y x-below-y
  diagonal : ℕ → P'
  diagonal n = LowerSet.element (inj (collapse n) (bound (F-is-chain (suc n))))
  bound-descent : ∀ n →
    order (F at suc n)
      (LowerSet.element (inj (F-is-chain (suc n)) (bound (F-is-chain (suc (suc n))))))
      (bound (F-is-chain (suc n)))
  bound-descent n = LowerSet.proof (inj (F-is-chain (suc n)) (bound (F-is-chain (suc (suc n)))))
  diagonal-is-chain : ∀ n → diagonal (suc n) <P diagonal n
  diagonal-is-chain n = collapse-is-monotone n _ _ (bound-descent n)
  Diagonal : Chain _<P_
  Diagonal = record { _at_ = diagonal ; is-chain = diagonal-is-chain }

{-
  The subprefix relation is defined between any pair of djangoes. It is both transitive and unchained.
  Therefore, the set of all djangoes forms a django when equipped with this relation!
-}

AllDjangoes : Django {lsuc lzero} -- one universe higher that _subpr_
AllDjangoes = record
  { Carrier = Django
  ; order = _subpr_
  ; is-Django = record
    { Django-is-transitive = subpr-is-transitive
    ; Django-is-unchained = subpr-is-unchained
    }
  }

{-
  If we have enabled --type-in-type, then AllDjangoes can live in the same universe as its relation, _subpr_.
  This allows us to ask whether or not AllDjangoes is a subprefix of itself (otherwise, AllDjangoes would
  lie outside the universe of the _subpr_ relation, and this question wouldn't type check).

  From here on, we assume that --type-in-type is enabled. In this case, we can easily prove that AllDjangoes
  is indeed a subprefix of itself, via the homomorphism that sends each django P to the prefix
    AllDjangoes↓P = {x | x subprefix of P}
  represents AllDjangoes inside its prefix AllDjangoes↓AllDjangoes.
-}

AllDjangoes-subpr-AllDjangoes : AllDjangoes subpr AllDjangoes
AllDjangoes-subpr-AllDjangoes = record
  { bound = AllDjangoes
  ; inj = λ P → (AllDjangoes ↓ P) suchThat (Prefix-is-subpr AllDjangoes P)
  ; isSubdjango = record { inj-is-monotone = Prefix-is-monotone AllDjangoes }
  }

{-
  But then we have a trivial subpr-chain as follows:

  ... --> AllDjangoes subpr AllDjangoes subpr AllDjangoes subpr AllDjangoes, for 
  ...   >       3        >        2        >        1        >        0

-}

AllDjangoes-is-chained : Chain _subpr_
AllDjangoes-is-chained = record
  { _at_ = λ n → AllDjangoes
  ; is-chain = λ n → AllDjangoes-subpr-AllDjangoes
  }

{-
  This contradicts the non-existence of subpr-chains established earlier. 
-}

paradox : ⊥
paradox = Django-is-unchained AllDjangoes AllDjangoes-is-chained

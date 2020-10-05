{-
  A Yabloesque paradox, showing that the positivity check is required to maintain consistency
  in the presence of inductive types, and it cannot be weakened for parametric families.
-}

{-# OPTIONS --no-positivity-check #-}

module Yablo where

open import Data.Nat
open import Data.Empty

{-
  Consider a natural number n. The nth Yablo sentence says that the (n+1)st, (n+2)nd, (n+3)rd and so
  on Yablo sentences are all false.
-}

record Yablo (n : ℕ) : Set where
  inductive
  field
    subsequent-Yablo-false : ∀ k → n < k → Yablo k → ⊥
open Yablo

{-
  If the nth Yablo sentence holds, then all subsequent ones fail. In particular, the (n+2)nd, (n+3)rd,
  (n+4)th and so on Yablo sentences all fail. But the (n+1)st Yablo sentence says precisely that these
  all fail, so the (n+1)st Yablo sentence must hold.
-}

Yablo-n-implies-Yablo-n+1 : ∀ n → Yablo n → Yablo (suc n)
Yablo-n-implies-Yablo-n+1 n yablo-n =
  record {
    subsequent-Yablo-false = λ k sn<k yablo-k → subsequent-Yablo-false yablo-n k (<-reduce sn<k) yablo-k
  } where
  <-reduce : ∀ {k n} → suc n < k → n < k
  <-reduce (s≤s (s≤s z≤n)) = s≤s z≤n
  <-reduce (s≤s (s≤s (s≤s sn<k))) = s≤s (<-reduce (s≤s (s≤s sn<k)))

{-
  But the nth Yablo sentence asserts precisely that all subsequent Yablo sentences, including
  the (n+1)st Yablo sentence, are all false.
-}

Yablo-n-implies-not-Yablo-n+1 : ∀ n → Yablo n → Yablo (suc n) → ⊥
Yablo-n-implies-not-Yablo-n+1 n yablo-n = subsequent-Yablo-false yablo-n (suc n) (s≤s (≤-refl n)) where
  ≤-refl : ∀ n → n ≤ n
  ≤-refl zero = z≤n
  ≤-refl (suc n) = s≤s (≤-refl n)

{-
  Now, assume that the nth Yablo sentence holds. Then, by the previous results, the (n+1)st Yablo
  sentence would both hold and fail, a contradiction. Therefore, our assumption must itself fail,
  and hence all Yablo sentences are false. 
-}

not-Yablo : ∀ n → Yablo n → ⊥
not-Yablo n yn = (Yablo-n-implies-not-Yablo-n+1 n yn) (Yablo-n-implies-Yablo-n+1 n yn)

{-
  However, if all Yablo sentences fail, then the first, second, third, and so on Yablo sentences
  all fail. The zeroth Yablo sentence says precisely that these all fail, so the zeroth Yablo sentence
  must actually hold.
-}
Yablo-0 : Yablo 0
Yablo-0 = record { subsequent-Yablo-false = λ k _ yablo-k → not-Yablo k yablo-k }

{-
  This means that the zeroth Yablo sentence both fails and holds, a contradiction.
-}

paradox : ⊥
paradox = not-Yablo 0 Yablo-0

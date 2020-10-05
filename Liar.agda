{-
  The liar paradox, showing that the positivity check is required to maintain consistency
  in the presence of inductive types.
-}

{-# OPTIONS --no-positivity-check #-}

module Liar where

open import Data.Empty

{-
  The liar sentence says "the Liar sentence is false".
-}

record Liar : Set where
  inductive
  field
    Liar-fails : Liar → ⊥
open Liar

{-
  Assume that the liar sentence holds. It then fails, a contradiction.  Therefore, our assumption
  must have been faulty, and the liar sentence does not hold.
-}

not-liar : Liar → ⊥
not-liar liar = Liar-fails liar liar

{-
  We just proved that the liar sentence fails. But it says precisely this, so it must hold.
-}

liar : Liar
liar = record { Liar-fails = not-liar }

{-
  We managed to prove that the liar sentence both holds and fails, a contradiction.
-}

paradox : ⊥
paradox = not-liar liar

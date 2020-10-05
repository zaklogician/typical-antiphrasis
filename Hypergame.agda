{-# OPTIONS --type-in-type #-}

module Hypergame where

open import Data.Empty

{-
  We can fully describe a round of a turn-based single-player game using the following data:
  * the set of possible moves that we can make in the current round, and
  * for each possible move m, a full description of the subsequent round f(m).
-}

record Round : Set₁ where
  inductive
  field
    moves : Set
    subsequent-round : moves → Round
open Round

{-
  To describe a game, it suffices to fully describe its first round (as the description gives all
  possible first moves, and descriptions of all possible subsequent rounds). 
-}

Game : Set₁
Game = Round

{- 
  We call a game G finite if either
  * G has finished, i.e. we cannot make any valid moves, or else
  * no matter which valid move we make in the current round, the game we end up playing in the next round
    is itself a finite game.
  
  Plainly speaking, a game is finite if it ends after finitely many rounds, no matter what sequence of
  moves is made by the player.
  
  Notice that a finite game may have infinitely many possible moves, and it may even have arbitrarily
  long finite sequences of moves (consider for example the game N where you first pick a natural number,
  then you have to pick a number that is smaller than your previous one, and so on  until you eventually
  reach 0.
-}

data IsFinite (G : Game) : Set where
  game-is-over : (moves G → ⊥) → IsFinite G
  all-subsequent-rounds-are-finite : (∀ (m : moves G) → IsFinite (subsequent-round G m)) → IsFinite G

record FiniteGame : Set₁ where
  field
    playGame : Game
    isFinite : IsFinite playGame
open FiniteGame

{-
  The Hypergame has the following rules:
  1. In the first round of the hypergame, you can choose any finite game G.
  2. In the subsequent rounds, play proceeds as if you were playing the game G that you picked in the
     first round. The Hypergame concludes once G is over.

  Defining Hypergame would run into size issues if we didn't enable  `--type-in-type`.
-}

Hypergame : Round
Hypergame = record { moves = FiniteGame ; subsequent-round = λ fg → playGame fg }

{- 
  The Hypergame is a finite game, since no matter what move you make in the first round, the game that
  you end up playing in the subsequent rounds is itself finite.
-}

isFinite-Hypergame : IsFinite Hypergame
isFinite-Hypergame = all-subsequent-rounds-are-finite isFinite

finite-Hypergame : FiniteGame
finite-Hypergame = record { playGame = Hypergame ; isFinite = isFinite-Hypergame }

{-
  But now consider the following strategy:
  1. In the first round of Hypergame, I have to pick a finite game G to play. We've just proved that
     Hypergame is a finite game , so I can pick G as Hypergame itself.
  2. On the next round, I'm playing Hypergame again, so I have to pick a finite game G to play.
     I pick Hypergame again.
  3. I continue picking Hypergame in every round...
  
  This sequence of moves is infinite. Hence Hypergame is not a finite game after all!
-}

isInfinite-Hypergame : IsFinite Hypergame → ⊥
isInfinite-Hypergame (game-is-over x) = x finite-Hypergame
isInfinite-Hypergame (all-subsequent-rounds-are-finite x) = isInfinite-Hypergame (x finite-Hypergame)

{-
  We have established that Hypergame is finite, and then that Hypergame is not finite, a contradiction.
-}

paradox : ⊥
paradox = isInfinite-Hypergame isFinite-Hypergame

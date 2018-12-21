module Minimax

import Debug.Trace

import Data.Fin
--import Data.Fin.Extra
import Data.Vect

import Utils

%default partial

finToNatWeakenNeutral : {n : Fin m} -> finToNat (weaken n) = finToNat n
finToNatWeakenNeutral {n=FZ} = Refl
finToNatWeakenNeutral {m=S (S _)} {n=FS _} = cong finToNatWeakenNeutral

public export
data Estimation = PO | DR | PX

export
Show Estimation where
  show PO = "PO"
  show PX = "PX"
  show DR = "DR"

export total
Eq Estimation where
  (==) PO PO = True
  (==) DR DR = True
  (==) PX PX = True
  (==) _  _  = False

export total
Ord Estimation where
  compare PO PO = EQ
  compare DR DR = EQ
  compare PX PX = EQ
  compare DR PX = LT
  compare DR PO = GT  
  compare PO _  = LT
  compare PX _  = GT

public export
data GameTree : Type where
  GTree : (pos : Position)     -> 
          (e : Estimation)     -> 
          (field : GameField)  -> 
          (ts : List GameTree) -> GameTree

total public export
lastIndex : Vect (S len) elem -> Fin (S len)
lastIndex {len = Z} [x] = FZ
lastIndex {len = (S k)} (x::xs) = FS $ lastIndex xs

-- natToFin' : (i, n : Nat) -> LT i n -> Fin n

public export
possibleMoves : Player -> GameField -> List (Position, GameField)
possibleMoves player field = possibleMovesHelper (lastIndex field) where
  pair : Position -> (Position, GameField)
  pair pos = (pos, updateAt pos (const $ P player) field)
  -- possibleMovesHelper : Fin n -> LTE n FieldSize -> List (Position, GameField)
  possibleMovesHelper : Position -> List (Position, GameField)
  possibleMovesHelper FZ =
    if Blank == index FZ field
       then [pair FZ]
       else []
  possibleMovesHelper pos@(FS npos) = 
    let
      rest = possibleMovesHelper $ weaken npos
    in
      if Blank == index pos field
         then pair pos :: rest
         else rest

opByPlayer : Player -> Estimation -> Estimation -> Bool
opByPlayer p = if p == X then (>) else (<)

bestForOpponentP : Player -> Estimation -> Estimation -> Estimation
bestForOpponentP player e e' = let op = opByPlayer (nextPlayer player) in if e `op` e' then e else e'

worstP : Player -> Estimation -> Estimation -> Estimation
worstP player e e' = let op = opByPlayer player in if e `op` e' then e' else e

bestP : Player -> Estimation -> Estimation -> Estimation
bestP player e e' = let op = opByPlayer player in if e `op` e' then e else e'

bestAbsP : Player -> Estimation
bestAbsP p = if p == X then PX else PO

worstAbsP : Player -> Estimation
worstAbsP p = if p == X then PO else PX

export
minimax : Player -> GameField -> Estimation
minimax player field = 
  case checkMoveResult field player of
    ResultWon => if player == X then PX else PO
    ResultDraw => DR
    NextMove => fromEither $ foldlM (\acc, (_, gamefield) => 
                                           let acc' = acc `worst` (minimax nextp gamefield)
                                           in if worstAbs == acc' then Left acc' else Right acc'
                                    )
                                    bestAbs (possibleMoves nextp field)
                -- foldr (\(_, gamefield), e => e `worst` (minimax nextp gamefield))
                --        bestAbs (possibleMoves nextp field)
  where
    nextp : Player
    nextp = nextPlayer player
    bestAbs : Estimation
    bestAbs = bestAbsP player
    worstAbs : Estimation
    worstAbs = worstAbsP player
    bestForOpponent : Estimation -> Estimation -> Estimation
    bestForOpponent = bestForOpponentP player
    worst : Estimation -> Estimation -> Estimation
    worst e e' = worstP player e e'
    best : Estimation -> Estimation -> Estimation
    best = bestP player

export
runMinimax : Player -> GameField -> Position
runMinimax player field = bestMove $ possibleMoves player field where
  best : (Position, Estimation) -> (Position, Estimation) -> (Position, Estimation)
  best m@(_, e) m'@(_, e') = let op = opByPlayer player in if e `op` e' then m else m'
  -- worst : Estimation
  -- worst = if player == X then PO else PX
  bestMove : List (Position, GameField) -> Position
  bestMove mvs = 
    case emvs of
         [] => ?never_here
         (x :: xs) => fst (foldr (\est, acc => acc `best` est) x xs)
    where
      emvs : List (Position, Estimation)
      emvs = map (\(pos, field) => (pos, minimax player field)) mvs
      

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
 
 

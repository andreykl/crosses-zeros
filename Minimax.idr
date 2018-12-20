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

export
minimax : Player -> Position -> GameField -> (Position, Estimation)
minimax player pos field = 
  case checkMoveResult field player of
    ResultWon => let e = if player == X then PX else PO in (pos, e)
    ResultDraw => (pos, DR)
    NextMove => 
      (pos, foldr (\(p, gamefield), e =>
              case minimax nextp p gamefield of
                (_, e') => e `best` e')
            DR (possibleMoves nextp field))
  where
    best : Estimation -> Estimation -> Estimation
    best e e' = let op = opByPlayer player in if e `op` e' then e else e'
    nextp : Player
    nextp = nextPlayer player

export
runMinimax : Player -> GameField -> Position
runMinimax player field = bestMove $ possibleMoves player field where
  best : (Position, Estimation) -> (Position, Estimation) -> (Position, Estimation)
  best m@(_, e) m'@(_, e') = let op = opByPlayer player in if e `op` e' then m else m'
  bestMove : List (Position, GameField) -> Position
  bestMove = fst . (foldr (\(pos, field), acc => acc `best` (minimax player pos field)) (FZ, DR))

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
 

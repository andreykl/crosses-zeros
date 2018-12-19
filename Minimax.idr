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

export
minimax : Player -> GameField -> (Position, Estimation)
minimax player field = 
  let
    tmp = trace "we are here" 1
    ts = map estimate $ possibleMoves player field
    (pos, e) = the (Position, Estimation) $
                   (case nonEmpty ts of
                      Yes (IsNonEmpty {xs=y::ys}) => getBestEst (y::ys)
                      No contra => trace "this should not happen ever" ?never_here) -- this should not happen
  in 
    (pos, e)
  where
    op : Estimation -> Estimation -> Bool
    op = if player == X then (>) else (<)
    getBestEst : (ts : List (Position, Estimation)) -> 
                 {auto prf : NonEmpty ts} -> (Position, Estimation)
    getBestEst (x :: xs) {prf = IsNonEmpty} = 
      foldr (\(pos, e), (pos', e') => if e `op` e' then (pos, e) else (pos', e')) x xs
    estimate : (Position, GameField) -> (Position, Estimation)
    estimate (pos', field') = case checkMoveResult field' player of
      ResultWon => let e' = if player == X then PX else PO in (pos', e')
      ResultDraw => (pos', DR)
      NextMove => let (_, e') = minimax (nextPlayer player) field' in (pos', e')

export
runMinimax : Player -> GameField -> Position
runMinimax player field = 
  let (pos, _) = minimax player field in pos

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:
 

module Minimax

import Data.Fin
import Data.Vect

import Utils

public export
data Estimation = PO | DR | PX

export
Eq Estimation where
  (==) PO PO = True
  (==) DR DR = True
  (==) PX PX = True
  (==) _  _  = False

export
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
  GTree : (pos : Position) -> (e : Estimation) -> (field : GameField) -> 
          (ts : List GameTree) -> GameTree

lastIndex : Vect (S len) elem -> Fin (S len)
lastIndex {len = Z} [x] = FZ
lastIndex {len = (S k)} (x::xs) = FS $ lastIndex xs

possibleMoves : Player -> GameField -> List (Position, GameField)
possibleMoves player field = possibleMovesHelper (lastIndex field) where
  pair : Position -> (Position, GameField)
  pair pos = (pos, updateAt pos (const $ P player) field)
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

-- total
minimax : Player -> GameField -> GameTree
minimax player field = 
  let
    ts = map estimate $ possibleMoves player field
    (pos, e) = the (Position, Estimation) $
                   (case nonEmpty ts of
                      Yes (IsNonEmpty {xs=x::xs}) => getBestEst (x::xs)
                      No contra => ?never_here) -- this should not happen
  in 
    GTree pos e field ts
  where
    op : Estimation -> Estimation -> Bool
    op = if player == X then (>) else (<)
    getBestEst : (ts : List GameTree) -> 
                 {auto prf : NonEmpty ts} -> (Position, Estimation)
    getBestEst ((GTree p1 e1 _ _) :: xs) {prf = IsNonEmpty} = 
      foldr (\(GTree pos e _ _), (pos', e') => if e `op` e' then (pos, e) else (pos', e')) (p1, e1) xs
    estimate : (Position, GameField) -> GameTree
    estimate (pos', field') = case checkMoveResult field' player of
      ResultWon => let res = if player == X then PX else PO in GTree pos' res field' []
      ResultDraw => GTree pos' DR field' []
      NextMove => 
        let 
          (GTree p e f ts) = minimax (nextPlayer player) field'
        in
          (GTree pos' e field' ts)

export --total
runMinimax : Player -> GameField -> Position
runMinimax player field = 
  let (GTree pos _ _ _) = minimax player field in pos

 

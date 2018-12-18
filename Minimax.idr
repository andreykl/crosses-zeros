module Minimax

import Data.Fin
import Data.Vect

import Utils

data Estimation = PO | DR | PX

Eq Estimation where
  (==) PO PO = True
  (==) DR DR = True
  (==) PX PX = True
  (==) _  _  = False

Ord Estimation where
  compare PO PO = EQ
  compare DR DR = EQ
  compare PX PX = EQ
  compare DR PX = LT
  compare DR PO = GT  
  compare PO _  = LT
  compare PX _  = GT

EstPos : Type
EstPos = (Estimation, Position)

Ord Player where
  compare X X = EQ
  compare O O = EQ
  compare X _ = GT
  compare O _ = LT

data TreeEstimation = Estimated | NotEstimated

data GameTree : Type where
  GTree : Position -> Estimation -> GameField -> List GameTree -> GameTree
  
-- Functor GameTree where
--  map f (GTree pos est a xs) = ?hole

lastIndex : Vect (S len) elem -> Fin (S len)
lastIndex {len = Z} [x] = FZ
lastIndex {len = (S k)} (x::xs) = FS $ lastIndex xs

bestEst : Player -> Estimation -> Estimation -> Estimation
bestEst p e e' = let op = if p == X then (>) else (<) in if e `op` e' then e else e'

minimax : Player -> GameTree -> GameTree
minimax player tree@(GTree pos DR field []) = 
  case checkMoveResult field player of
    ResultWon => let res = if player == X then PX else PO in GTree pos res field []
    ResultDraw => tree
    NextMove => let (e, estTreeList) = foldr foldingf (DR, []) possibleMoves in GTree pos e field estTreeList
  where
    nplayer : Player
    nplayer = nextPlayer player
    best : Estimation -> Estimation -> Estimation
    best = bestEst player
    foldingf : GameTree {-not estimated-} -> (Estimation, List GameTree {-estimated-}) -> (Estimation, List GameTree{-estimated-})
    foldingf tree (e, xs) =
      let
        t@(GTree _ e' _ _) = minimax nplayer tree
      in (best e' e, t :: xs)
          
    upWCurPlayer : Cell -> Cell
    upWCurPlayer = const $ P player 
    singletonTree : Position -> GameTree
    singletonTree pos = GTree pos DR (updateAt pos upWCurPlayer field) []
    possibleMovesHelper : Position -> List GameTree
    possibleMovesHelper FZ =
      if Blank == index FZ field
         then [singletonTree FZ]
         else []
    possibleMovesHelper pos@(FS npos) = 
      let
        rest = possibleMovesHelper $ weaken npos
      in
        if Blank == index pos field
           then singletonTree pos :: rest
           else rest
    possibleMoves : List GameTree
    possibleMoves = possibleMovesHelper (lastIndex field)
minimax player (GTree _ _ _ _) = ?never_here_1


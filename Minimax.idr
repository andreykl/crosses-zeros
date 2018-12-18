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

export
Ord Player where
  compare X X = EQ
  compare O O = EQ
  compare X _ = GT
  compare O _ = LT

data TreeEstimation = Estimated | NotEstimated

public export
data GameTree : Type where
  GTree : Position -> Estimation -> GameField -> List GameTree -> GameTree
  
-- Functor GameTree where
--  map f (GTree pos est a xs) = ?hole

lastIndex : Vect (S len) elem -> Fin (S len)
lastIndex {len = Z} [x] = FZ
lastIndex {len = (S k)} (x::xs) = FS $ lastIndex xs

bestEst : Player -> Estimation -> Estimation -> Estimation
bestEst p e e' = let op = if p == X then (>) else (<) in if e `op` e' then e else e'

possibleMoves : Player -> GameField -> List GameTree
possibleMoves player field = possibleMovesHelper (lastIndex field) where
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

-- total
minimax : Player -> GameTree -> GameTree
minimax player tree@(GTree pos DR field []) = 
  case checkMoveResult field player of
    ResultWon => let res = if player == X then PX else PO in GTree pos res field []
    ResultDraw => tree
    NextMove => 
      let 
        (e, estTreeList) = foldr foldingf (DR, []) $ possibleMoves player field 
      in 
        GTree pos e field estTreeList
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
minimax player (GTree _ _ _ _) = ?never_here_1

export --total
runMinimax : Player -> GameField -> Position
runMinimax p field = 
  let
    ts = map (minimax p) (possibleMoves p field)
  in case nonEmpty ts of
       Yes (IsNonEmpty {xs=x::xs}) => selectbest p (x::xs)
       No contra => ?never_here_2
  where
    selectbest : Player -> (ts : List GameTree) -> {auto prf : NonEmpty ts} -> Position
    selectbest p ts = 
      let 
        (GTree pos _ _ _ ) = foldr (\t, tacc => best t tacc) (head ts) (tail ts) 
      in
        pos
      where
        op : Estimation -> Estimation -> Bool
        op = if p == X then (>) else (<)
        best : GameTree -> GameTree -> GameTree
        best t@(GTree _ e _ _) t'@(GTree _ e' _ _) = if e `op` e' then t else t'

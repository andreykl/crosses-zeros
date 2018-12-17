module Minimax

import Data.Fin
import Data.Vect

import Utils

Estimation : Type
Estimation = Player

EstPos : Type
EstPos = (Estimation, Position)

MEstPos : Type
MEstPos = Maybe EstPos

Ord Player where
  compare X X = EQ
  compare O O = EQ
  compare X _ = GT
  compare O _ = LT

data TreeEstimation = Estimated | NotEstimated

data GameTree : Type where
  GTree : MEstPos -> GameField -> List GameTree -> GameTree
  
-- Functor GameTree where
--  map f (GTree pos est a xs) = ?hole

lastIndex : Vect (S len) elem -> Fin (S len)
lastIndex {len = Z} [x] = FZ
lastIndex {len = (S k)} (x::xs) = FS $ lastIndex xs

--- we need always estimated value if we have it
mepBest : Player -> MEstPos -> MEstPos -> MEstPos
mepBest p m@(Just (e, _)) m'@(Just (e', _)) = let op = if p == X then (>) else (<) in if e `op` e' then m else m'
mepBest p Nothing m' = m'
mepBest p m Nothing = m

-- draw is lost... just a bit less to write, but actually it will play wrongly
minimax : Player -> GameTree -> GameTree
minimax player (GTree Nothing field []) = 
  let
    (ep, estTreeList) = foldr foldingf (Nothing, []) possibleMoves
      -- case checkMoveResult field player of
      --                     ResultWon => (Just (player, (the (Fin FieldSize) FZ)), [])
      --                     ResultDraw => (Just (nextPlayer player, (the (Fin FieldSize) FZ)), [])
      --                     NextMove => 
  in
    (GTree ep field estTreeList)
  where
    nplayer : Player
    nplayer = nextPlayer player
    mepBestP : MEstPos -> MEstPos -> MEstPos
    mepBestP = mepBest player
    foldingf : GameTree {-not estimated-} -> (MEstPos, List (Position, GameTree {-estimated-})) -> (MEstPos, List GameTree{-estimated-})
    foldingf tree@(GTree _{-empty-} field _{-empty-}) (mep, xs) =
      let
        mvr = checkMoveResult field player
        (mep', t) = moveResultToFoldType mvr
      in ?ho--(mepBestP mep mep', t :: xs)
        where 
          moveResultToFoldType : MoveResult -> (MEstPos, GameTree)
          moveResultToFoldType NextMove = let t1@(GTree mep1 _ _) = minimax nplayer tree in (mep1, t1)
          moveResultToFoldType ResultWon = (Just (player, ?pos), tree)
          moveResultToFoldType ResultDraw = (Just (nplayer, ?posd), tree)
          
    upWCurPlayer : Cell -> Cell
    upWCurPlayer = const $ P player 
    singletonTree : Position -> GameTree
    singletonTree pos = GTree Nothing (updateAt pos upWCurPlayer field) []
    possibleMovesHelper : Position -> List (Position, GameTree)
    -- possibleMovesHelper FZ =
    --   if Blank == index FZ field
    --      then [singletonTree FZ]
    --      else []
    -- possibleMovesHelper pos@(FS npos) = 
    --   let
    --     rest = possibleMovesHelper $ weaken npos
    --   in
    --     if Blank == index pos field
    --        then singletonTree pos :: rest
    --        else rest
    possibleMoves : List (Position, GameTree)
    possibleMoves = possibleMovesHelper (lastIndex field)
minimax player (GTree (Just _) _ _) = ?never_here_1
minimax player (GTree _ _ xs) = ?never_here_2


module Lib

import Data.Vect
import Data.Fin

%default total

data Forever = More Forever

partial
forever : Forever
forever = More forever

data Player = X | O

Eq Player where
  X == X = True
  O == O = True
  _ == _ = False

Show Player where
  show X = "X"
  show O = "O"

data Cell = Blank | P Player

Eq Cell where
  (==) Blank Blank  = True
  (==) (P p) (P p') = p == p'
  (==) _     _      = False

Show Cell where
  show Blank = " "
  show (P p) = show p

-- This is the only suported size!
Rows : Nat
Rows = 3

-- This is the only suported size!
Cols : Nat
Cols = 3

FieldSize : Nat
FieldSize = Rows * Cols

GameField : Type
GameField = Vect FieldSize Cell

rowIndex : Nat -> Nat -> Fin FieldSize
rowIndex r c = 
  case natToFin (c + r * Cols) FieldSize of
    Nothing => FZ
    (Just x) => x

colIndex : Nat -> Nat -> Fin FieldSize
colIndex = flip rowIndex

data FinishedState = SWon Player | SDraw

data GameState = SMoveOf Player | SFinished FinishedState | SNotRunning

data MoveResult : Type where
  NextMove : MoveResult
  ResultWon : MoveResult
  ResultDraw : MoveResult

nextPlayer : Player -> Player
nextPlayer X = O
nextPlayer O = X

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (p : Player) -> GameCmd () SNotRunning (const (SMoveOf p))
  Move : {p : Player} -> Fin FieldSize -> 
         GameCmd MoveResult (SMoveOf p) 
                 (\res => case res of
                            NextMove => SMoveOf (nextPlayer p)
                            ResultWon => SFinished (SWon p)
                            ResultDraw => SFinished SDraw)
  Won : (p : Player) -> GameCmd () (SFinished (SWon p)) (const SNotRunning)
  Draw : GameCmd () (SFinished SDraw) (const SNotRunning)
  
  ShowState : GameCmd () st (const st)
  ReadMove : GameCmd (Fin FieldSize) (SMoveOf p) (const (SMoveOf p))
  
  Pure : (res : a) -> GameCmd a (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn -> 
          ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
          GameCmd b state1 state3_fn

namespace GameLoop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn -> 
            ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
            GameLoop b state1 state3_fn
    Exit : GameLoop () SNotRunning (const SNotRunning)

gameLoop : GameLoop () (SMoveOf p) (const SNotRunning)
gameLoop {p} = do
  ShowState
  move <- ReadMove
  mres <- Move move
  case mres of
    NextMove => gameLoop
    ResultWon => do Won p
                    ShowState
                    Exit
    ResultDraw => do Draw
                     ShowState
                     Exit

crossesZeros : GameLoop () SNotRunning (const SNotRunning)
crossesZeros = do NewGame X
                  gameLoop

data Game : GameState -> Type where
  StartGame : Game SNotRunning
  WinGame : (p : Player) -> Game (SFinished (SWon p))
  DrawGame : Game (SFinished SDraw)
  InProgress : (p : Player) -> GameField -> Game (SMoveOf p)
  EndGame : Game prev -> Game SNotRunning

Show (Game g) where
  show (EndGame g)= "Game is finished. " ++ show g
  show StartGame = "Game to start"
  show (WinGame p) = "Player " ++ show p ++ " won the game."
  show DrawGame = "It's a draw."
  show (InProgress p xs) = drowField where
    drowRow : (Fin 3) -> String
    drowRow row =
      let
        rInd = rowIndex (finToNat row)
      in
        " " ++ show (index (rInd 0) xs) ++ " | " ++ show (index (rInd 1) xs) ++ " | " ++ show (index (rInd 2) xs) ++ " "
    drowField : String
    drowField = "---+---+---\n" ++
                drowRow 0 ++ "\n" ++
                "---+---+---" ++ "\n" ++
                drowRow 1 ++ "\n" ++
                "---+---+---" ++ "\n" ++
                drowRow 2 ++ "\n"
                
data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> (Game (state_fn res)) -> GameResult ty state_fn

ok : (res : ty) -> (Game (state_fn res)) -> IO (GameResult ty state_fn)
ok res instate = pure (OK res instate)

playerCell : Player -> Cell -> Bool
playerCell p (P pl) = pl == p
playerCell _ Blank  = False

checkCols : Player -> GameField -> Bool
checkCols p xs = any id (map (all (playerCell p)) rows) where
  rows : List (List Cell)
  rows = [[index (rowIndex r c) xs | c <- [0..2]] | r <- [0..2]]

checkRows : Player -> GameField -> Bool
checkRows p xs = any id (map (all (playerCell p)) rows) where
  rows : List (List Cell)
  rows = [[index (colIndex c r) xs | r <- [0..2]] | c <- [0..2]]

checkDiags : Player -> GameField -> Bool
checkDiags p xs = any id (map (all (playerCell p)) diags) where
  diags : List (List Cell)
  diags = 
    let
      xsInd = flip index xs
    in map (map xsInd) (the (List (List (Fin 9))) [[0, 4, 8], [2, 4, 6]])

noMoreBlank : GameField -> Bool
noMoreBlank = all (/= Blank)

checkMoveResult : GameField -> Player -> MoveResult
checkMoveResult xs p = 
  if (checkCols p xs) || 
     (checkRows p xs) ||
     (checkDiags p xs)
  then ResultWon
  else if noMoreBlank xs
       then ResultDraw
       else NextMove

runCmd : Forever -> Game instate -> GameCmd a instate state_fn -> IO (GameResult a state_fn)
runCmd _ instate (NewGame p) = ok () (InProgress p $ replicate FieldSize Blank)
runCmd _ (InProgress p xs) (Move pos) = do
  let xs' = updateAt pos (const $ P p) xs
  case checkMoveResult xs' p of
    NextMove => ok NextMove (InProgress (nextPlayer p) xs')
    ResultWon => ok ResultWon (WinGame p)
    ResultDraw => ok ResultDraw DrawGame
runCmd _ instate (Won p) = ok () (EndGame instate)
runCmd _ instate Draw = ok () (EndGame instate)
runCmd _ instate ShowState = do printLn instate; ok () instate
runCmd (More frvr) instate@(InProgress p xs) ReadMove = do
  putStr ("Move of " ++ show p ++ ": ")
  ans <- getLine
  case unpack ans of
    [cpos] => if isDigit cpos
              then
                case integerToFin (cast (ord cpos - ord '0')) FieldSize of
                  Nothing => do putStrLn "Invalid input. Please use numbers 0-8 to identify needed cell."
                                runCmd frvr instate (do ShowState; ReadMove)
                  (Just mv) => case index mv xs of
                                 Blank  => ok mv instate
                                 (P pl) => do putStrLn $ "Invalid input. Cell is not free (" ++ show pl ++ ")."
                                              runCmd frvr instate (do ShowState; ReadMove)
              else do
                putStrLn "Invalid input. Please use numbers 0-8 to identify needed cell."
                runCmd frvr instate (do ShowState; ReadMove)
    _      => runCmd frvr instate (do ShowState; ReadMove)
runCmd _ instate (Pure res) = ok res instate
runCmd frvr instate (cmd >>= cont) = do 
  (OK res' st') <- runCmd frvr instate cmd
  runCmd frvr st' (cont res')

runLoop : Forever -> Game instate -> GameLoop a instate state_fn -> IO a
runLoop (More frvr) inst (x >>= f) = do (OK res' st') <- runCmd frvr inst x
                                        runLoop frvr st' (f res')
runLoop _ inst Exit = pure ()


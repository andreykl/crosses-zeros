module Lib

import Data.Vect

%default total

data Forever = More Forever

partial
forever : Forever
forever = More forever

data Player = X | O

data Cell = Blank | P Player

FieldSize : Nat
FieldSize = 9

GameField : Type
GameField = Vect FieldSize Cell

data GameState = SMoveOf Player | SWon Player | SDraw | SNotRunning

data MoveResult : Type where 
  NextMove : MoveResult
  ResultWon : MoveResult
  ResultDraw : MoveResult

next : Player -> Player
next X = O
next O = X

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (p : Player) -> GameCmd () SNotRunning (const (SMoveOf p))
  Move : {p : Player} -> Fin FieldSize -> 
         GameCmd MoveResult (SMoveOf p) 
                 (\res => case res of
                            NextMove => SMoveOf (next p)
                            ResultWon => SWon p
                            ResultDraw => SDraw)
  Won : (p : Player) -> GameCmd () (SWon p) (const SNotRunning)
  Draw : GameCmd () SDraw (const SNotRunning)
  
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

runCmd : Forever -> GameCmd a instate state_fn -> IO a
runCmd x y = ?runCmd_rhs

runLoop : Forever -> GameLoop a instate state_fn -> IO a
runLoop (More frvr) (cmd >>= cont) = do res <- runCmd frvr cmd
                                        runLoop frvr (cont res)
runLoop _ Exit = pure ()

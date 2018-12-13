module Lib

import Data.Vect

data Player = X | O

data Cell = Blank | P Player

FieldSize : Nat
FieldSize = 9

GameField : Type
GameField = Vect FieldSize Cell

data GameState = SMoveOf Player | SWon Player | SDraw | SNotRunning

data MoveResult : Type where 
  NextMove : (next : Player) -> MoveResult
  ResultWon : (p : Player) -> MoveResult
  ResultDraw : MoveResult

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  Move : Player -> Fin FieldSize -> 
         GameCmd MoveResult (SMoveOf cp) 
                 (\res => case res of
                            (NextMove next) => SMoveOf next
                            (ResultWon p) => SWon p
                            ResultDraw => SDraw)
  Won : GameCmd () (SWon p) (const SNotRunning)
  Draw : GameCmd () SDraw (const SNotRunning)
  
  ShowState : GameCmd () st (const st)
  ReadMove : GameCmd (Fin FieldSize) st (const st)
  
  Pure : a -> GameCmd a st (const st)
  (>>=) : GameCmd a state1 state2_fn -> 
          ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
          GameCmd b state1 state3_fn

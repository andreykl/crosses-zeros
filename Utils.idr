module Utils

import Data.Vect
import Data.Fin

%default total

public export
data Forever = More Forever

export partial
forever : Forever
forever = More forever

public export
data Player = X | O

export
Eq Player where
  X == X = True
  O == O = True
  _ == _ = False

export
Show Player where
  show X = "X"
  show O = "O"

public export
data Cell = Blank | P Player

export
Eq Cell where
  (==) Blank Blank  = True
  (==) (P p) (P p') = p == p'
  (==) _     _      = False

export
Show Cell where
  show Blank = " "
  show (P p) = show p

-- This is the only suported size!
public export
Rows : Nat
Rows = 3

-- This is the only suported size!
public export
Cols : Nat
Cols = 3

public export
FieldSize : Nat
FieldSize = Rows * Cols

public export
Position : Type
Position = Fin FieldSize

public export
GameField : Type
GameField = Vect FieldSize Cell

export
rowIndex : Nat -> Nat -> Fin FieldSize
rowIndex r c = 
  case natToFin (c + r * Cols) FieldSize of
    Nothing => FZ
    (Just x) => x

export
colIndex : Nat -> Nat -> Fin FieldSize
colIndex = flip rowIndex

public export
data MoveResult : Type where
  NextMove : MoveResult
  ResultWon : MoveResult
  ResultDraw : MoveResult

export
playerCell : Player -> Cell -> Bool
playerCell p (P pl) = pl == p
playerCell _ Blank  = False

export
checkCols : Player -> GameField -> Bool
checkCols p xs = any id (map (all (playerCell p)) rows) where
  rows : List (List Cell)
  rows = [[index (rowIndex r c) xs | c <- [0..2]] | r <- [0..2]]

export
checkRows : Player -> GameField -> Bool
checkRows p xs = any id (map (all (playerCell p)) rows) where
  rows : List (List Cell)
  rows = [[index (colIndex c r) xs | r <- [0..2]] | c <- [0..2]]

export
checkDiags : Player -> GameField -> Bool
checkDiags p xs = any id (map (all (playerCell p)) diags) where
  diags : List (List Cell)
  diags = 
    let
      xsInd = flip index xs
    in map (map xsInd) (the (List (List (Fin 9))) [[0, 4, 8], [2, 4, 6]])

export
noMoreBlank : GameField -> Bool
noMoreBlank = all (/= Blank)

export
checkMoveResult : GameField -> Player -> MoveResult
checkMoveResult xs p = 
  if (checkCols p xs) || 
     (checkRows p xs) ||
     (checkDiags p xs)
  then 
    ResultWon
  else 
    if noMoreBlank xs
       then ResultDraw
       else NextMove

export
nextPlayer : Player -> Player
nextPlayer X = O
nextPlayer O = X

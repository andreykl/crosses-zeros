module Main

import Data.Vect
import Specdris.Spec

import Utils
import Minimax

gf1 : GameField
gf1 = [
  P X, P X, P O,
  P X, P X, P O,
  P O, P O, Blank
]

gf2 : GameField
gf2 = [
  P X, Blank, P O,
  P X, P X, P O,
  P O, P O, Blank
]

gf9 : GameField
gf9 = [
  Blank, Blank, Blank,
  Blank, Blank, Blank,
  Blank, Blank, Blank
]

gfDraw : GameField
gfDraw = [
  P O, P X, P X,
  P X, P X, P O,
  P O, P O, P X
]

gf1X : GameField
gf1X = [
  P X, P X, P O,
  P X, P X, P O,
  P O, P O, P X
]

gf1O : GameField
gf1O = [
  P X, P X, P O,
  P X, P X, P O,
  P O, P O, P O
]

gf2BO : GameField
gf2BO = [
  P X, Blank, P O,
  P X, P X, P O,
  P O, P O, P O
]

gf2BX : GameField
gf2BX = [
  P X, Blank, P O,
  P X, P X, P O,
  P O, P O, P X
]

gf2OB : GameField
gf2OB = [
  P X, P O, P O,
  P X, P X, P O,
  P O, P O, Blank
]

gf2XB : GameField
gf2XB = [
  P X, P X, P O,
  P X, P X, P O,
  P O, P O, Blank
]

Show Position where
  show p = show $ finToNat p
  
PMType : Type
PMType = List (Position, GameField)

main : IO ()
main = spec $ do
  describe "$ possibleMoves tests" $ do
    describe "this is 1 step test" $ do
      it "adds one X to the only empty position on field" $ do
        possibleMoves X gf1 `shouldBe` [(8, gf1X)]
      it "adds one O to the only empty position on field" $ do
        possibleMoves O gf1 `shouldBe` [(8, gf1O)]
      it "adds one X to each of 2 empty spaces, one by one" $ do
        possibleMoves X gf2 `shouldBe` [(8, gf2BX), (1, gf2XB)]
      it "adds one O to each of 2 empty spaces, one by one" $ do
        possibleMoves O gf2 `shouldBe` [(8, gf2BO), (1, gf2OB)]
    describe "amount of cases" $ do
      it "adds X to the only empty space" $ do
        (length $ possibleMoves X gf1) `shouldBe` 1
      it "adds X to each of two empty spaces" $ do
        (length $ possibleMoves X gf2) `shouldBe` 2
      it "adds X to each of nine empty spaces" $ do
        (length $ possibleMoves X gf9) `shouldBe` 9
      it "adds O to each of nine empty spaces" $ do
        (length $ possibleMoves O gf9) `shouldBe` 9
      it "tryes to add moves to full field" $ do
        (length $ possibleMoves X gfDraw) `shouldBe` 0
  describe "$ last index" $ do
    it "takes last index of GameField" $ do
      finToNat (lastIndex gf1) `shouldBe` (FieldSize - 1)

-- Local Variables:
-- idris-load-packages: ("specdris")
-- End:

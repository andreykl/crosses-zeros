module Main

import Lib
import Utils

main : IO ()
main = runLoop forever StartGame crossesZeros

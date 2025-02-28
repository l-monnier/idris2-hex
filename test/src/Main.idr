module Main

import Hedgehog

import Test.Hex

%default total

main : IO ()
main = test [Hex.props]

module Main

import Hedgehog

import Test.Hex
import Test.WebColors

%default total

main : IO ()
main = test [ Hex.props
            , WebColors.props
            ]

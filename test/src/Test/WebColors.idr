module Test.WebColors

import Hedgehog

import Data.Hex
import Data.Hex.WebColors

import Data.Refined.String
import Data.String

%default total

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

private
strGen : Gen String
strGen = do
  b <- bool
  let len = the Nat $ if b then 6 else 8
  xs <- list (linear len len) hexit
  pure $ "#" <+> pack xs

--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

private
testString6 : Property
testString6 = property1 $
   fromString "#ab42cd"
     === MkWebColor (HexA, HexB) (Hex4, Hex2) (HexC, HexD) Nothing

private
testString8 : Property
testString8 = property1 $
   fromString "#6af24eb3"
     === MkWebColor (Hex6, HexA) (HexF, Hex2) (Hex4, HexE) (Just (HexB, Hex3))

--------------------------------------------------------------------------------
-- Property tests
--------------------------------------------------------------------------------

public export
props : Group
props = MkGroup "Test `Web Colors`"
  [ ("Prop string 6", testString6)
  , ("Prop string 8", testString8)
  ]

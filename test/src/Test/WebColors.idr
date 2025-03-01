module Test.WebColors

import Hedgehog

import Data.Hex
import Data.Hex.WebColors

import Data.Refined.String
import Data.String

%default total

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

private
testString6 : Property
testString6 = property1 $
   fromString "#ab42cd"
     === MkWebColor (HexA, HexB) (Hex4, Hex2) (HexC, HexD) Nothing

public export
props : Group
props = MkGroup "Test `Web Colors`"
  [ ("Prop string 6", testString6)
  ]

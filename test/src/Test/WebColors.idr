module Test.WebColors

import Hedgehog

import Data.Hex
import Data.Hex.WebColors

import Data.List1
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
testString7 : Property
testString7 = property1 $
   fromString "#ab42cd"
     === MkWebColor (HexA, HexB) (Hex4, Hex2) (HexC, HexD) Nothing

private
testString9 : Property
testString9 = property1 $
   fromString "#6af24eb3"
     === MkWebColor (Hex6, HexA) (HexF, Hex2) (Hex4, HexE) (Just (HexB, Hex3))

private
testFromHex : Property
testFromHex = property1 $
   fromHex "a" "a42" "cd" Nothing
     === MkWebColor (Hex0, HexA) (HexF, HexF) (HexC, HexD) Nothing

private
testFromHexAlpha : Property
testFromHexAlpha = property1 $
   fromHex "cd" "F" "100" (Just "3F")
     === MkWebColor (HexC, HexD) (Hex0, HexF) (HexF, HexF) (Just (Hex3, HexF))

--------------------------------------------------------------------------------
-- Property tests
--------------------------------------------------------------------------------

private
propInvertible : Property
propInvertible = property $ do
  s <- forAll strGen
  case WebColors.fromStringMaybe s of
    Just hex => toUpper s === toString hex
    Nothing  => s === "This string shouldn't have been generated"

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

public export
props : Group
props = MkGroup "Test `Web Colors`"
  [ ("Prop string 7", testString7)
  , ("Prop string 9", testString9)
  , ("Test from hex", testFromHex)
  , ("Test from hex with alpha", testFromHexAlpha)
  , ("Prop invertible", propInvertible)
  ]

module Test.Hex

import Hedgehog

import Data.Hex

import Data.Refined.String
import Data.String

%default total

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

private
hex0 : Hex
hex0 = fromString "0"

private
hex10 : Hex
hex10 = fromString "10"

private
hex101 : Hex
hex101 = fromString "101"

private
integer0 : Integer
integer0 = 0

private
integer16 : Integer
integer16 = 16

private
integer257 : Integer
integer257 = 257

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

private
n0Gen : Gen Integer
n0Gen = integer (linear 0 10000)

private
n1Gen : Gen Integer
n1Gen = integer (linear 1 10000)

private
negGen : Gen Integer
negGen = integer (linear (-10000) (-1))

private
strGen : Gen String
strGen = map pack $ list (linear 1 10) hexit

--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

private
testHex0ToInteger : Property
testHex0ToInteger = property1 $
   cast hex0 === 0

private
testHex10ToInteger : Property
testHex10ToInteger = property1 $
  cast hex10 === 16

private
testHex101ToInteger : Property
testHex101ToInteger = property1 $
  cast hex101 === 257

private
testHexLeading0ToInteger : Property
testHexLeading0ToInteger = property1 $
  cast (fromString "0101") === 257

private
testHexLeading0Equals : Property
testHexLeading0Equals = property1 $
  (fromString "0101" == hex101) === True

--------------------------------------------------------------------------------
-- Property tests
--------------------------------------------------------------------------------

private
propInvertible : Property
propInvertible = property $ do
  x <- forAll n0Gen
  x === (the Integer $ cast $ the Hex $ cast x)

private
propInvertibleStr : Property
propInvertibleStr = property $ do
  str <- forAll strGen
  case fromStringMaybe str of
    Just hex => toUpper str === toString hex
    Nothing  => str === "This string shouldn't have been generated"

private
propIsoAdd : Property
propIsoAdd = property $ do
  x <- forAll n0Gen
  y <- forAll n0Gen
  x + y === (the Integer $ cast $ (the Hex (cast x) + the Hex (cast y)))

private
propIsoMult : Property
propIsoMult = property $ do
  x <- forAll n0Gen
  y <- forAll n0Gen
  x * y === (the Integer $ cast $ (the Hex (cast x) * the Hex (cast y)))

private
propIsoDiv : Property
propIsoDiv = property $ do
  x <- forAll n0Gen
  y <- forAll n1Gen
  div x y === (the Integer $ cast $ div (the Hex $ cast x) (the Hex $ cast y))

private
propIsoMinus : Property
propIsoMinus = property $ do
  x <- forAll n0Gen
  y <- forAll n0Gen
  max 0 (x - y) === (the Integer $ cast $ minus (the Hex $ cast x) (the Hex $ cast y))

private
propIsoMod : Property
propIsoMod = property $ do
  x <- forAll n0Gen
  y <- forAll n1Gen
  mod x y === (the Integer $ cast $ mod (the Hex $ cast x) (the Hex $ cast y))

private
propIsoEq : Property
propIsoEq = property $ do
  x <- forAll n0Gen
  y <- forAll n0Gen
  (x == y) === (the Hex (cast x) == the Hex (cast y))

private
propIsoOrd : Property
propIsoOrd = property $ do
  x <- forAll n0Gen
  y <- forAll n0Gen
  compare x y === compare (the Hex $ cast x) (the Hex $ cast y)

private
propNegTo0 : Property
propNegTo0 = property $ do
  x <- forAll negGen
  hex0 === the Hex (cast x)

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

public export
props : Group
props = MkGroup "Test `Hex`"
  [ ("Prop hex 0 to `Integer`", testHex0ToInteger)
  , ("Prop hex 10 to `Integer`", testHex10ToInteger)
  , ("Prop hex 101 to `Integer`", testHex101ToInteger)
  , ("Prop hex with leading 0 to `Integer`", testHexLeading0ToInteger)
  , ("Prop leading 0 do not change equality", testHexLeading0Equals)
  , ("Prop invertible", propInvertible)
  , ("Prop invertible `String`", propInvertibleStr)
  , ("Prop addition is isomorphic", propIsoAdd)
  , ("Prop division is isomorphic", propIsoDiv)
  , ("Prop modulos are isomorphic", propIsoMod)
  , ("Prop multiplication is isomorphic", propIsoMult)
  , ("Prop substraction is isomorphic", propIsoMinus)
  , ("Prop `Eq` is isomorphic", propIsoEq)
  , ("Prop `Ord` is isomorphic", propIsoOrd)
  , ("Prop negative integers converted to zero hex", propNegTo0)
  ]

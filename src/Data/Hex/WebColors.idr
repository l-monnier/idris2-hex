||| Web colours specified using hexadecimal colour codes.
module Data.Hex.WebColors

import Data.Hex
import Data.Refined.Integer
import Data.Refined.String
import Data.String
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import Derive.Prelude

%language ElabReflection
%default total

||| A  web color.
public export
data WebColor =
  MkWebColor
    (Symbol, Symbol)
    (Symbol, Symbol)
    (Symbol, Symbol)
    (Maybe (Symbol, Symbol))

%runElab derive "WebColor" [Eq, Show]

||| Returns the `Hex` value for the red color.
public export
red : WebColor -> Hex
red (MkWebColor r _ _ _) = cast r

||| Returns the `Hex` value for the green color.
public export
green : WebColor -> Hex
green (MkWebColor _ g _ _) = cast g

||| Returns the `Hex` value for the blue color.
public export
blue : WebColor -> Hex
blue (MkWebColor _ _ b _) = cast b

||| Returns the `Hex` value for the alpha channel.
public export
alpha : WebColor -> Maybe Hex
alpha (MkWebColor _ _ _ a) = map cast a

||| Converts a `List` of 6 elements to a `WebColor`.
private
list6ToWebColor :
     (xs : List Char)
  -> {auto 0 prf1 : 6 = length xs}
  -> {auto prf2 : All Hexit xs}
  -> WebColor
list6ToWebColor
  (r1 :: r2 :: g1 :: g2 :: b1 :: b2 :: [])
  {prf2 = (a :: b :: c :: d :: e :: f :: h)} =
  MkWebColor
    (fromChar r1, fromChar r2)
    (fromChar g1, fromChar g2)
    (fromChar b1, fromChar b2)
    Nothing

||| Converts a `List` of 8 elements to a `WebColor`.
private
list8ToWebColor :
     (xs : List Char)
  -> {auto 0 prf1 : 8 = length xs}
  -> {auto prf2 : All Hexit xs}
  -> WebColor
list8ToWebColor
  (r1 :: r2 :: g1 :: g2 :: b1 :: b2 :: a1 :: a2 :: [])
  {prf2 = (a :: b :: c :: d :: e :: f :: h :: i :: j)} =
  MkWebColor
    (fromChar r1, fromChar r2)
    (fromChar g1, fromChar g2)
    (fromChar b1, fromChar b2)
    (Just (fromChar a1, fromChar a2))

||| Creates a `WebColor` from a `String`.
|||
||| To be valid the provided 'String' must start with a '#'
||| and the rest of the 'String' must:
||| - be of 6 or 8 characters long; and
||| - all characters must be hexadecimal ones ([0-9a-fA-F]).
public export
fromString :
     (str : String)
  -> let
       list : List Char
       list = unpack str
     in
     {auto prf1 : NonEmpty list}
  -> let
       xs : List Char
       xs = tail list
       
       size = length xs
     in
     {auto prf2 :
       Either (6 = size) (8 = size)
     }
  -> {auto prf3 : '#' = head list}
  -> {auto prf4 : All Hexit xs}
  -> WebColor
fromString str {prf2 = (Left x)}  = list6ToWebColor (tail $ unpack str)
fromString str {prf2 = (Right x)} = list8ToWebColor (tail $ unpack str)

||| Converts a `WebColor` to a `String`.
public export
Cast WebColor String where
  cast (MkWebColor r g b a) =
        "#"
    <+> tupleToString r
    <+> tupleToString g
    <+> tupleToString b
    <+> foldMap tupleToString a
    where
      tupleToString : (Symbol, Symbol) -> String
      tupleToString (s1, s2) = singleton (toChar s1) <+> singleton (toChar s2)

||| Converts a `WebColor` to a RGBA representation.
|||
||| The values of the returned 4-`Tuple` represents:
|||
||| - red [0-255]
||| - green [0-255]
||| - blue [0-255]
||| - alpha [0-1]
public export
toRGBA : WebColor -> (Int, Int, Int, Double)
toRGBA color =
  let
    a = maybe "F" id (alpha color)
  in
  ( cast (red color)
  , cast (green color)
  , cast (blue color)
  , (the Double $ cast $ a) / 255
  )

||| Converts a `Hex` to a tuple of two `Symbol`s.
|||
||| If the `Hex` is greater than `FF`, then the value is clamped to `FF`.
private
hexToTuple : Hex -> (Symbol, Symbol)
hexToTuple x =
  case min x "FF" of
    MkHex (head ::: [])     => ('0', head)
    -- As the maximal value is "FF"
    -- there cannot be more than two elements in the list.
    MkHex (head ::: y :: _) => (head, y)

||| Converts hexadecimal values to a `WebColor`.
|||
||| Values are clamped to "FF".
public export
fromHex :
     (red : Hex)
  -> (green: Hex)
  -> (blue : Hex)
  -> (alpha: Maybe Hex)
  -> WebColor
fromHex r g b a =
  MkWebColor
    (hexToTuple r)
    (hexToTuple g)
    (hexToTuple b)
    (map hexToTuple a)

||| Additive color mixing.
public export
additiveMixing : WebColor -> WebColor -> WebColor
additiveMixing color1 color2 =
  let
    r = red color1 + red color2
    g = green color1 + green color2
    b = blue color1 + blue color2
    a = case (alpha color1, alpha color2) of
          (Nothing, Nothing)   => Nothing
          (Nothing, (Just y))  => Just y
          ((Just x), Nothing)  => Just x
          ((Just x), (Just y)) => Just (x + y)
  in
  fromHex r g b a

--------------------------------------------------------------------------------
-- Compile Time Test
--------------------------------------------------------------------------------

failing
  private
  testStringNoSharp : WebColor
  testStringNoSharp = fromString "123456"

failing
  private
  testString2Sharp : WebColor
  testString2Sharp = fromString "##123456"

failing
  private
  testString5 : WebColor
  testString5 = fromString "#12345"

failing
  private
  testString7 : WebColor
  testString7 = fromString "#1234567"

failing
  private
  testString9 : WebColor
  testString9 = fromString "#123456789"

failing
  private
  testStringBadChar : WebColor
  testStringBadChar = fromString "#12H456"

||| Web colours specified using hexadecimal colour codes.
module Data.Hex.WebColors

import Derive.Prelude
import Data.Refined.Char

import public Data.Hex

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

||| Proof that the first element of `List` of `Char` is `#`.
public export
data StartWithSharp : List Char -> Type where
  Here : StartWithSharp ('#' :: cs)

public export
HDec0 (List Char) StartWithSharp where
  hdec0 ('#' :: _) = Just0 Here
  hdec0 _          = Nothing0

||| Proof that all remaining elemnets of a `List` of `Char` are hexadecimal.
public export
data TailHexit : List Char -> Type where
  There : All Hexit t -> TailHexit (c :: t)

public export
HDec0 (List Char) TailHexit where
  hdec0 []       = Nothing0
  hdec0 [c]      = Nothing0
  hdec0 (c :: t) = case hdec0 {p = All Hexit} t of
                     Just0 prf => Just0 (There prf)
                     Nothing0  => Nothing0

||| Proof that a `List` has a length of 7 elements.
public export
data Length7 : List a -> Type where
  Here7 : Length7 (a :: b :: c :: d :: e :: f :: g :: [])

public export
HDec0 (List a) Length7 where
  hdec0 (a :: b :: c :: d :: e :: f :: g :: []) =
    Just0 Here7
  hdec0 _ =
    Nothing0

||| Proof that a `List` has a length of 9 elements.
public export
data Length9 : List a -> Type where
  Here9 : Length9 (a :: b :: c :: d :: e :: f :: g :: h :: i :: [])

public export
HDec0 (List a) Length9 where
  hdec0 (a :: b :: c :: d :: e :: f :: g :: h :: i :: []) =
    Just0 Here9
  hdec0 _ =
    Nothing0

public export
0 IsWebColor : String -> Type
IsWebColor = Str $ StartWithSharp && TailHexit && (Length7 || Length9)

||| Converts a `List` to `Maybe` a `WebColor`.
|||
||| The list must be 7 or 9 character long.
||| Its first element must be '#'.
||| All the remaining elements must be hexadecimal characters.
public export
fromListMaybe : List Char -> Maybe WebColor
fromListMaybe ('#' :: r1 :: r2 :: g1 :: g2 :: b1 :: b2 :: cs) = do
  let mkWebCol = MkWebColor
                   (!(fromCharMaybe r1), !(fromCharMaybe r2))
                   (!(fromCharMaybe g1), !(fromCharMaybe g2))
                   (!(fromCharMaybe b1), !(fromCharMaybe b2))
  case cs of
    []               => pure $ mkWebCol Nothing
    (a1 :: a2 :: []) => pure $ mkWebCol $ Just
                          (!(fromCharMaybe a1), !(fromCharMaybe a2))
    _                => Nothing
fromListMaybe _ = Nothing

||| Creates `Maybe` a `WebColor` from a `String`.
|||
||| To return `Just` a `WebColor` the provided 'String' must:
||| - start with a '#';
||| - all remaining characters must be hexadecimal ones ([0-9a-fA-F]); and
||| - be of 7 or 9 characters long.
public export
fromStringMaybe : String -> Maybe WebColor
fromStringMaybe str =
  case hdec0 {p = IsWebColor} str of
    Just0 prf => fromListMaybe (unpack str)
    Nothing0 => Nothing

||| Creates a `WebColor` from a `String`.
|||
||| To be valid the provided 'String' must:
||| - start with a '#';
||| - all remaining characters must be hexadecimal ones ([0-9a-fA-F]); and
||| - be of 7 or 9 characters long.
public export
fromString :
     (s : String)
  -> {auto 0 prf : IsJust (WebColors.fromStringMaybe s)}
  -> WebColor
fromString s = fromJust $ fromStringMaybe s

||| Converts a `WebColor` to a `String`.
public export
toString : WebColor -> String
toString (MkWebColor r g b a) =
        "#"
    <+> tupleToString r
    <+> tupleToString g
    <+> tupleToString b
    <+> foldMap tupleToString a
    where
      tupleToString : (Symbol, Symbol) -> String
      tupleToString (s1, s2) = singleton (toChar s1) <+> singleton (toChar s2)

public export
Cast WebColor String where
  cast = toString

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
public export
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

private
testL7 : fromString "#ab42cd" =
  MkWebColor (HexA, HexB) (Hex4, Hex2) (HexC, HexD) Nothing
testL7 = Refl

private
testL9 : fromString "#ab42cd24" =
  MkWebColor (HexA, HexB) (Hex4, Hex2) (HexC, HexD) (Just (Hex2, Hex4))
testL9 = Refl

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

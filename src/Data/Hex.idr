||| This module provides functions for hexadecimal numbers creation
||| from `String`s, convertion to `Integer`s, basic interfaces and
||| arithmetic operations.
module Data.Hex

import Data.Monoid.Exponentiation
import Data.Refined.Integer
import Data.Refined.String
import Derive.Prelude

%default total
%language ElabReflection

||| Hexadecimal symbols from 0 to F.
public export
data Symbol =
    Hex0
  | Hex1
  | Hex2
  | Hex3
  | Hex4
  | Hex5
  | Hex6
  | Hex7
  | Hex8
  | Hex9
  | HexA
  | HexB
  | HexC
  | HexD
  | HexE
  | HexF

%runElab derive "Symbol" [Eq, Show]

||| A hexadecimal number.
|||
||| The hexadecimal number consists of a `List` of `Symbol`s.
public export
data Hex : Type where
  MkHex : List1 Symbol -> Hex

%runElab derive "Hex" [Semigroup, Show]

private
snoc : Hex -> Symbol -> Hex
snoc (MkHex xs) symbol = MkHex (snoc xs symbol)

public export
fromCharMaybe : Char -> Maybe Symbol
fromCharMaybe '0' = Just Hex0
fromCharMaybe '1' = Just Hex1
fromCharMaybe '2' = Just Hex2
fromCharMaybe '3' = Just Hex3
fromCharMaybe '4' = Just Hex4
fromCharMaybe '5' = Just Hex5
fromCharMaybe '6' = Just Hex6
fromCharMaybe '7' = Just Hex7
fromCharMaybe '8' = Just Hex8
fromCharMaybe '9' = Just Hex9
fromCharMaybe 'A' = Just HexA
fromCharMaybe 'B' = Just HexB
fromCharMaybe 'C' = Just HexC
fromCharMaybe 'D' = Just HexD
fromCharMaybe 'E' = Just HexE
fromCharMaybe 'F' = Just HexF
fromCharMaybe 'a' = Just HexA
fromCharMaybe 'b' = Just HexB
fromCharMaybe 'c' = Just HexC
fromCharMaybe 'd' = Just HexD
fromCharMaybe 'e' = Just HexE
fromCharMaybe 'f' = Just HexF
fromCharMaybe _   = Nothing

||| Creates a `Symbol` from a `Char`.
|||
||| Only characters which are digits or letters from a to f are accepted.
||| In other words, it must match the regular expression `^[0-9A-Fa-f]*$`.
public export
fromChar : (c : Char) -> {auto 0 prf : IsJust (fromCharMaybe c)} -> Symbol
fromChar c = fromJust $ fromCharMaybe c

||| Converts a hexadecimal 'Symbol' to a 'Char'.
public export
toChar : Symbol -> Char
toChar Hex0 = '0'
toChar Hex1 = '1'
toChar Hex2 = '2'
toChar Hex3 = '3'
toChar Hex4 = '4'
toChar Hex5 = '5'
toChar Hex6 = '6'
toChar Hex7 = '7'
toChar Hex8 = '8'
toChar Hex9 = '9'
toChar HexA = 'A'
toChar HexB = 'B'
toChar HexC = 'C'
toChar HexD = 'D'
toChar HexE = 'E'
toChar HexF = 'F'

||| Converts a `List` of `Char`s to a `Maybe` a `List1` of `Symbol`s.
|||
||| All characters must be either digits or letters from a to f.
||| In other words, they must be part of the `[0-9A-Fa-f]` set.
||| The `List` must not be empty.
public export
fromListMaybe : List Char -> Maybe (List1 Symbol)
fromListMaybe [] = Nothing
fromListMaybe (c :: cs) =
  case hdec0 {p = All Hexit} (c :: cs) of
  Nothing0  => Nothing
  (Just0 _) => do
    pure (!(fromCharMaybe c) ::: !((sequence . map fromCharMaybe) cs))

||| Converts a `List` of `Char`s to a `List1` of `Symbol`s.
|||
||| All characters must be either digits or letters from a to f.
||| In other words, they must be part of the `[0-9A-Fa-f]` set.
||| The `List` must not be empty.
public export
fromList :
     (l : List Char)
  -> {auto 0 prf : IsJust (fromListMaybe l)}
  -> List1 Symbol
fromList l = fromJust $ fromListMaybe l

||| Converts a `String` to `Maybe Hex`.
|||
||| For `Just Hex` to be returned, all characters must be either digits or
||| letters from a to f.
||| In other words, the `String` must match the regular expression
||| `^[0-9A-Fa-f]+$`.
||| Otherwise, `Nothing` is returned.
public export
fromStringMaybe : String -> Maybe Hex
fromStringMaybe "" = Nothing
fromStringMaybe s  = case hdec0 {p = Str (All Hexit)} s of
  Nothing0  => Nothing
  (Just0 _) => MkHex <$> (fromListMaybe $ unpack s)

||| Converts a `String` to a `Hex`.
|||
||| All characters must be either digits or letters from a to f.
||| In other words, the `String` must match the regular expression
||| `^[0-9A-Fa-f]+$`.
public export
fromString : (s : String) -> {auto 0 prf : IsJust (fromStringMaybe s)} -> Hex
fromString s = fromJust $ fromStringMaybe s

private
symbolToInteger : Symbol -> Integer
symbolToInteger Hex0 = 0
symbolToInteger Hex1 = 1
symbolToInteger Hex2 = 2
symbolToInteger Hex3 = 3
symbolToInteger Hex4 = 4
symbolToInteger Hex5 = 5
symbolToInteger Hex6 = 6
symbolToInteger Hex7 = 7
symbolToInteger Hex8 = 8
symbolToInteger Hex9 = 9
symbolToInteger HexA = 10
symbolToInteger HexB = 11
symbolToInteger HexC = 12
symbolToInteger HexD = 13
symbolToInteger HexE = 14
symbolToInteger HexF = 15

private
integerToSymbol : (x : Integer) -> {auto 0 prf : FromTo 0 15 x} -> Symbol
integerToSymbol 0  = Hex0
integerToSymbol 1  = Hex1
integerToSymbol 2  = Hex2
integerToSymbol 3  = Hex3
integerToSymbol 4  = Hex4
integerToSymbol 5  = Hex5
integerToSymbol 6  = Hex6
integerToSymbol 7  = Hex7
integerToSymbol 8  = Hex8
integerToSymbol 9  = Hex9
integerToSymbol 10 = HexA
integerToSymbol 11 = HexB
integerToSymbol 12 = HexC
integerToSymbol 13 = HexD
integerToSymbol 14 = HexE
integerToSymbol 15 = HexF
-- Cannot be reached
integerToSymbol _  = Hex0

private
toIntegerHelper : List1 Symbol -> Integer
toIntegerHelper (head ::: tail) =
  toIntegerHelper' (head :: tail)
  where
    toIntegerHelper' : List Symbol -> Integer
    toIntegerHelper' [] = 0
    toIntegerHelper' (x :: xs) =
      (symbolToInteger x) * (16 ^ length xs) + toIntegerHelper' xs

public export
Ord Symbol where
  compare x y = compare (symbolToInteger x) (symbolToInteger y)

||| Convertion of a hexadecimal symbol to a hexadecimal number.
Cast Symbol Hex where
  cast symb = MkHex (pure symb)

Cast Symbol Char where
  cast = toChar

||| Convertion of a `Pair` of hexadecimal symbols to a hexadecimal number.
Cast (Symbol, Symbol) Hex where
  cast (x, y) = MkHex (x ::: [y])

||| Convertion of a hexadecimal number to an `Integer`.
|||
||| # Notes
|||
||| Leading zeros will get removed.
||| For example, `"00a"` will be converted to `10`.
|||
||| If all you want is to get the integer value of a hexadecimal number
||| it is easier to just type `0x` and your hexadecimal number.
||| It will get directly converted to an `Integer` by Idris.
||| For example, `0x42` is converted to `66`.
public export
Cast Hex Integer where
  cast (MkHex xs) = toIntegerHelper xs

||| Convertion of an `Integer` to a hexadecimal number.
|||
||| Negative integers are converted to '0'.
public export
Cast Integer Hex where
  cast val =
    case hdec0 {p = GreaterThan 0} val of
      Nothing0 => "0"
      Just0 _  =>
          let
            (val' ** _)   = maxGt0 val
            (result ** _) = div16LtQ val'
            (remain ** _) = mod16 val'
          in
          case result of
            0 => MkHex (integerToSymbol remain ::: [])
            r =>
              -- The function is total, because each `result` is smaller
              -- and the function converges to 0, which is the termination case.
              snoc
                (assert_total $ the Hex $ cast result)
                (integerToSymbol remain)
          where
            -- Axioms

            -- The max value between 0 and any integer is at least 0.
            maxGt0 : (x : Integer) -> (result ** 0 <= result)
            maxGt0 x = let result = max 0 x in (result ** believe_me result)

            -- For any integer from 0,
            -- its division by 16 leads to a result of at leat 0.
            div16LtQ :
                 (quotient : Integer)
              -> {auto 0 prf : 0 <= quotient}
              -> (result ** (0 <= result))
            div16LtQ quotient =
              let result = quotient `div` 16 in (result ** believe_me result)

            -- For any integer from 0,
            -- its remainder when divided by 16
            -- will be between 0 and 15 included.
            mod16 :
              (quotient : Integer)
              -> {auto 0 prf : 0 <= quotient}
              -> (result ** FromTo 0 15 result)
            mod16 quotient =
              let result = quotient `mod` 16 in (result ** believe_me result)

public export
Cast Hex Int where
  cast hex = cast $ the Integer $ cast hex

public export
Cast Hex Double where
  cast hex = cast $ the Integer $ cast hex

public export
Cast Hex (List1 Symbol) where
  cast (MkHex xs) = xs

public export
Cast Hex (List Symbol) where
  cast hex = toList $ the (List1 Symbol) $ cast hex

||| Converts a `Hex` to a `String`.
public export
toString : Hex -> String
toString = pack . map toChar . cast

public export
Cast Hex String where
  cast = toString

||| Leading zeros are ignored for equality.
||| For example, hex "0101" equals hex "101".
|||
||| If you want leading zeros to matter, convert first the `Hex` to `String`s.
|||
||| ```idris example
|||
||| toString hex0101 == toString hex101
||| > result = False
||| ```
Eq Hex where
  x == y = (the Integer $ cast x) == (the Integer $ cast y)

||| Leading zeros are ignored for equality.
||| For example, hex "0101" is smaller or equal to hex "101".
public export
Ord Hex where
  compare x y = compare (the Integer $ cast x) (the Integer $ cast y)

public export
Num Hex where
  x + y = cast $ the Integer (cast x + cast y)
  x * y = cast $ the Integer (cast x * cast y)
  fromInteger = cast

public export
Integral Hex where
  div x y = cast $ the Integer (cast x `div` cast y)
  mod x y = cast $ the Integer (cast x `mod` cast y)

||| Subtracts hexadecimal numbers.
|||
||| If the second number is larger than the first, returns 0.
public export
minus : Hex -> Hex -> Hex
minus x y = cast $ max 0 (the Integer (cast x - cast y))

--------------------------------------------------------------------------------
-- Compile Time Tests
--------------------------------------------------------------------------------

private
TestHex0 : Hex
TestHex0 = MkHex (pure Hex0)

private
TestHex16 : Hex
TestHex16 = MkHex (Hex1 ::: [Hex0])

private
TestHex257 : Hex
TestHex257 = MkHex (Hex1 ::: [Hex0, Hex1])

private
test0 : cast 0 = TestHex0
test0 = Refl

private
test16 : the Hex (cast 16) = TestHex16
test16 = Refl

private
test257 : cast 257 = TestHex257
test257 = Refl

private
test0Str : fromString "0" = TestHex0
test0Str = Refl

private
test16Str : fromString "10" = TestHex16
test16Str = Refl

private
test257Str : fromString "101" = TestHex257
test257Str = Refl

failing
  testNonValidChar : Hex
  testNonValidChar = fromString "G"

failing
  testNonValidChars : Hex
  testNonValidChars = fromString "0Gh"

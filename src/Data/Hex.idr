||| This module provides functions for hexadecimal numbers creation
||| from `String`s, convertion to `Integer`s, basic interfaces and
||| arithmetic operations.
module Data.Hex

import Data.List1.Quantifiers
import Data.Monoid.Exponentiation
import Data.Refined.Char
import Data.Refined.Integer
import Data.Refined.String
import Data.String
import Decidable.Equality
import Derive.Prelude

%default total
%language ElabReflection

||| Hexadecimal symbols from 0 to F.
export
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

%runElab derive "Hex" [Eq, Semigroup, Show]

private
snoc : Hex -> Symbol -> Hex
snoc (MkHex xs) symbol = MkHex (snoc xs symbol)

||| Creates a `Symbol` from a `Char`.
|||
||| Only characters which are digits or letters from a to f are accepted.
||| In other words, it must match the regular expression `^[0-9A-Fa-f]*$`.
public export
fromChar : (c : Char) -> {auto 0 prf : Hexit c} -> Symbol
fromChar '0' = Hex0
fromChar '1' = Hex1
fromChar '2' = Hex2
fromChar '3' = Hex3
fromChar '4' = Hex4
fromChar '5' = Hex5
fromChar '6' = Hex6
fromChar '7' = Hex7
fromChar '8' = Hex8
fromChar '9' = Hex9
fromChar 'A' = HexA
fromChar 'B' = HexB
fromChar 'C' = HexC
fromChar 'D' = HexD
fromChar 'E' = HexE
fromChar 'F' = HexF
fromChar 'a' = HexA
fromChar 'b' = HexB
fromChar 'c' = HexC
fromChar 'd' = HexD
fromChar 'e' = HexE
fromChar 'f' = HexF
fromChar _   = Hex0

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

||| Converts a `List` of `Char`s to a `List1` of `Symbol`s.
|||
||| All characters must be either digits or letters from a to f.
||| In other words, they must be part of the `[0-9A-Fa-f]` set.
public export
fromList :
     (l : List Char)
  -> {auto 0 prf1 : NonEmpty l}
  -> {auto 0 prf2 : All Hexit l}
  -> List1 Symbol
fromList (x :: xs) {prf1 = IsNonEmpty} {prf2 = a :: b} =
  fromChar x ::: fromList' xs
  where
    fromList' : (l : List Char) -> {auto 0 prf : All Hexit l} -> List Symbol
    fromList' [] = []
    fromList' (x :: xs) {prf = a :: b} = fromChar x :: fromList' xs

||| Converts a `String` to a `Hex`.
|||
||| All characters must be either digits or letters from a to f.
||| In other words, the `String` must match the regular expression
||| `^[0-9A-Fa-f]*$`.
public export
fromString : (s : String) -> {auto 0 prf1 : NonEmpty (unpack s)} -> {auto 0 prf2 : Str (All Hexit) s} -> Hex
fromString str {prf2 = (HoldsOn x)} = MkHex $ fromList $ unpack str

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
integerToSymbol : (x : Integer) -> {auto 0 prf : ((0 <=) && (16 >)) x} -> Symbol
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
-- Cannot be reached.
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

||| Convertion of a `Tuple` of hexadecimal symbols to a hexadecimal number.
Cast (Symbol, Symbol) Hex where
  cast tup = MkHex (?tupToList1 tup)

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

public export
Cast Integer Hex where
  cast val =
    case decEq val 0 of
      (Yes _) => "0"
      (No _) =>
          let
            (val' ** _)   = maxGt0 val
            (result ** _) = div16LtQ val'
            (remain ** _) = mod16 val'
          in
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
              -> (result ** ((0 <=) && (16 >)) result)
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

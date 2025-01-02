module Data.Hex

import Data.List.Quantifiers
import Data.Monoid.Exponentiation
import Data.Refined.Char
import Data.Refined.String
import Data.String
import Data.Vect

%default total

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

||| A hexadecimal number.
|||
||| The hexadecimal number consists of a vector of `Symbol`.
export
data Hex : Type where
  MkHex : {n : Nat} -> Vect n Symbol -> Hex

private
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

private
fromStringHelper :
     (l : List Char)
  -> {auto 0 prf : All Hexit l}
  -> Vect (length l) Symbol
fromStringHelper [] = []
fromStringHelper (x :: xs) {prf = (a :: b)} = fromChar x :: fromStringHelper xs

public export
fromString : (s : String) -> {auto 0 prf : Str (All Hexit) s} -> Hex
fromString str {prf = (HoldsOn x)} = MkHex $ fromStringHelper $ unpack str

private
symbolToInt : Symbol -> Integer
symbolToInt Hex0 = 0
symbolToInt Hex1 = 1
symbolToInt Hex2 = 2
symbolToInt Hex3 = 3
symbolToInt Hex4 = 4
symbolToInt Hex5 = 5
symbolToInt Hex6 = 6
symbolToInt Hex7 = 7
symbolToInt Hex8 = 8
symbolToInt Hex9 = 9
symbolToInt HexA = 10
symbolToInt HexB = 11
symbolToInt HexC = 12
symbolToInt HexD = 13
symbolToInt HexE = 14
symbolToInt HexF = 15

private
toIntHelper : {n : Nat} -> Vect n Symbol -> Integer
toIntHelper [] = 0
toIntHelper {n = S len} (x :: xs) =
  (symbolToInt x) * (16 ^ cast len) + toIntHelper xs

||| Convertion of a hexadecimal number to an `Integer`.
|||
||| Note that leading zeros will get removed.
||| For example, `"00a"` will be converted to `10`.
public export
Cast Hex Integer where
  cast (MkHex vect) = toIntHelper vect

||| Convertion of a hexadecimal number to an `Integer`.
|||
||| Note that the conversion is not isomorphic
||| as leading zeros will get removed.
||| For example, `"00a"` will be converted to `10`.
public export
Cast Hex Nat where
  cast = cast . the Integer . cast

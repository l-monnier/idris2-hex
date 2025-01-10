module Data.Hex

import Data.List.Quantifiers
import Data.Monoid.Exponentiation
import Data.Refined.Char
import Data.Refined.Integer
import Data.Refined.String
import Data.String
import Data.Vect
import Decidable.Equality

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
  MkHex : List Symbol -> Hex

public export
Semigroup Hex where
  (MkHex xs) <+> (MkHex ys) = MkHex (xs <+> ys)

public export
Monoid Hex where
  neutral = MkHex neutral 

private
snoc : Hex -> Symbol -> Hex
snoc (MkHex xs) symbol = MkHex (snoc xs symbol)

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
  -> List Symbol
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
integerToSymbol _  = Hex0

private
toIntegerHelper : List Symbol -> Integer
toIntegerHelper [] = 0
toIntegerHelper list@(x :: xs) =
  (symbolToInteger x) * (16 ^ length xs) + toIntegerHelper xs

||| Convertion of a hexadecimal number to an `Integer`.
|||
||| Note that leading zeros will get removed.
||| For example, `"00a"` will be converted to `10`.
public export
Cast Hex Integer where
  cast (MkHex xs) = toIntegerHelper xs

||| Convertion of a hexadecimal number to an `Integer`.
|||
||| Note that the conversion is not isomorphic
||| as leading zeros will get removed.
||| For example, `"00a"` will be converted to `10`.
public export
Cast Hex Nat where
  cast = cast . the Integer . cast

public export
Cast Integer Hex where
  cast val =
    case decEq val 0 of
      (Yes _) => neutral
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
Num Hex where
  x + y = cast $ the Integer (cast x + cast y)
  x * y = cast $ the Integer (cast x * cast y)
  fromInteger = cast

public export
Integral Hex where
  div x y = cast $ the Integer (cast x `div` cast y)
  mod x y = cast $ the Integer (cast x `mod` cast y)

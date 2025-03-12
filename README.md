# idris2-hex
Hexadecimal library in Idris.

# Purpose

This library is first and foremost a personal learning project.
Its practical use is rather limited.

# Features

## String conversion

You can converts `String`s to `Hex` using the `fromString` function.
Such strings are validated at compile time. Only non-empty `String`s with 
valid hexadecimal characters will be accepted.

Upper and lower case letters are accepted.
For example, `a4` and `A4` are valid.

## Numeric operations

`Hex` is an instance of `Num` and `Integral`.

It is therefore possible to perform numeric operations.
For example, you can write:

```idris
"12" + "F2"
``` 

## Web colors

The `Data.Hex.WebColors` module provides functionnalities dedicated to
web colors.

The `fromString` fonction converts `String`s at compile time, requiring that
they start with '#' and comprise 6 or 8 hexadecimal characters.

It is possible to convert a `WebColor` to RGBA values.

There is also the possibility to mix additively two `WebColor`s
with the `additiveMixing` function.

# Feedback

As mentioned, this library is mainly a learning exercice.
Feedback on how to improve its implementation is more than welcome.

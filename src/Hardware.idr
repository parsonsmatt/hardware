module Hardware

import Data.Vect

Gate : Type
Gate = Bool -> Bool -> Bool

nand : Gate
nand True True = False
nand a    b    = True

and : Gate
and a b = nand (nand a b) (nand a b)

or : Gate
or a b = nand (nand a a) (nand b b)

not : Bool -> Bool
not a = nand a a

nor : Gate
nor a b = nand q q
  where 
    q = nand (nand a a) (nand b b)

xor : Gate
xor a b = nand d e
  where
    c : Bool
    c = nand a b
    d = nand c a
    e = nand c b

halfAdder : Bool -> Bool -> (Bool, Bool)
halfAdder a b = (xor a b, and a b)

fullAdder : Bool -> Bool -> Bool -> (Bool, Bool)
fullAdder a b c = (xor a (xor b c), or (and a b) (and c (xor a b)))

Byte : Type
Byte = Vect 8 Bool

zero : Byte
zero = replicate 8 False

one : Byte
one = True :: replicate 7 False

rippleCarry : Vect n Bool -> Vect n Bool -> Vect n Bool
rippleCarry x y = go False x y
  where
    go : Bool -> Vect n Bool -> Vect n Bool -> Vect n Bool
    go carry [] [] = Data.Vect.Nil
    go carry (a :: as) (b :: bs) =
      let (s, c) = fullAdder a b carry
       in s :: go c as bs

two : Byte
two = rippleCarry one one

three : Byte
three = rippleCarry one two

four : Byte
four = rippleCarry one three

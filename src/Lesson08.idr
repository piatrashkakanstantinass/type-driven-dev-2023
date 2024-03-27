module Lesson08

import Data.Vect
import Data.Vect.Elem
import Data.String
import Decidable.Equality

%default total


-- removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
-- removeElem value (x :: xs) = case decEq value x of
--                                   (Yes prf) => xs
--                                   (No contra) => x :: removeElem value xs

elemTest : Elem "Mary" ["Peter", "Paul", "Mary"]
elemTest = There (There Here)

removeElem : (xs : Vect (S n) a) -> (prf : Elem _ xs) -> Vect n a
removeElem (x :: xs) Here = xs
removeElem (x :: []) (There later) = absurd later
removeElem (x :: (y :: xs)) (There later) = x :: removeElem (y :: xs) later

removeElem' : (value : a) -> (xs : Vect (S n) a) -> { auto prf : Elem value xs} -> Vect n a
removeElem' value (value :: xs) {prf = Here} = xs
removeElem' value (x :: []) {prf = There later} = absurd later
removeElem' value (x :: (y :: xs)) {prf = (There later)} = x :: removeElem' value (y :: xs)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There later) impossible

notInTail : (value = x -> Void) -> (Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isEl : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isEl value [] = No notInNil
isEl value (x :: xs) = case decEq value x of
                              (Yes Refl) => Yes Here
                              (No notHere) => case (isEl value xs) of
                                                   (Yes prf) => Yes (There prf)
                                                   (No notThere) => No (notInTail notHere notThere)

data Last : List a -> a -> Type where
    LastOne : Last [value] value
    LastCons : (prf: Last xs value) -> Last (x::xs) value

noLastInEmpty : Last [] _ -> Void
noLastInEmpty LastOne impossible
noLastInEmpty (LastCons prf) impossible

lastNotInHead : (value = x -> Void) -> (Last [x] value -> Void)
lastNotInHead f LastOne = f Refl
lastNotInHead f (LastCons prf) = noLastInEmpty prf

lastNotInTail : (Last (x::xs) value -> Void) -> Last (y :: (x :: xs)) value -> Void
lastNotInTail f (LastCons prf) = f prf

test : Last [1,2,3] 3
test = LastCons (LastCons LastOne)

noName : (Last (y :: xs) value -> Void) -> Last (_ :: (y :: xs)) value -> Void
noName f (LastCons prf) = f prf


isLast : DecEq a => (value : a) -> (xs: List a) -> Dec (Last xs value)
isLast value [] = No noLastInEmpty
isLast value [x] = case decEq value x of
                        (Yes Refl) => Yes LastOne
                        (No contra) => No $ lastNotInHead contra
isLast value (_ :: l @ (y :: xs)) = case isLast value l of
                                         (Yes prf) => Yes $ LastCons prf
                                         (No contra) => No $ noName contra

-- [1, 2] value = 2
-- [2] value = 2

-- isLast : DecEq a => (value : a) -> (xs: List a) -> Dec (Last xs value)
-- isLast value [] = No noLastInEmpty
-- isLast value (x :: []) = case decEq value x of
--                               (Yes Refl) => Yes LastOne
--                               (No contra) => No $ lastNotInHead contra
-- isLast value (_ :: l @ (y :: xs)) = case isLast value l of
--                                          (Yes prf) => Yes $ LastCons prf
--                                          (No contra) => No $ lastNotInTail contra

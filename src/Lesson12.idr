||| Infinite total programs.
||| pack --rlwrap --with-ipkg *.ipkg repl src/Lesson12.idr
module Lesson12

import Data.Bits
import Data.Stream
import Data.Primitives.Views
import System

%default total

-------------------- Preliminaries

export
random_step : Int -> Int
random_step seed =
    let seed' = 1664525 * seed + 1013904223
    in (seed' `shiftR` 2)

{- REPL:
    map random_step [0, 1, 2, 3, 4]
-}

-------------------- Cont.

labelFrom : Integer -> List a -> List (Integer, a)
labelFrom i [] = []
labelFrom i (x :: xs) = (i, x) :: labelFrom (i + 1) xs

label : List a -> List (Integer, a)
label xs = labelFrom 0 xs

failing
    countFrom : Integer -> List Integer
    countFrom i = i :: countFrom (i+1)

AdderType : (num : Nat) -> Type
AdderType 0 = Integer
AdderType (S k) = (next : Integer) -> AdderType k

failing
    AdderType' : Type
    AdderType' = (next : Integer) -> AdderType'

data CounterData : Type where
    Elem : (Integer) -> (() -> CounterData) -> CounterData

failing
    counterData : Integer -> CounterData
    counterData i = Elem i \() => counterData_rhs_1

-- experiment : Integer -> (() -> (Integer, () -> (Integer, List Integer)))

----------------------

data InfList : Type -> Type where
    (::) : (value : a) -> (Inf (InfList a)) -> (InfList a)

total
countAfter : Integer -> InfList Integer
countAfter i = i :: Delay (countAfter (i+1))

------------

getPrefix : (n : Nat) -> InfList a -> List a
getPrefix 0 x = []
getPrefix (S k) (value :: lst) = value :: getPrefix k (Force lst)

------------

label'With : Stream l -> List a -> List (l, a)
label'With xs [] = []
label'With (lbl :: nxt) (a :: as) = (lbl, a) :: (label'With nxt as)

label' : List a -> List (Integer, a)
label' xs = label'With [0..] xs

-------------------- IO

covering -- Non total, because non-productive nor terminating.
quiz: Stream Int -> (score : Nat) -> IO ()
quiz (x :: y :: z) score =
    do  putStrLn ("Score so far: " ++ show score)
        putStr (show x ++ " * " ++ show y ++ "?")
        answer <- getLine
        if cast answer == x * y
            then do putStrLn "Correct!"
                    quiz z (score + 1)
            else do putStrLn ("Wrong, the answer is " ++ show (x * y))
                    quiz z score


data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO
    Exit : IO a -> InfIO

total
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

covering
run : InfIO -> IO ()
run (Do act cnt) = do res <- act
                      run (cnt res)
run (Exit act) = do
    _ <- act
    pure ()


data Fuel = Dry | More Fuel

total
tank : Nat -> Fuel
tank 0 = Dry
tank (S k) = More (tank k)

total
run' : Fuel -> InfIO -> IO ()
run' Dry _ = putStrLn "Astalavista"
run' (More fu) (Do act cnt) = do res <- act
                                 run' fu (cnt res)
run' (More fu) (Exit act) =
    do
        _ <- act
        pure ()

data Gas = Empty | Full (Lazy Gas)

covering
forever : Gas
forever = Full forever


total
runOnGas : Gas -> InfIO -> IO ()
runOnGas Empty _ = putStrLn "Astalavista"
runOnGas (Full fu) (Do act cnt) = do res <- act
                                     runOnGas fu (cnt res)
runOnGas (Full _) (Exit act) =
    do
        _ <- act
        pure ()

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

(>>) : IO a -> Inf InfIO -> InfIO
x >> y = Do x (\z => y)

exitInfIO : IO a -> InfIO
exitInfIO x = Exit x

total
quizInf: Stream Int -> (score : Nat) -> InfIO
quizInf (x :: y :: z) score =
    do  putStrLn ("Score so far: " ++ show score)
        putStr (show x ++ " * " ++ show y ++ "?")
        answer <- getLine
        if answer == "exit" then exitInfIO (putStrLn "Bye") else (if cast answer == x * y
            then do putStrLn "Correct!"
                    quizInf z (score + 1)
            else do putStrLn ("Wrong, the answer is " ++ show (x * y))
                    quizInf z score)
covering
quizGameOnGas : IO ()
quizGameOnGas = run (quizInf [1..] 0)

everyOther : Stream a -> Stream a
everyOther (x :: (z :: w)) = x :: everyOther w

data Face = Heads | Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips 0 xs = []
coinFlips (S k) (x :: y) with (divides x 2)
  coinFlips (S k) (((2 * div) + rem) :: y) | (DivBy div rem prf) =
    let face = if rem == 0 then Heads else Tails
    in face :: coinFlips k y

sqrtApprox : (num : Double) -> (approx : Double) -> Stream Double
sqrtApprox num approx = let approx' = (approx + (num / approx)) / 2
    in approx' :: sqrtApprox num approx'

sqrtBounded : (max : Nat) -> (num : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
sqrtBounded 0 num bound approxs = head approxs
sqrtBounded (S k) num bound (x :: y) = case abs (x * x - num) < bound of
                                           False => sqrtBounded k num bound y
                                           True => x

data DelayedExecution = DelayedExec Int (Int -> Int)

genSeries : DelayedExecution
genSeries = DelayedExec 0 (\arg => arg + 1)

next : DelayedExecution -> (Int, DelayedExecution)
next (DelayedExec i f) = (i, DelayedExec (f i) f)

takeDel : Nat -> DelayedExecution -> List Int
takeDel 0 x = []
takeDel (S k) x = let (v, n) = next x in (v :: takeDel k n)

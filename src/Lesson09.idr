module Lesson09

import Data.List
import Data.List.Views
import Data.Nat

%default total

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> (ListLast (xs ++ [x]))

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case (listLast xs) of
                          Empty => (NonEmpty [] x)
                          (NonEmpty ys y) => (NonEmpty (x :: ys) y)

-- f : List a -> Int
-- f (xs ++ [x]) = ?f_rhs

describeHelper : (input: List Int) -> (form : (ListLast input)) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non empty, last one " ++ show x

describe' : (input: List Int) -> String
describe' input = (describeHelper input ((listLast input)))

describe : (input: List Int) -> String
describe input with (listLast input)
  describe [] | Empty = "Empty"
  describe (xs ++ [x]) | (NonEmpty xs x) = "Non empty, last one " ++ show x

describe'' : (input: List Int) -> String
describe'' input = case (listLast input) of
                        Empty => "Empty"
                        (NonEmpty xs x) => "Non empty, last one " ++ show x

covering
myReverse : List a -> List a
myReverse xs with ((listLast xs))
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

-- mergeSort : Ord a => List a -> List a
-- mergeSort [] = []
-- mergeSort [x] = [x]
-- mergeSort (left ++ right) = merge (mergeSort left) (mergeSort right)

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (left : List a) -> (right: List a) -> (SplitList (left ++ right))

splitList : (input : List a) -> (SplitList input)
splitList input = splitList' input input
  where
    splitList' : List a -> (input : List a) -> (SplitList input)
    splitList' _ [] = SplitNil
    splitList' _ [x] = SplitOne {x=x}
    splitList' (_ :: _ :: counter) (item :: items) = case splitList' counter items of
                                                          SplitNil => SplitOne
                                                          SplitOne {x} => SplitPair [item] [x]
                                                          (SplitPair left right) => SplitPair (item :: left) right
    splitList' _ items = (SplitPair [] items)

covering
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (left ++ right) | (SplitPair left right) = merge (mergeSort left) (mergeSort right)

data MySnocList : List a -> Type where
  MyEmpty : MySnocList []
  MySnoc : (x ,xs : _) -> (rec : MySnocList xs) -> MySnocList (xs ++ [x])

snocListHelper : {input : _} -> (snoc : MySnocList input) -> (rest : List a) -> MySnocList (input ++ rest)
snocListHelper snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelper snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in (snocListHelper ((MySnoc x input snoc)) xs)

snocList' : (xs : List a ) -> MySnocList xs
snocList' xs = snocListHelper MyEmpty xs

reverse'' : List a -> List a
reverse'' xs with (snocList' xs)
  reverse'' [] | MyEmpty = []
  reverse'' (ys ++ [x]) | (MySnoc x ys rec) = x :: (reverse'' ys) | rec

mergeSort'' : Ord a => List a -> List a
mergeSort'' input with (splitRec input)
  mergeSort'' [] | SplitRecNil = []
  mergeSort'' [x] | (SplitRecOne x) = [x]
  mergeSort'' (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
    = merge (mergeSort'' lefts | lrec) (mergeSort'' rights | rrec)

-- data TakeN : List a -> Type where
--   Fewer : TakeN xs
--   Exact : (n_xs : List a) -> {rest : _} -> TakeN (n_xs :: rest)

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs

-- groupBy : (n : Nat) -> (xs : List a) -> List (List a)

-- halves : List a -> (List a, List a)

-- data TakeN : List a -> Type where
--   Fewer : TakeN xs
--   Exact : (n_xs : List a) -> {rest : _} -> TakeN (n_xs ++ rest)

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN 0 xs = Exact []
-- takeN (S k) [] = Fewer
-- takeN (S k) (x :: xs) = case takeN k xs of
--                              Fewer => Fewer
--                              (Exact n_xs) => Exact (x :: n_xs)

-- covering
-- groupBy : (n : Nat) -> (xs : List a) -> List (List a)
-- groupBy n xs with (takeN n xs)
--   groupBy n [] | Fewer = []
--   groupBy n xs | Fewer = [xs]
--   groupBy 0 (n_xs ++ rest) | (Exact n_xs) = []
--   groupBy n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupBy n rest

-- halves : List a -> (List a, List a)
-- halves xs = let
--   half_size = (length xs) `div` 2
--   in case takeN half_size xs of
--           Fewer => ([], []) -- IMPOSSIBLE
--           (Exact n_xs {rest}) => (n_xs, rest)

-- data TakeN : List a -> Type where
--   Fewer : TakeN xs
--   Exact : (xs : _) -> (n_xs : TakeN xs) -> (rest : _) -> TakeN (xs ++ rest)

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN 0 xs = Exact [] Fewer xs
-- takeN (S k) [] = Fewer
-- takeN (S k) (x :: xs) = case takeN k xs of
--                       Fewer => Fewer
--                       (Exact ys n_xs rest) => ?i (Exact (x :: ys) n_xs rest)

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (xs : List a) -> {rest : List a} -> TakeN rest -> TakeN (xs ++ rest)

takeNHelper : (n : Nat) -> (xs : List a) -> (fuel : List a) -> TakeN xs
takeNHelper 0 _ _ = Exact [] Fewer
takeNHelper _ [] _ = Fewer
takeNHelper _ _ [] = Fewer
takeNHelper n @ (S k) (y :: xs) (x :: ys) = case takeNHelper k xs ys of
                                             Fewer => Fewer
                                             (Exact zs {rest} z) => Exact (y :: zs) (takeNHelper n rest ys)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN n xs = takeNHelper n xs xs

groupBy : (n : Nat) -> (xs : List a) -> List (List a)
groupBy n xs with (takeN n xs)
  groupBy _ [] | Fewer = []
  groupBy _ xs | Fewer = [xs]
  groupBy n (ys ++ rest) | (Exact ys y) = ys :: groupBy n rest | y

module Lesson05

import Data.Vect

%default total

occurences : Eq ty => (item: ty) -> (values: List ty) -> Nat
occurences item [] = 0
occurences item (x :: xs) = case item == x of
                                 False => (occurences item xs)
                                 True => 1 + (occurences item xs)

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

data Tree e = Empty | Node (Tree e) e (Tree e)

Eq e => Eq (Tree e) where
    (==) Empty Empty = True
    (==) (Node l v r) (Node l' v' r') = l == l' && r == r' && v == v'
    (==) _ _ = False

tree1 : Tree Nat
tree1 = Node Empty 10 (Node Empty 15 (Node Empty 20 Empty))

record Album where
    constructor MkAlbum
    artist : String
    title : String
    year : Integer

a1 : Album
a1 = (MkAlbum "A1" "t1" 2000)

a2 : Album
a2 = (MkAlbum "A1" "t2" 2000)

Eq Album where
  (==) (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) = a1 == a2 && t1 == t2 && y1 == y2

Ord Album where
    compare (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) =
        case compare a1 a2 of
            EQ => case compare t1 t2 of
                EQ => compare y1 y2
                diff_t => diff_t
            diff_art => diff_art

Show Album where
    show (MkAlbum artist title year) = artist ++ " " ++ title ++ " (" ++ show year ++ ")"

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Abs (Expr num)
              | Neg (Expr num)

expr : Expr Nat
expr = Add (Val 1) (Mul (Val 4) (Abs (Neg (Val 6))))

eval : (Num num, Integral num, Abs num, Neg num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Abs x) = abs (eval x)
eval (Neg x) = -1 * (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    a * b = Mul a b
    fromInteger = Val . fromInteger

Num ty => Abs (Expr ty) where
    abs = Abs

Cast (Maybe a) (List a) where
    cast Nothing = []
    cast (Just x) = [x]

Foldable (\a => Tree a) where
    foldr f acc Empty = acc
    foldr f acc (Node left e right) =
        let leftFold = foldr f acc left
            rightFold = foldr f leftFold right in
            f e rightFold

-- 1. Functor Expr
-- 2. prettyPrint

Functor Expr where
    map f (Val x) = Val (f x)
    map f (Add x y) = Add (map f x) (map f y)
    map f (Mul x y) = Mul (map f x) (map f y)
    map f (Abs x) = Abs (map f x)
    map f (Neg x) = Neg (map f x)

prettyPrint: Show a => Expr a -> String
prettyPrint (Val x) = show x

prettyPrint (Add x y@(Neg _)) = "\{prettyPrint  x} + (\{prettyPrint y})"
prettyPrint (Add x y) = "\{prettyPrint  x} + \{prettyPrint y}"

prettyPrint (Mul x@(Add _ _) y@(Add _ _)) = "(\{prettyPrint x}) * (\{prettyPrint y})"
prettyPrint (Mul x@(Add _ _) y) = "(\{prettyPrint x}) * \{prettyPrint y}"
prettyPrint (Mul x y@(Add _ _)) = "\{prettyPrint x} * (\{prettyPrint y})"
prettyPrint (Mul x y@(Neg _)) = "\{prettyPrint  x} * (\{prettyPrint y})" -- more cases
prettyPrint (Mul x y) = "\{prettyPrint x} * \{prettyPrint y}"

prettyPrint (Abs x) = "|\{prettyPrint x}|"
prettyPrint (Neg (Val x)) = "-\{show x}"
prettyPrint (Neg x@(Abs _)) = "-\{prettyPrint x}"
prettyPrint (Neg x) = "-(\{prettyPrint x})"

fix : Expr a -> Expr a
fix x @ (Val _) = x
fix (Add x y) = Add (fix x) (fix y)
fix (Mul x y) = Mul (fix x) (fix y)
fix (Abs (Abs x)) = Abs $ fix x
fix (Abs (Neg x)) = Abs $ fix x
fix (Abs x) = Abs $ fix x
fix (Neg (Neg x)) = fix x
fix (Neg x) = Neg $ fix x

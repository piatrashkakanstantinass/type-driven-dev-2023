module Lesson07

import Data.Vect
import Data.Vect.Elem
import Data.String
import Decidable.Equality

%default total

append' : Vect n e -> Vect m e -> Vect (n+m) e
append' [] ys = ys
append' (x :: xs) ys = x :: append' xs ys

append_nil : Vect m e -> Vect (plus m 0) e
append_nil xs = rewrite plusCommutative m 0 in xs

append_xs : Vect (S (plus m len)) e -> Vect (plus m (S len)) e
append_xs xs = rewrite sym (plusSuccRightSucc m len) in xs

append : Vect n e -> Vect m e -> Vect (m+n) e
append [] ys = append_nil ys
append (x :: xs) ys = append_xs $ x :: append xs ys

test : Void -> Vect 1 Int
test x = [42]

test' : Void -> 3 = 2
test' _ impossible

test'' : 2 + 2 = 6 -> Void
test'' Refl impossible

--test''' : 2 + 2 = 4 -> Void
--test''' Refl impossible

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

no' : (S k = S j) -> k = j
no' Refl = Refl

noRec : (k = j -> Void) -> S k = S j -> Void
noRec f c = f (no' c)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc
checkEqNat (S k) 0 = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes (cong S prf)
                              (No contra) => No (noRec contra)

exactLenght : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLenght {m} len input = case decEq m len of
                             (Yes prf) => Just $ rewrite sym prf in input
                             (No _) => Nothing

checkEqInt : (num1 : Int) -> (num2 : Int) -> Dec (num1 = num2)
checkEqInt num1 num2 = ?checkEqInt_rhs

void : Nat -> Void
void 0 = believe_me 0
void (S k) = void k

void' : Void
void' = believe_me 0

-- headUnequal : DecEq a => (xs : Vect n a) -> (ys: Vect n a) -> (contr : (x=y) -> Void) -> ((x :: xs) = (y :: ys) -> Void)
-- tailUnequal : DecEq a => (xs : Vect n a) -> (ys: Vect n a) -> (contr : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys) -> Void)

headUnequal : DecEq a => (xs : Vect n a) -> (ys: Vect n a) -> (contr : (x=y) -> Void) -> ((x :: xs) = (y :: ys) -> Void)
headUnequal xs ys contr prf = contr $ cong head prf

tailUnequal : DecEq a => (xs : Vect n a) -> (ys: Vect n a) -> (contr : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys) -> Void)
tailUnequal xs ys contr prf = contr $ cong tail prf

data Vec : (len : Nat) -> (elem : Type) -> Type where
    Nil : Vec 0 elem
    (::) : (x: elem) -> (xs : Vec len elem) -> Vec (S len) elem

headUnequalVec : DecEq a => (xs : Vec n a) -> (ys: Vec n a) -> (contr : (x=y) -> Void) -> ((x :: xs) = (y :: ys) -> Void)
headUnequalVec xs xs contr Refl = contr Refl

tailUnequalVec : DecEq a => (xs : Vec n a) -> (ys: Vec n a) -> (contr : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys) -> Void)
tailUnequalVec xs xs contr Refl = contr Refl


DecEq a => DecEq (Vec n a) where
    decEq [] [] = Yes Refl
    decEq (x :: xs) (y :: ys) = case decEq x y of
                                     (Yes Refl) => case decEq xs ys of
                                                       (Yes Refl) => Yes Refl
                                                       (No contra) => No $ tailUnequalVec xs ys contra
                                     (No contra) => No $ headUnequalVec xs ys contra
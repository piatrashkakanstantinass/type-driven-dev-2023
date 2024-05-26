module Lesson14.Main
import Data.Vect
import Lesson14.Undestroyable
import Data.Linear.LMaybe
import Data.Linear.Notation

%default total


-- Erasure (Q=0)

f1 : Vect n a
f1 = ?f1_rhs

f2 : {n : Nat} -> Vect n a
f2 = ?f2_rhs

failing
    f2' : {0 n : Nat} -> Vect n a
    f2' {n} = f2 {n = n} --?f2'_rhs

f2'' : {0 n : _} -> {0 a : _} -> Vect n a
f2'' {n} = f1 {n = n}

failing
    f2''' : {0 n : _} -> {0 a : _} -> Vect n a
    f2''' {n = 0} = ?f2'''_rhs_0
    f2''' {n = (S k)} = ?f2'''_rhs_1

0 f3 : {0 n : _} -> {0 a : _} -> {0 v : a} -> Vect n a
f3 {n = 0} = []
f3 {n = (S k)} {v=v} = v :: f3 {n=k} {v=v}

failing
    MkNatVec : (0 n : Nat) -> {0 a : Type} -> Type -- passes with 0
    MkNatVec n {a} = Vect n a

data Some : Type -> Type where
    MkSome : (0 x : Nat) -> Some a

MkSomeT : (0 n : Nat) -> Some a
MkSomeT n = MkSome n

failing
    MkSomeT' : (0 n : Nat) -> Some a
    MkSomeT' 0 = ?MkSomeT'_0 -- MkSome 0
    MkSomeT' (S k) = ?MkSomeT'_1 -- MkSome (S k)

0 MkSomeT'' : (0 n : Nat) -> Some a
MkSomeT'' 0 = ?MkSomeT''_0 -- MkSome 0
MkSomeT'' (S k) = ?MkSomeT''_1


-- Linearity (Q=1)

-- Linear implication -@

drop' : a -> ()
drop' _ = ()

dupl' : a -> (a, a)
dupl' x = (x, x)

failing
    drop : (1 x : a) -> ()
    drop x = ()

failing
    dupl : (1 _ : a) -> LPair a a
    dupl x = x # x


-- How to destroy?

data MyThing = MkMyThing

failing
    destroyMyThing : (1 _ : MyThing) -> ()
    destroyMyThing _ = ()

destroyMyThing : (1 _ : MyThing) -> ()
destroyMyThing MkMyThing = ()

-- Hide constructors to protect a value.

failing
    destroyUndT : (1 _ : UndT) -> ()
    destroyUndT x = ()

failing
    destroyUndT : (1 _ : UndT) -> ()
    destroyUndT UndV = ()

failing
    destroyUndT : (1 _ : UndT) -> Nat -> ()
    destroyUndT x n =
        let n = n + n in
        let a = Data.Linear.LMaybe.Just x in
        ()

failing
    destroyUndT : (1 _ : UndT) -> Nat -> ()
    destroyUndT x n =
        let n = n + n in
        let a = Data.Linear.LMaybe.Just x in
        case a of
            Nothing => ()
            (Just y) => ()

data UndBox : Type where
    MkUndBox : (1 _ : UndT) -> UndBox

failing
    destroyUndT : (1 _ : UndT) -> ()
    destroyUndT x = let a = MkUndBox x in ()

-- destroyUndT : (1 _ : UndT) -> (UndBox, UndBox)
-- destroyUndT x = let a = MkUndBox x in ()

{- Create ? -}


createLinInt : () -> ()
createLinInt () =
    let 1 x = 132 in
    ?createLinInt_rhs

failing
    createLinUnd : () -> ()
    createLinUnd () =
        let 1 a = UndV in
        ?createLinUnd_rhs


createLinUnd : () -> ()
createLinUnd () =
    let 1 a = mkUnd in
    ?createLinUnd_rhs

createLinUnd' : () -> ()
createLinUnd' () =
    let a = mkUnd in
    () -- Sad, we lost the value.


createLinUnd'' : () -> ()
createLinUnd'' () =
    let 0 a = mkUndH in -- Sad, we lost the value.
    ()

createLinUnd''' : () -> ()
createLinUnd''' () =
    let a = mkUndH in -- Sad, we lost the value.
    ?createLinUnd'''_rhs

undProtoIO : IO ()
undProtoIO = mkUndIO $ \u => let () = dropUnd u in pure ()

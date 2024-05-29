module Lesson15.StackMachine

import Data.List

%default total

data Binop = Plus | Times

data Exp : Type where
    Const : Nat -> Exp
    Op : Binop -> Exp -> Exp -> Exp

binopDenote : Binop -> Nat -> Nat -> Nat
binopDenote Plus k j = k + j
binopDenote Times k j = k * j

expDenote : Exp -> Nat
expDenote (Const k) = k
expDenote (Op x y z) = (binopDenote x) (expDenote y) (expDenote z)

test : Exp
test = Op Times (Op Plus (Const 2) (Const 2)) (Const 7)

data Instr : Type where
    IConst : Nat -> Instr
    IOp : Binop -> Instr

Prog = List Instr
Stack = List Nat

instrDenote : Instr -> Stack -> Maybe Stack
instrDenote (IConst k) ks = Just (k :: ks)
instrDenote (IOp x) (a1 :: a2 :: s') = Just ((((binopDenote x) a1 a2) :: s'))
instrDenote (IOp x) _ = Nothing

progDenote : Prog -> Stack -> Maybe Stack
progDenote [] ks = Just ks
progDenote (x :: xs) ks = case instrDenote x ks of
                               Nothing => Nothing
                               (Just y) => progDenote xs y

compile : Exp -> Prog
compile (Const k) = [IConst k]
compile (Op x e1 e2) = (compile e2) ++ (compile e1) ++ [IOp x]

appendAssociativeRev : (l, c, r : List a) -> (l ++ c) ++ r = l ++ (c ++ r)
appendAssociativeRev l c r = rewrite sym (appendAssociative l c r) in Refl

compileCorrect : (e : Exp) -> (p : Prog) -> (s : Stack) ->
                 progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compileCorrect (Const k) p s = Refl
compileCorrect (Op x e1 e2) p s = rewrite appendAssociativeRev (compile e2) (compile e1 ++ [IOp x]) p in
                                  rewrite compileCorrect e2 ((compile e1 ++ [IOp x]) ++ p) s in
                                  rewrite appendAssociativeRev (compile e1) [IOp x] p in
                                  rewrite compileCorrect e1 ([IOp x] ++ p) (expDenote e2 :: s) in
                                  Refl
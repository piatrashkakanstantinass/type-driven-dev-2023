module StackMachine where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Data.List.Properties using (++-assoc)

data Binop : Set where
  Plus : Binop
  Times : Binop

data Exp : Set where
  Const : ℕ → Exp
  Op : Binop → Exp → Exp → Exp

binopDenote : Binop → ℕ → ℕ → ℕ
binopDenote Plus a1 a2 = a1 + a2
binopDenote Times a1 a2 = a1 * a2

expDenote : Exp → ℕ
expDenote (Const x) = x
expDenote (Op x e₁ e₂) =  (binopDenote x) (expDenote e₁) (expDenote e₂)

data Instr : Set where
  IConst : ℕ → Instr
  IOp : Binop → Instr

Prog = List Instr
Stack = List ℕ

instrDenote : Instr → Stack → Maybe Stack
instrDenote (IConst x) s = just (x ∷ s)
instrDenote (IOp x) (x₁ ∷ x₂ ∷ s) = just ((binopDenote x x₁ x₂) ∷ s)
instrDenote (IOp x) _ = nothing

progDenote : Prog → Stack → Maybe Stack
progDenote [] s = just s
progDenote (x ∷ p) s with instrDenote x s
progDenote (x ∷ p) s | nothing = nothing
progDenote (x ∷ p) s | just y = progDenote p y

compile : Exp → Prog
compile (Const x) =  (IConst x)  ∷ []
compile (Op x e₁ e₂) = ( compile e₂ ) ++ ( compile e₁ ) ++ (IOp x ∷ [])

compileCorrect : ∀ (e : Exp) → ∀ (p : Prog) → ∀ (s : Stack) →
                 progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)
compileCorrect (Const x) p s = refl
compileCorrect (Op x e₁ e₂) p s rewrite ++-assoc (compile e₂) (compile e₁ ++ IOp x ∷ []) p |
                                compileCorrect e₂ ((compile e₁ ++ IOp x ∷ []) ++ p) s |
                                ++-assoc (compile e₁) (IOp x ∷ []) p |
                                compileCorrect e₁ (IOp x ∷ [] ++ p) (expDenote e₂ ∷ s)
                                = refl 

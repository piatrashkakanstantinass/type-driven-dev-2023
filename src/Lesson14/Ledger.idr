module Lesson14.Ledger
import Data.Nat
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.LList
%default total

public export
data User : Type where
    MkUser : Nat -> User

Eq User where
    (==) (MkUser a) (MkUser b) = a == b

export
data Coin : Type where
    MkCoin : (owner : User) -> (amt : Nat) -> Coin

export
data Tx : Type where
    MkTx : (inp : Coin) -> (out : LList Coin) -> Tx

export
record Ledger where
    constructor MkLedger
    coins : List Coin

export
genesisLedger : User -> Nat -> Ledger
genesisLedger usr amt = MkLedger [(MkCoin usr amt)]


-- NOTE: We con't solve the problem here of `3 - 7 = 0`.
export
splitCoin :
    (1 _ : Coin) ->
    (rcp : User) ->
    (amt : Nat) ->
    (1 f : ((1 c1 : Coin) -> (1 c2 : Coin) -> LList Coin)) -> LList Coin
splitCoin (MkCoin o k) rcp amt f = f (MkCoin o (minus k amt)) (MkCoin rcp amt)

failing -- f is linear, but if we have not enough of coins, we will not call it.
    newTx : Ledger -> User -> Nat -> (1 f : ((1 _ : Coin) -> Tx)) -> LMaybe Tx
    newTx ledger owner amount f = Nothing

-- Remove 1 from f for newTx.

newTxOfCoins : List Coin -> User -> Nat -> ((1 _ : Coin) -> LList Coin) -> LMaybe Tx
newTxOfCoins [] own amt f = Nothing
newTxOfCoins (c@(MkCoin cOwn cAmt) :: coins) own amt f =
    case isLTE amt cAmt of
        (Yes prf) => case cOwn == own of
                        True => Just (MkTx c (f c))
                        False => newTxOfCoins coins own amt f
        (No contra) => newTxOfCoins coins own amt f

export
newTx : Ledger -> User -> Nat -> (f : ((1 _ : Coin) -> LList Coin)) -> LMaybe Tx
newTx (MkLedger coins) owner amount f = newTxOfCoins coins owner amount f


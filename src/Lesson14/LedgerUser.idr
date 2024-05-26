module Lesson14.LedgerUser
import Lesson14.Ledger
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.LList

-- We cannot loose the coins here.
test : ()
test =
    let u1 = MkUser 1 in
    let u2 = MkUser 2 in
    let l = genesisLedger u1 100 in
    let tx = newTx l u1 10 $ \c => splitCoin c u2 3 $ \c1, c2 => [c1, c2] in
    ?lookHere

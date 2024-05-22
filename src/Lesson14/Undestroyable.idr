module Lesson14.Undestroyable
%default total

export -- Non public!
data UndT = UndV

export
mkUnd : UndT
mkUnd = UndV

export
dropUnd : (1 _ : UndT) -> ()
dropUnd UndV = ()

public export
data UndH : Type where
    MkUndH : (1 _ : UndT) -> UndH

export
mkUndH' : UndH
mkUndH' = MkUndH UndV

export
mkUndH'' : UndH
mkUndH'' = let 1 v = UndV in MkUndH v

export
1 mkUndH : UndH
mkUndH = MkUndH UndV

export
mkUndIO : (1 f : ((1 _ : UndT) -> IO ())) -> IO ()
mkUndIO f = f UndV



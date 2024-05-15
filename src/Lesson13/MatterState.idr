module Lesson13.MatterState

%default total

data MatterState = Solid | Liquid | Gas

data MatterTransition : Type -> (from : MatterState) -> (to : MatterState) -> Type where
  Melt : MatterTransition () Solid Liquid
  Freeze : MatterTransition () Liquid Solid
  Boil : MatterTransition () Liquid Gas
  Condense : MatterTransition () Gas Liquid
  (>>=) : MatterTransition a from temp -> (a -> MatterTransition b temp to) -> MatterTransition b from to
  (>>) : MatterTransition a from temp -> MatterTransition b temp to -> MatterTransition b from to

testTransition : MatterTransition () Solid Liquid
testTransition = do
  Melt
  Boil
  Condense
  Freeze
  Melt

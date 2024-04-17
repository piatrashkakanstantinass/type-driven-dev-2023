module Lesson10

import Data.Vect

%default total

infixr 5 .+.

public export 
data Schema = SString
            | SInt
            | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

-- record DataStore' (t: Type) where

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
emp : DataStore schema
emp = (MkData 0 [])

export
addToStore : (value : SchemaType schema) -> 
             (store : DataStore schema) ->
             DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $ 
            addToStore ("Venus", "Venera", 1961) $
            emp

public export
data StoreView : (schema : _) -> DataStore schema -> Type where
  SNil : StoreView schema emp
  SAdd : (value, store: _) -> (rec : StoreView schema store) ->
         StoreView schema ((addToStore value store))

storeViewHelp : {size : _} -> 
               (items : Vect size ((SchemaType schema))) ->
                StoreView schema (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd x _ (storeViewHelp xs)

storeView : (store : DataStore schema) -> StoreView schema store
storeView (MkData size items) = storeViewHelp items

listItems : DataStore schema -> List (SchemaType schema)
listItems x with (storeView x)
  listItems x | SNil = []
  listItems (addToStore value store) | (SAdd value store rec) =
    value :: listItems store | rec

-- p and q => p or q

i1 : (p, q) -> Either p q
i1 x = Left (fst x)

i2 : Either (p, q) r ->(Either p r, Either q r)
i2 (Left x) = (Left (fst x), Left (snd x))
i2 (Right x) = (Right x, Right x)

i3 : (Either p r, Either q r) -> Either (p, q) r
i3 ((Left x), (Left y)) = Left (x, y)
i3 (_, (Right y)) = Right y
i3 ((Right x), _) = Right x

i4 : (p -> r) -> ((q -> r) -> (Either p q -> r))
i4 f g (Left x) = f x
i4 f g (Right x) = g x

i5 : p -> Not (Not p)
i5 x f = f x

i6 : Not (p, q) -> (p -> Not q)
i6 f x y = f (x, y)

i7 : (Not (Either p q) -> (Not p, Not q), (Not p, Not q) -> Not (p, q))
i7 = (\f => (\x => f (Left x), \x => f (Right x)), \x => \y => fst x (fst y))

i8' : Not (p, q) -> Either (Not p) (Not q)

i8'' : Either (Not p) (Not q) -> Not (p, q)
i8'' (Left x) y = x (fst y)
i8'' (Right x) y = x (snd y)

i8 : (Not (p, q) -> Either (Not p) (Not q), Either (Not p) (Not q) -> Not (p, q))
i8 = (i8', i8'')

i9 : (p -> q) -> (Not q -> Not p)
i9 f g x = g (f x)

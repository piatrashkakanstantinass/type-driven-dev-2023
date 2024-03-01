module Lesson04

import Data.String
import Data.Vect
import System.REPL

%default total

-- readVect' : {l : Nat} -> IO (Vect l String)
-- readVect' = do x <- getLine
--                case x == "" of
--                  True => pure []
--                  False => do xs <- readVect'
--                              pure x :: xs

covering
readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              case x == "" of
                 True => pure (_ ** [])
                 False => do (_ ** xs) <- readVect
                             pure (_ ** x :: xs)

dp : (len ** Vect len String)
dp = (2 ** ["labas", "medis"])

Position : Type
Position = (Double, Double)

-- adder 0 10 = 10
-- adder 1 10 10 = 20
-- adder 2 10 5 5 = 20

AdderType : (numargs: Nat) -> Type
AdderType 0 = Int
AdderType (S k) = (next : Int) -> AdderType k

adder : (numargs: Nat) -> (acc: Int) -> AdderType numargs
adder 0 acc = acc
adder (S k) acc = \next => adder k (acc + next)

-- printf("%s = %d", "el", 42)

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = (i: Int) -> PrintfType x
PrintfType (Str x) = (s: String) -> PrintfType x
PrintfType (Lit str x) = (PrintfType x)
PrintfType End = String

printFmt : (fmt : Format) -> (acc: String) -> PrintfType fmt
printFmt (Number x) acc = \i => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s => printFmt x (acc ++ s)
printFmt (Lit str x) acc = printFmt x (acc ++ str)
printFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat (x :: xs) = Lit (pack [x]) (toFormat xs)

-- printf "%s = %d" -> String -> Numb -> Strin
-- printf "%d" -> Numb -> Strin
-- printf "=" -> Strin

infixr 5 .+.

data Schema = SString
           | SInt
           | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToTail : Vect s t -> t -> Vect (S s) t
addToTail [] item = [item]
addToTail (x :: xs) item = x :: addToTail xs item

addToStore : (store : DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData s size items) item =
     MkData s (S size) (addToTail items item)

escapeStr : String -> String
escapeStr str = pack $ reverse $ foldl (\acc, c => case c of
                                              a @ '\\' => (a :: a :: acc)
                                              a @ '"' => (a :: '\\' :: acc)
                                              a => a :: acc) [] (unpack str)

display : {schema : Schema} -> SchemaType schema -> String
display {schema = SString} x = "\"" ++ escapeStr x ++ "\""
display {schema = SInt} x = show x
display {schema = (y .+. z)} (x, w) = "(" ++ display x ++ "," ++ display w ++ ")"

getEntry : (pos : Nat) -> (dataStore: DataStore) -> Maybe String
getEntry pos dataStore = case natToFin pos (size dataStore) of
                              Nothing => Nothing
                              (Just x) => Just(display(index x (items dataStore)))

emptyDataStore : DataStore
emptyDataStore = MkData SString 0 []

data Parser : Type -> Type where
    MkParser : (List Char -> Maybe (a, List Char)) -> Parser a

parseP : Parser a -> List Char -> Maybe (a, List Char)
parseP (MkParser f) = f

Functor Parser where
    map f p = MkParser (\inp => case parseP p inp of
                                    Just (a,inp') => Just $ (f a, inp')
                                    Nothing => Nothing)

Applicative Parser where
    af <*> aa = MkParser (\inp => case parseP af inp of
                                      Nothing => Nothing
                                      (Just (f, inp')) => parseP (map f aa) inp')
    pure v = MkParser (\inp => Just (v, inp))

Monad Parser where
    p >>= f = MkParser (\inp => case parseP p inp of
                                     Nothing => Nothing
                                     (Just (v, inp')) => parseP (f v) inp')

Alternative Parser where
    a <|> b = MkParser (\inp => case parseP a inp of
                                        Nothing => parseP b inp
                                        v => v)
    empty = MkParser (\_ => Nothing)

itemParser : Parser Char
itemParser = MkParser (\inp => case inp of
                                   [] => Nothing
                                   (x :: xs) => Just (x, xs))

charParser : Char -> Parser Char
charParser c = MkParser (\inp => case parseP itemParser inp of
                                      Nothing => Nothing
                                      (Just (item, inp')) => case item == c of
                                                                  False => Nothing
                                                                  True => Just (item, inp'))

stringParser : String -> Parser String
stringParser str = MkParser (\inp => case take (length str) inp == (unpack str) of
                                            True => Just (str, drop (length str) inp)
                                            False => Nothing)

                                                                
endParser : Parser ()
endParser = MkParser (\inp => case null inp of
                                    True => Just ((), [])
                                    False => Nothing)

optional : Alternative f => f a -> f (Maybe a)
optional x = map Just x <|> pure Nothing

whitespaceParser : Parser (List Char)
whitespaceParser = MkParser (\inp => let
    res = takeWhile (\c => isSpace c) inp
    resLen = length res
    rest = drop resLen inp
    in case resLen == 0 of
        False => Just (res, rest)
        True => Nothing)

stupleParser : Parser a -> Parser b -> Parser (a, b) 
stupleParser x y = do
    _ <- charParser '('
    _ <- optional whitespaceParser
    r1 <- x
    _ <- optional whitespaceParser
    _ <- charParser ','
    _ <- optional whitespaceParser
    r2 <- y
    _ <- optional whitespaceParser
    _ <- charParser ')'
    pure (r1, r2)

sstringParser : Parser String
sstringParser = do
        _ <- charParser '"'
        res <- MkParser (\inp => parseInside inp [])
        _ <- charParser '"'
        pure res
    where parseInside : List Char -> List Char -> Maybe (String, List Char)
          parseInside [] acc = Just (pack $ reverse acc, [])
          parseInside ('\\' :: []) acc = Nothing
          parseInside ('\\' :: ('"' :: ys)) acc = parseInside ys ('"' :: acc)
          parseInside ('\\' :: (y :: ys)) acc = parseInside ys (y :: '\\' :: acc)
          parseInside a @ ('"' :: xs) acc = Just (pack $ reverse acc, a)
          parseInside (x :: xs) acc = parseInside xs (x :: acc)

sintParser : Num a => Neg a => Parser a
sintParser = MkParser (\inp => let
    res = takeWhile (\c => isDigit c) inp
    resLen = length res
    rest = drop resLen inp
    in case parseInteger (pack res) of
            Nothing => Nothing
            (Just x) => Just (x, rest))

cmdArgParser : Parser a -> Parser a
cmdArgParser p = do
    _ <- optional whitespaceParser
    r <- p
    _ <- optional whitespaceParser
    endParser
    pure r

schemaParser : (s: Schema) -> Parser (SchemaType s)
schemaParser SString = sstringParser
schemaParser SInt = sintParser
schemaParser (x .+. y) = stupleParser (schemaParser x) (schemaParser y)

data Command : Schema -> Type where
    Add : SchemaType s -> Command s
    Get : Nat -> Command s
    Quit : Command s
    Size : Command s
    SetSchema : Schema -> Command s

schemaTypeStringParser : Parser Schema
schemaTypeStringParser = do
    _ <- stringParser "string"
    pure SString

schemaTypeIntParser : Parser Schema
schemaTypeIntParser = do
    _ <- stringParser "int"
    pure SInt

mutual
    covering
    schemaTypeTupleParser : Parser Schema
    schemaTypeTupleParser = do
        (a, b) <- stupleParser schemaTypeParser schemaTypeParser
        pure (a .+. b)

    covering
    schemaTypeParser : Parser Schema
    schemaTypeParser = schemaTypeStringParser <|> schemaTypeIntParser <|> schemaTypeTupleParser

covering
parseCommand : (s: Schema) -> String -> String -> Maybe (Command s)
parseCommand s "add" str = parseP (cmdArgParser $ schemaParser s) (unpack str) >>= (\r => Just $ Add (fst r))
parseCommand _ "get" str = case all isDigit (unpack str) of
                               False => Nothing
                               True => Just (Get (cast str))
parseCommand _ "quit" _ = Just Quit
parseCommand _ "size" _ = Just Size
parseCommand _ "setSchema" str = parseP (cmdArgParser schemaTypeParser) (unpack str) >>= (\r => Just $ SetSchema (fst r))
parseCommand _ _ _ = Nothing

covering
parse : (s: Schema) -> String -> Maybe (Command s)
parse schema str = case span (/= ' ') str of
                        (cmd, arg) => parseCommand schema cmd (ltrim arg)

processCommand : (d: DataStore) -> (Command d.schema) -> Maybe (String, DataStore)
processCommand d (Add x) = Just ("Added " ++ display x ++ "\n", addToStore d x)
processCommand x (Get i) = case getEntry i x of
                                 Nothing => Just ("Invalid index\n", x)
                                 (Just v) => Just (v ++ "\n", x)
processCommand _ Quit = Nothing
processCommand x Size = Just ((show $ length $ items x) ++ "\n", x)
processCommand d (SetSchema s) = Just $ ("Using new schema. All previous data is gone!\n", MkData s 0 [])

covering
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput x str = case parse x.schema str of
                          Nothing => Just ("Failed to parse command\n", x)
                          (Just cmd) => processCommand x cmd

covering
main : IO ()
main = replWith (emptyDataStore) ">>> " processInput

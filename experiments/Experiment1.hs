{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GADTs, Arrows #-}

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow

data Parser' p a b where
  Id :: Parser' p a a
  Arr :: (a -> x) -> Parser p x b -> Parser' p a b
  Port :: Parser p a1 x -> Parser p (Either x a2, a3) b -> Parser' p (Either a1 a2, a3) b
  Match :: Char -> Parser p a b -> Parser' p a b
  Free :: p (Parser p) a1 x -> Parser p (x, a2) b -> Parser' p (a1, a2) b

instance Category (Parser' p) where
  id = Id
  k . Id = k 
  k . (Match c p) = Match c (Parser [k] . p)
  k . (Arr f p) = Arr f (Parser [k] . p)
  k . (Port p q) = Port p (Parser [k] . q)
  k . (Free x p) = Free x (Parser [k] . p)

assocr :: ((a,b),c) -> (a,(b,c))
assocr ((a,b),c) = (a,(b,c))

assocl :: (a,(b,c)) -> ((a,b),c)
assocl (a,(b,c)) = ((a,b),c)

instance Arrow (Parser' p) where
  arr f = Arr f id
  first Id = Id
  first (Arr f k) = Arr (first f) (first k)
  first (Port p k) = Arr assocr (Parser [Port p (Parser [Arr assocl (first k)])])
  first (Match c k) = Match c (first k)
  first (Free x k) = Arr assocr (Parser [Free x (Parser [Arr assocl (first k)])])

newtype Parser p a b = Parser [Parser' p a b]

instance ArrowZero (Parser p) where
  zeroArrow = Parser []
  
instance ArrowPlus (Parser p) where
  Parser ps <+> Parser qs = Parser (ps ++ qs)

instance Category (Parser p) where
  id = Parser [Id]
  p0 . Parser qs = foldr (<+>) zeroArrow $ map (composeL p0) qs where
    composeL k Id = k 
    composeL k (Match c p) = Parser [Match c (k . p)]
    composeL k (Arr f p) = Parser [Arr f (k . p)]
    composeL k (Port p q) = Parser [Port p (k . q)]
    composeL k (Free x p) = Parser [Free x (k . p)]

instance Arrow (Parser p) where
  arr f = Parser [Arr f id]
  first (Parser ps) = Parser (map first ps)

instance ArrowChoice (Parser p) where
  left p = arr (,()) >>> Parser [Port p id] >>> arr fst

char :: Char -> Parser p a a
char c = Parser [Match c id]

string :: String -> Parser p a a
string [] = id
string (x:xs) = char x >>> string xs

send :: p (Parser p) a b -> Parser p a b
send x = Parser [Arr (,()) (Parser [Free x (arr fst)])]

parse :: forall p a b. (forall x y. p (Parser p) x y -> Parser p x y) -> p (Parser p) a b -> String -> a -> [b]
parse g p0 xs0 x0 = map fst $ go x0 xs0 (g p0) where
  go :: c -> String -> Parser p c d -> [(d, String)]
  go x xs (Parser ps) = go' x xs =<< ps
  go' :: c -> String -> Parser' p c d -> [(d, String)] 
  go' x xs Id = [(x, xs)]
  go' x xs (Arr f k) = go (f x) xs k
  go' y (x:xs) (Match c k) | x == c = go y xs k
  go' _ _ Match{} = []
  go' x xs (Port p k) =
    case x of
      (Left x1,y) -> do
        (x', xs') <- go x1 xs p
        go (Left x', y) xs' k
      (Right x2, y) -> go (Right x2, y) xs k
  go' x xs (Free p k) =
    case x of
      (x', y) -> go x' xs (k . arr (,y) . g p) -- TODO avoid left-recursion

-- E(l,r) ::= [4 >= l] '-' E(l,4) //4
-- | [3 >= r, 3 >= l] E(3,3) '*' E(l,4) //3
-- | [2 >= r, 2 >= l] E(2,2) '+' E(l,3) //2
-- | [1 >= l] 'if' E(0,0) 'then' E(0,0) 'else' E(0,0) //1
-- | a

guardA :: (ArrowChoice a, ArrowZero a) => a Bool ()
guardA = proc b ->
  if b
  then returnA -< ()
  else zeroArrow -< ()

data E p a b where
  E :: E p (Int, Int) Expr

data Expr = Neg Expr | Mul Expr Expr | Add Expr Expr | ITE Expr Expr Expr | A
  deriving Show

gram :: E p a b -> Parser E a b
gram E =
  proc (l, r) -> do
    guardA -< 4 >= l
    char '-' -< ()
    x <- send E -< (l, 4)    
    returnA -< Neg x
  <+> do
    guardA -< 3 >= r && 3 >= l
    x <- send E -< (3, 3)
    char '*' -< ()
    y <- send E -< (l, 4)
    returnA -< Mul x y
  <+> do
    guardA -< 2 >= r && 2 >= l
    x <- send E -< (2, 2)
    char '+' -< ()
    y <- send E -< (l, 3)
    returnA -< Add x y
  <+> do
    guardA -< 1 >= l
    string "if" -< ()
    b <- send E -< (0, 0)
    string "then" -< ()
    x <- send E -< (0, 0)
    string "else" -< ()
    y <- send E -< (0, 0)
    returnA -< ITE b x y
  <+> do
    char 'a' -< ()
    returnA -< A

main :: IO ()
main = gram `seq` pure ()
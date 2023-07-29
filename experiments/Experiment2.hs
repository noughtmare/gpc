{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Control.Applicative
import Data.Char
import Data.Type.Equality
-- import Debug.Trace
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad

data P p a = P [P' p a] deriving Functor
deriving instance (forall x. Show (p x)) => Show (P p a)

instance Applicative (P p) where
  pure x = P [Pure x]
  P ps <*> q = asum (map (`go` q) ps) where
    go (Pure f) k' = fmap f k'
    go (Match c k) k' = P [Match c (k <*> k')]
    go (Free x k) k' = P [Free x (flip <$> k <*> k')]

instance Alternative (P p) where
  empty = P []
  P ps <|> P qs = P (ps ++ qs)

data P' p a = Pure a | Match Char (P p a) | forall b. Free (p b) (P p (b -> a))
deriving instance Functor (P' p)
instance (forall x. Show (p x)) => Show (P' p a) where
  show Pure{} = "Pure"
  show (Match c k) = "Match " ++ show c ++ " (" ++ show k ++ ")"
  show (Free x k) = "Free " ++ show x ++ " (" ++ show k ++ ")"

char :: Char -> P p Char
char c = P [Match c (pure c)]

send :: p a -> P p a
send x = P [Free x (pure id)]

data SomeNT f = forall a. SomeNT (f a)
instance G f => Eq (SomeNT f) where
  SomeNT x == SomeNT y = case cmp x y of Equal{} -> True; _ -> False
instance G f => Ord (SomeNT f) where
  compare (SomeNT x) (SomeNT y) = case cmp x y of LessThan -> LT; Equal{} -> EQ; GreaterThan -> GT

parse :: forall f a. (forall x. Show (f x), G f) => (forall x. f x -> P f x) -> f a -> String -> [(a, String)]
parse g p0 xs0 = go mempty xs0 (g p0) where
  go :: Set (SomeNT f) -> String -> P f b -> [(b, String)]
--  go _ xs p | traceShow ("parse.go", xs, scry 0 p) False = undefined
  go s xs (P ps) = go' s xs =<< ps
  go' :: Set (SomeNT f) -> String -> P' f b -> [(b, String)]
--   go' _ xs p | traceShow ("parse.go'", xs, scry' 0 p) False = undefined
  go' _ xs (Pure x) = [(x, xs)]
  go' _ (x:xs) (Match c k) | c == x = go mempty xs k
  go' _ _ Match{} = []
  go' s xs (Free x k) | SomeNT x `Set.notMember` s =
    let
      (_, l) = analysed x
      extended = (g x <**> chain (asum l)) <**> k
    in
--      traceShow ("parse.go' Free", scry 5 extended) $ 
        go (Set.insert (SomeNT x) s) xs extended
  go' _ _ Free{} = []

  analysed :: f b -> ([b], [P f (b -> b)])
  analysed = analyse g

  chain p = res where res = pure id <|> (flip (.)) <$> p <*> res

data DOrdering a b = LessThan | Equal (a :~: b) | GreaterThan

class (forall x. Ord (f x)) => G f where
  cmp :: f a -> f b -> DOrdering a b

analyse :: forall f a. (forall x. Show (f x), G f) => (forall x. f x -> P f x) -> f a -> ([a], [P f (a -> a)])
analyse g x0 = go mempty (g x0) where
  go :: Set (SomeNT f) -> P f b -> ([b], [P f (a -> b)])
--  go _ p | traceShow ("analyse.go", scry 0 p) False = undefined
  go s (P ps) = foldMap (go' s) ps

  go' :: Set (SomeNT f) -> P' f b -> ([b], [P f (a -> b)])
--  go' _ p | traceShow ("analyse.go'", scry' 0 p) False = undefined
  go' _ (Pure x) = ([x], [])
  go' s (Free x k)
    | Equal Refl <- cmp x x0 = ([], [k])
    | SomeNT x `Set.notMember` s = go (Set.insert (SomeNT x) s) (g x <**> k)
    | otherwise = ([], [])
  go' _ Match{} = ([], [])

scry :: Int -> P f a -> P f a
scry n0 (P xs) = P (map (scry' n0) xs) where

scry' :: Int -> P' f a -> P' f a
scry' _ (Pure x) = Pure x
scry' 0 (Match c _) = Match c empty
scry' n (Match c k) = Match c (scry (n - 1) k)
scry' 0 (Free x _) = Free x empty
scry' n (Free x k) = Free x (scry (n - 1) k)

data Gram a where
  Digit :: Gram Int
  Number :: Gram Int
deriving instance Eq (Gram a)
deriving instance Ord (Gram a)
deriving instance Show (Gram a)

instance G Gram where
  cmp Digit Digit = Equal Refl
  cmp Digit Number = LessThan
  cmp Number Number = Equal Refl
  cmp Number Digit = GreaterThan

gram :: Gram a -> P Gram a
gram Digit = asum [n <$ char (intToDigit n) | n <- [0..9]]
gram Number = send Digit <|> (\hd d -> hd * 10 + d) <$> send Number <*> send Digit

-- >>> parse gram Number "314"

data E a where
  E :: Int -> Int -> E Expr
deriving instance Eq (E a)
deriving instance Ord (E a)
deriving instance Show (E a)

instance G E where
  cmp (E a b) (E c d)
    | a < c || a == c && b < d = LessThan
    | a == c && b == d = Equal Refl
    | otherwise = GreaterThan

data Expr = Neg Expr | Mul Expr Expr | Add Expr Expr | ITE Expr Expr Expr | A
  deriving Show

string :: String -> P p String
string (x:xs) = (:) <$> char x <*> string xs
string [] = pure ""

gramE :: E a -> P E a
gramE (E l r) =
      Neg <$ guard (4 >= l) <* char '-' <*> send (E l 4)
  <|> Mul <$ guard (3 >= r && 3 >= l) <*> send (E 3 3) <* char '*' <*> send (E l 4)
  <|> Add <$ guard (2 >= r && 2 >= l) <*> send (E 2 2) <* char '+' <*> send (E l 3)
  <|> ITE <$ guard (1 >= l) <* string "if " <*> send (E 0 0) <* string " then " <*> send (E 0 0) <* string " else " <*> send (E 0 0)
  <|> A <$ char 'a'

-- >>> parse gramE (E 0 0) "if a+a then -a else a*a+a"
-- [(ITE (Add A A) (Neg A) (Mul A A),"+a"),(ITE (Add A A) (Neg A) (Add (Mul A A) A),""),(ITE (Add A A) (Neg A) A,"*a+a")]

main :: IO ()
main = print $ parse gramE (E 0 0) "if a+a then -a else a*a+a"

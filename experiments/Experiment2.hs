{-# LANGUAGE GADTs #-}

import Control.Applicative
import Data.Char
import Data.Type.Equality
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Some
import Data.GADT.Compare

newtype P p a = P [P' p a] deriving Functor

instance Applicative (P p) where
  pure x = P [Pure x]
  -- Note that the standard 'P ps <*> P qs = P [p <*> q | p <- ps, q <- qs]'
  -- would **not** work because this would combine all the alternatives of
  -- the second parser with the first parser. 
  -- Essentially, that would mean we would have to choose an alternative
  -- from the first parser **and** the second parser up front.
  -- Instead, it is possible and better to postpone choosing the alternatives 
  -- of the second parser.
  -- In particular, the 'chain' combinator we use below depends on this
  -- postponement.
  P ps <*> q = asum (map (`go` q) ps) where
    go (Pure f) k' = fmap f k'
    go (Match c k) k' = P [Match c (k <*> k')]
    go (Free x k) k' = P [Free x (flip <$> k <*> k')]

instance Alternative (P p) where
  empty = P empty
  P ps <|> P qs = P (ps <|> qs)

data P' p a = Pure a | Match Char (P p a) | forall b. Free (p b) (P p (b -> a))
deriving instance Functor (P' p)

char :: Char -> P p Char
char c = P [Match c (pure c)]

send :: p a -> P p a
send x = P [Free x (pure id)]

parse :: forall f a. (GCompare f) => (forall x. f x -> P f x) -> f a -> String -> [a]
parse g p0 xs0 = map fst $ filter ((== "") . snd) $ go mempty xs0 (g p0) where

  -- We use the set 's :: Set (SomeNT f)' to avoid recursing into the same
  -- nonterminal indefinitely, which would otherwise happen if the grammar
  -- was left-recursive.  Of course that means we could miss those parses which
  -- would require taking those loops. 

  -- To account for those, we essentially transform following this general example:
  -- X ::= X Y | Z
  -- ==>
  -- X ::= Z Y*
  -- (where * means repeating zero or more times)
  
  -- More concretely, we analyse the grammar, simulating a single
  -- left-recursive loop and record how parsing would continue after exiting
  -- the loop at that point. Using the 'chain' combinator, we take this
  -- continuation and run it zero or more times, thus simulating an arbitrary
  -- number of left-recursive loops. We recover the missed parses by appending
  -- this chained continuation to the body of each nonterminal we parse.

  go :: Set (Some f) -> String -> P f b -> [(b, String)]
  go s xs (P ps) = go' s xs =<< ps

  go' :: Set (Some f) -> String -> P' f b -> [(b, String)]
  go' _ xs (Pure x) = [(x, xs)]
  go' _ (x:xs) (Match c k) | c == x = go mempty xs k
  go' s xs (Free x k) | Some x `Set.notMember` s =
    go (Set.insert (Some x) s) xs ((g x <**> chain (asum (loops g x))) <**> k)
  go' _ _ _ = []

  chain p = res where res = pure id <|> (flip (.)) <$> p <*> res
  -- TODO: what if 'p' accepts the empty string?

-- | Find left-recursive loops in the grammar definition
-- For each such loop, return the parser fragment that we would enter after
-- running one loop iteration and exiting the loop.
loops :: forall f a. (GCompare f) => (forall x. f x -> P f x) -> f a -> [P f (a -> a)]
loops g x0 = go mempty (g x0) where
  go :: Set (Some f) -> P f b -> [P f (a -> b)]
  go s (P ps) = foldMap (go' s) ps

  go' :: Set (Some f) -> P' f b -> [P f (a -> b)]
  go' s (Free x k)
    | GEQ <- gcompare x x0 = [k]
    | Some x `Set.notMember` s = go (Set.insert (Some x) s) (g x <**> k)
    -- TODO: what if 'x' accepts the empty string?
  go' _ _ = []

data Gram a where
  Digit :: Gram Int
  Number :: Gram Int
deriving instance Show (Gram a)

instance GEq Gram where
  geq Digit Digit = Just Refl
  geq Number Number = Just Refl
  geq _ _ = Nothing

instance GCompare Gram where
  gcompare Digit Digit = GEQ
  gcompare Digit Number = GLT
  gcompare Number Number = GEQ
  gcompare Number Digit = GGT

-- >>> parse gram Number "314"
-- [314]

gram :: Gram a -> P Gram a
gram Digit = asum [n <$ char (intToDigit n) | n <- [0..9]]
gram Number = send Digit <|> (\hd d -> hd * 10 + d) <$> send Number <*> send Digit

data E a where
  E :: Int -> Int -> E Expr
deriving instance Show (E a)

instance GEq E where
  geq (E a b) (E c d)
    | a == c && b == d = Just Refl
    | otherwise = Nothing

instance GCompare E where
  gcompare (E a b) (E c d)
    | a < c || a == c && b < d = GLT
    | a == c && b == d = GEQ
    | otherwise = GGT

data Expr = Neg Expr | Expr :*: Expr | Expr :+: Expr | ITE Expr Expr Expr | A
  deriving Show

string :: String -> P p String
string (x:xs) = (:) <$> char x <*> string xs
string [] = pure ""

gramE :: E a -> P E a
gramE (E l r) =
      Neg   <$ guard (4 >= l)           <*  char '-' <*> send (E l 4)
  <|> (:*:) <$ guard (3 >= r && 3 >= l) <*> send (E 3 3) <* char '*' <*> send (E l 4)
  <|> (:+:) <$ guard (2 >= r && 2 >= l) <*> send (E 2 2) <* char '+' <*> send (E l 3)
  <|> ITE   <$ guard (1 >= l)           <*  string "if " <*> send (E 0 0) <* string " then " <*> send (E 0 0) <* string " else " <*> send (E 0 0)
  <|> A     <$                              char 'a'

-- >>> parse gramE (E 0 0) "if a+a then -a else a+a*-a+a"
-- [ITE (A :+: A) (Neg A) ((A :+: (A :*: Neg A)) :+: A)]

main :: IO ()
main = print $ parse gramE (E 0 0) "if a+a then -a else a+a*-a+a"

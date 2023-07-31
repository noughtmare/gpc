{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

{-
To deal with *left recursion*, we essentially transform the grammar
following this general example:

    X ::= X Y | Z    ==>    X ::= Z Y*    (1)

Where Y* means repeating Y zero or more times. And note that any
left-recursive nonterminal can be written in this form (if we allow an
in-line disjuction operator or add more nonterminals), e.g.:

    X ::= X + X | X - X | 0 | 1
==>
    X ::= X (+ X | - X) | (0 | 1)         (2)
==> 
    X ::= (0 | 1) (+ X | - X)*

There are two main edge-cases: indirect left-recursion and empty
productions. 

We deal with *indirect left-recursion* using a combination of a static
analysis, before parsing, and dynamic checks, during parsing. 

* Statically, we recursively look through all nonterminals which are in
  leftmost position to search for possible left-recursion. For each
  left-recursive loop we find, we collect the continuation, e.g. Y in (1)
  or + X and - X in (2).

  This is done in the 'loops' function.

* Dynamically, we prevent entering the same nonterminal twice by keeping
  track of the visited nonterminals in a set. We clear the set whenever
  the parser consumes an actual character.

  This is done in the 'parse' function.

As for *empty productions*, we don't deal with those yet. For now it is
not that bad to avoid it manually. However, we do plan on resolving it
before a 1.0 release. There seem to be two promising approaches:

* Statically transform the grammar to factor out nonterminals which accept
  the empty string. This could cause nonterminals to expand quadratically
  if done naively, e.g.:

      X  ::= X1  X2  X3  X4
      X' ::= X1' X2  X3  X4
          |  X1  X2' X3  X4
          |  X1  X2  X3' X4
          |  X1  X2  X3  X4'

  Where the primes indicate the non-empty variant of each nonterminal.
   
  It's also be possible to limit the blowup to be be linear if we add
  more helper nonterminals, e.g.:
     
      X2345 ::= X2 X345
      X345  ::= X3 X45
      X45   ::= X4 X5

      X'     ::= X1' X2345
              |  X1  X2345'
      X2345' ::= X2' X345
              |  X2  X345'
      X345'  ::= X3' X45
              |  X3  X45'
      X45'   ::= X4' X5
              |  X4  X5'

* Dynamically enforce that input is consumed and bail out otherwise.
-}

module Experiment2 where

import Control.Applicative
import Data.Char
import Data.Type.Equality
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Some
import Data.GADT.Compare
import Data.String
import Data.Kind

newtype P f a = P [P' f a] deriving Functor

instance Applicative (P f) where
  pure x = P [Pure x]
  -- Note that the standard 'P ps <*> P qs = P [p <*> q | p <- ps, q <- qs]'
  -- would **not** work because this would combine all the alternatives of the
  -- second parser with the first parser. Essentially, that would mean we would
  -- have to choose an alternative from the first parser **and** the second
  -- parser up front. Instead, it is possible and better to postpone choosing
  -- the alternatives of the second parser. In particular, the 'chain'
  -- combinator which we use further down depends on this postponement.
  P ps <*> q = asum (map (`go` q) ps) where
    go (Pure f) k' = fmap f k'
    go (Match c k) k' = P [Match c (k <*> k')]
    go (Free x k) k' = P [Free x (flip <$> k <*> k')]

instance Alternative (P p) where
  empty = P empty
  P ps <|> P qs = P (ps <|> qs)

data P' f a = Pure a | Match Char (P f a) | forall b. Free (f (P f) b) (P f (b -> a))
deriving instance Functor (P' p)

char :: Char -> P p Char
char c = P [Match c (pure c)]

send :: f (P f) a -> P f a
send x = P [Free x (pure id)]

parse :: forall f a. (GCompare (f (P f))) => (forall x. f (P f) x -> P f x) -> f (P f) a -> String -> [a]
parse g p0 xs0 = map fst $ filter ((== "") . snd) $ go mempty xs0 (g p0) where

  -- We use the set 's :: Set (Some f)' to avoid recursing into the same
  -- nonterminal indefinitely.
  go :: Set (Some (f (P f))) -> String -> P f b -> [(b, String)]
  go s xs (P ps) = go' s xs =<< ps

  go' :: Set (Some (f (P f))) -> String -> P' f b -> [(b, String)]
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
loops :: forall f a. (GCompare (f (P f))) => (forall x. f (P f) x -> P f x) -> f (P f) a -> [P f (a -> a)]
loops g x0 = go mempty (g x0) where
  go :: Set (Some (f (P f))) -> P f b -> [P f (a -> b)]
  go s (P ps) = foldMap (go' s) ps

  go' :: Set (Some (f (P f))) -> P' f b -> [P f (a -> b)]
  go' s (Free x k)
    | GEQ <- gcompare x x0 = [k]
    | Some x `Set.notMember` s = go (Set.insert (Some x) s) (g x <**> k)
    -- TODO: what if 'x' accepts the empty string?
  go' _ _ = []

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

data Gram f a where
  Digit :: Gram f Int
  Number :: Gram f Int
deriving instance Show (Gram f a)

instance GEq (Gram f) where
  geq Digit Digit = Just Refl
  geq Number Number = Just Refl
  geq _ _ = Nothing

instance GCompare (Gram f) where
  gcompare Digit Digit = GEQ
  gcompare Digit Number = GLT
  gcompare Number Number = GEQ
  gcompare Number Digit = GGT

-- >>> parse gram Number "314"
-- [314]

gram :: Gram (P Gram) a -> P Gram a
gram Digit = asum [n <$ char (intToDigit n) | n <- [0..9]]
gram Number = send Digit <|> (\hd d -> hd * 10 + d) <$> send Number <*> send Digit

data E f a where
  E :: Int -> Int -> E f Expr
deriving instance Show (E f a)

instance GEq (E f) where
  geq (E a b) (E c d)
    | a == c && b == d = Just Refl
    | otherwise = Nothing

instance GCompare (E f) where
  gcompare (E a b) (E c d)
    | a < c || a == c && b < d = GLT
    | a == c && b == d = GEQ
    | otherwise = GGT

data Expr = Neg Expr | Expr :*: Expr | Expr :+: Expr | ITE Expr Expr Expr | A
  deriving Show

string :: String -> P p String
string (x:xs) = (:) <$> char x <*> string xs
string [] = pure ""

gramE :: E (P E) a -> P E a
gramE (E l r) =
      Neg   <$ guard (4 >= l)           <*  char '-' <*> send (E l 4)
  <|> (:*:) <$ guard (3 >= r && 3 >= l) <*> send (E 3 3) <* char '*' <*> send (E l 4)
  <|> (:+:) <$ guard (2 >= r && 2 >= l) <*> send (E 2 2) <* char '+' <*> send (E l 3)
  <|> ITE   <$ guard (1 >= l)           <*  string "if " <*> send (E 0 0) <* string " then " <*> send (E 0 0) <* string " else " <*> send (E 0 0)
  <|> A     <$                              char 'a'

-- >>> parse gramE (E 0 0) "if a+a then -a else a+a*-a+a"
-- [ITE (A :+: A) (Neg A) ((A :+: (A :*: Neg A)) :+: A)]

-- Desugar:
--
-- E ::= E '*' E   left
--    >  E '+' E   left
--    |  '(' E ')'
--    |  a
--
-- To:
--
-- E(p) ::= [2 >= p] E(2) * E(3)
--       |  [1 >= p] E(0) * E(2)
--       |  '(' E(0) ')'
--       |  a

type E2 :: (Type -> Type) -> Type -> Type
data E2 f a where
  E2 :: E2 f Expr

type X :: ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Type
data X g f a where
  LeftAssoc :: f a -> X g f a
  (:>>) :: f a -> f a -> X g f a
  X :: g f a -> X g f a

infixl 2 |>>

(|>>) :: P (X E2) a -> P (X E2) a -> P (X E2) a
(|>>) x y = send (x :>> y)

left :: P (X E2) a -> P (X E2) a
left x = send (LeftAssoc x)

instance (a ~ String) => IsString (P f a) where
  fromString = string

gramE2 :: E2 (P (X E2)) Expr -> P (X E2) Expr
gramE2 E2 = let e = send (X E2) in
      left ((:*:) <$> e <* "*" <*> e)
  |>> left ((:+:) <$> e <* "+" <*> e)
  <|> "(" *> e <* ")"
  <|> A <$ "a"

type Y :: ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Type
data Y g f a

-- TODO: Does this need some sort of Distributive?
-- desugar :: (forall x. f (P (X f)) x -> P (X f) x) -> Y f (P (Y f)) a -> P (Y f) a
-- desugar = _

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}

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
not that bad to limit ourselves to non-empty productions  manually. However, we
do plan on resolving it before a 1.0 release. There seem to be two promising
approaches:

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
import Data.Functor.Identity
import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as Map
import Unsafe.Coerce (unsafeCoerce)
import Data.Void
import Data.Functor.Compose
import Control.Monad.Writer

newtype P t f a = P { alts :: t (P' f a) }
  deriving (Functor, Applicative, Alternative) via Compose t (P' f)

traverseAlts :: (Traversable t, Applicative m) => (P' f a -> m (P' f' b)) -> P t f a -> m (P t f' b)
traverseAlts f (P as) = P <$> traverse f as

data P' f a = Pure a | Match Char (P' f a) | forall b. Free (f b) (P' f (b -> a))
deriving instance Functor (P' p)

instance Applicative (P' f) where
  pure = Pure
  Pure f <*> k' = fmap f k'
  Match c k <*> k' = Match c (k <*> k')
  Free x k <*> k' = Free x (flip <$> k <*> k')

char :: Applicative t => Char -> P t p Char
char c = P (pure (Match c (pure c)))

send :: Applicative t => f a -> P t f a
send x = P (pure (Free x (pure id)))

parse :: forall f a. (GCompare f) => G [] f -> f a -> String -> [a]
parse (G g) p0 xs0 = map fst $ filter ((== "") . snd) $ go p0 mempty xs0 (g p0) where

  -- We use the set 's :: Set (Some f)' to avoid recursing into the same
  -- nonterminal indefinitely.
  go :: f b -> Set (Some f) -> String -> P [] f b -> [(b, String)]
  go nt s xs (P ps) = go' nt s xs =<< ps

  go' :: f b -> Set (Some f) -> String -> P' f b -> [(b, String)]
  go' nt s xs (Pure x) = (x, xs) : (go' nt s xs . fmap ($ x) =<< loops g nt)
  -- TODO: what if 'nt' accepts the empty string?
  go' nt _ (x:xs) (Match c k) | c == x = go' nt mempty xs k
  go' nt s xs (Free x k) | Some x `Set.notMember` s = do
    (x', xs') <- go x (Set.insert (Some x) s) xs (g x)
    go' nt s xs' (($ x') <$> k)
  go' _ _ _ _ = []

-- | Find left-recursive loops in the grammar definition
-- For each such loop, return the parser fragment that we would enter after
-- running one loop iteration and exiting the loop.
loops :: forall f a. (GCompare f) => (forall x. f x -> P [] f x) -> f a -> [P' f (a -> a)]
loops g x0 = go mempty (g x0) where
  go :: Set (Some f) -> P [] f b -> [P' f (a -> b)]
  go s (P ps) = foldMap (go' s) ps

  go' :: Set (Some f) -> P' f b -> [P' f (a -> b)]
  go' s (Free x k)
    | GEQ <- gcompare x x0 = [k]
    | Some x `Set.notMember` s = go (Set.insert (Some x) s) (g x <**> P [k])
    -- TODO: what if 'x' accepts the empty string?
  go' _ _ = []

newtype G t f = G (forall x. f x -> P t f x)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

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

gram :: Gram a -> P [] Gram a
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

string :: Applicative t => String -> P t p String
string (x:xs) = (:) <$> char x <*> string xs
string [] = pure ""

gramE :: (Alternative t, Applicative t) => G t E
gramE = G $ \(E l r) ->
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

type E2 :: Type -> Type
data E2 a where
  E2 :: E2 Expr
instance GEq E2 where
  geq E2 E2 = Just Refl
instance GCompare E2 where
  gcompare E2 E2 = GEQ

data Assoc = BothAssoc | LeftAssoc | RightAssoc | NoneAssoc

-- Assoc forms a lattice like this:
--
--      None
--      /   \
--   Left   Right
--      \   /
--      Both

instance Semigroup Assoc where
  BothAssoc <> x = x
  x <> BothAssoc = x
  LeftAssoc <> LeftAssoc = LeftAssoc
  RightAssoc <> RightAssoc = RightAssoc
  _ <> _ = NoneAssoc
instance Monoid Assoc where
  mempty = BothAssoc
newtype X a = X [[(a, Assoc)]]
  deriving (Functor, Applicative) via Compose [] (Compose [] (Writer Assoc))
instance Alternative X where
  empty = X [[]]
  X xs0 <|> X ys0 = X (go xs0 ys0) where
    -- appends the last element of xs with the first element of ys
    go [] ys = ys
    go xs [] = xs
    go [x] (y:ys) = (x ++ y) : ys
    go (x:xs) ys = x : go xs ys

infixl 2 >|>

(>|>) :: P X f a -> P X f a -> P X f a
(>|>) (P (X xs)) (P (X ys)) = P (X (xs ++ ys))

left :: P X f a -> P X f a
left (P (X xs)) = P (X (getCompose (fmap (\(x,_) -> (x, LeftAssoc)) (Compose xs))))

-- (<*<) :: P X E2 (a -> b) -> P X E2 a -> P X E2 b
-- x <*< y = send (x :<*< y)

instance (Applicative t, a ~ String) => IsString (P t f a) where
  fromString = string

gramE2 :: G X E2
gramE2 = G $ \E2 -> let e = send E2 in
      left ((:*:) <$> e <* "*" <*> e)
  >|> left ((:+:) <$> e <* "+" <*> e)
  <|> "(" *> e <* ")"
  <|> A <$ "a"

-- -- The desugaring to data dependent grammars should proceed like this:
-- --
-- -- E = ... X >|> Y ...
-- -- ==>
-- -- (E b) = ... (guard b *> X False) <|> Y True ...
-- --
-- -- E = ... X <*< Y ...
-- -- ==>
-- -- (E b)  = ... (guard b *> X True) <*> Y False ...
-- --
-- -- (If the same expression has multiple occurrences of >|> and <*<,
-- -- then the booleans could be combined into an int as an optmization.)
-- --
-- -- The major remaining problem is that each occurrence of such a special
-- -- disambiguation operator requires its own boolean. That's hard to do
-- -- in a type-safe way. I could perhaps do something like Map Key Bool,
-- -- but how can I identify these operators? Would I have to use observable
-- -- sharing techniques again?
-- --
-- -- One option may be to identify these operators by the location in the
-- -- free applicative at which they occur.
--
-- -- I want to try creating a new nonterminal for each occurrence of these
-- -- operators. Then each can be individually guarded. Each occurrence can be
-- -- identified by its ordinal.
--
-- type Y :: (Type -> Type) -> (Type -> Type) -> Type -> Type
-- data Y f m a where
--   Y :: f a -> Y f m a
--   Y' :: Int -> Bool -> Y f m a
-- instance GEq f => GEq (Y f m) where
--   geq (Y x) (Y y) = geq x y
--   geq (Y' i0 b0) (Y' i1 b1) = if i0 == i1 && b0 == b1 then Just (unsafeCoerce Refl) else Nothing
--   geq _ _ = Nothing
-- instance GCompare f => GCompare (Y f m) where
--   gcompare (Y x) (Y y) = gcompare x y
--   gcompare (Y' i0 b0) (Y' i1 b1) =
--     case compare i0 i1 <> compare b0 b1 of
--       LT -> GLT
--       EQ -> unsafeCoerce GEQ
--       GT -> GGT
--   gcompare Y{} Y'{} = GLT
--   gcompare Y'{} Y{} = GGT
--
--
--
-- bla :: P' (X f) a -> State (Int, Map Int (Some (P (Y f)))) (P' (Y f) a)
-- bla (Pure x) = pure (Pure x)
-- bla (Match c k) = Match c <$> traverseAlts bla k
-- bla (Free (X op) k) = Free (Y op) <$> traverseAlts bla k
-- bla (Free (x :<*< y) k) = do
--   x' <- traverseAlts bla x
--   y' <- traverseAlts bla y
--   (i, m) <- get
--   put (i + 1, Map.insert i (Some (x' <*> y')) m)
--   Free (Y' i True) <$> traverseAlts bla k
-- bla (Free (x :>|> y) k) = do
--   x' <- traverseAlts bla x
--   y' <- traverseAlts bla y
--   (i, m) <- get
--   put (i + 1, Map.insert i (Some (x' <|> y')) m)
--   Free (Y' i True) <$> traverseAlts bla k
--
-- class Funny f where
--   fun :: Applicative m => (forall x. P t f x -> m (P t f' x)) -> G t f -> m (G t f)
--
-- instance Funny E2 where
--   fun f (G g) = (\x -> G $ \E2 -> x) <$> f (g E2)
--
-- fun' :: (Funny f, Applicative m) => (forall x. P' t f x -> m (P' t f' x)) -> G t f -> m (G f')
-- fun' f g = fun (traverseAlts f) g
--
-- desugar :: Funny f => G f (X f) -> G (Y f m) (Y f)
-- desugar g = let (G g', (_, m)) = runState (fun' bla g) (0, Map.empty) in G $ \case
--   Y x -> g' x
--   Y' i b -> guard b *> case m Map.! i of Some x -> unsafeCoerce x
--
-- example :: [Expr]
-- example = parse (desugar gramE2) (Y E2) "1+2*3"
--
-- -- >>> example
-- -- []
--

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Gigaparsec.Core where

import Control.Monad.State
import Data.Foldable (traverse_)
import Control.Applicative
import Data.Type.Equality
import Data.Bifunctor (first)
import Unsafe.Coerce
import qualified Debug.Trace
import Data.Char
import Language.Haskell.TH (Name)

traceShow _ = id

type Id a = Name
newtype Parser a = Parser { alts :: [P a] }
data P a = T Char (Parser a) | forall b. NT (Id b) (Parser b) (b -> Parser a) | Success a

instance Functor P where
  fmap f (T c p) = T c (fmap f p)
  fmap f (NT n p q) = NT n p (fmap f . q)
  fmap f (Success x) = Success (f x)

char :: Char -> Parser ()
char c = Parser [T c (pure ())]

pattern (::=) :: Name -> Parser a -> Parser a
pattern name ::= p <- (error "'::=' cannot be used in a pattern." -> (name, p)) where
  (::=) = \name p -> Parser [NT name p (\x -> Parser [Success x])]
infix 1 ::= -- tighter than $ but looser than <|>

instance Functor Parser where
  fmap f (Parser xs) = Parser (map (fmap f) xs)

instance Applicative Parser where
  pure x = Parser [Success x]
  Parser ps <*> q0 = asum $ fmap (`seqP` q0) ps where
    seqP (T c p) q = Parser [T c (p <*> q)]
    seqP (NT n p p') q = Parser [NT n p (\x -> p' x <*> q)]
    seqP (Success f) q = f <$> q

instance Alternative Parser where
  empty = Parser []
  Parser ps <|> Parser qs = Parser (ps <> qs)

instance Monad Parser where
    Parser xs >>= k0 = Parser (xs >>= go (alts . k0)) where
        go :: (a -> [P b]) -> P a -> [P b]
        go k (Success x) = k x
        go k (T c p) = [T c (Parser (concatMap (go k) (alts p)))]
        go k (NT n p q) = [NT n p (Parser . concatMap (go k) . alts . q)]


data SelfCont a = forall b. SelfCont (Stack b a) (a -> Parser b)

data Stack a b where
  SNil :: Stack a a
  SCons :: Id a -> Int -> [SelfCont a] -> (a -> Parser b) -> Stack b c -> Stack a c

eqId :: Id a -> Id b -> Maybe (a :~: b)
eqId x y
  | x == y = Just (unsafeCoerce Refl)
  | otherwise = Nothing

unwind :: forall a b c. Id b -> Int -> Stack a c -> Maybe (Stack a b, Stack b c)
unwind _ _ SNil = Nothing
unwind n i (SCons n' i' dcs k s) =
  case eqId @a @b n n' of
    Just Refl | i == i' -> Just (SNil, SCons n' i' dcs k s)
    _ -> first (SCons n' i' dcs k) <$> unwind n i s

appendStack :: Stack a b -> Stack b c -> Stack a c
appendStack SNil x = x
appendStack (SCons n i ks k stack') stack'' = SCons n i ks k (appendStack stack' stack'')

update :: ([SelfCont a] -> [SelfCont a]) -> Stack a b -> Stack a b
update f (SCons n i q q' s) = SCons n i (f q) q' s
update _ SNil = error "Cannot update SNil"

parse :: forall a. Parser a -> String -> [a]
parse p0 xs0 = evalState (parse' 0 xs0 p0) SNil where
  parse' :: Int -> String -> Parser b -> State (Stack b c) [c]
  parse' i xs = fmap concat . traverse (go i xs) . alts

  go :: forall b c. Int -> String -> P b -> State (Stack b c) [c]
  go i (:){} (T c _) | traceShow ("t/match", c, i) False = undefined
  go i (x:xs) (T c p) | x == c = parse' (i + 1) xs p
  go i [] (T c _) | traceShow ("t/fail", c, i) False = undefined
  go _ _ T{} = pure []

  go i xs (NT n p p') = state $ \s -> 
    -- Find out if the current (n, i) combination is already on the stack
    case unwind n i s of
      -- If not, push a new empty continuation on the initial stack (stack0) and continue running
      Nothing | traceShow ("nt/nothing", n, i) False -> undefined
      Nothing -> let (x, s') = runState (parse' i xs p) (SCons n i [] p' s) in (x, maybe undefined snd (unwind n i s'))
      -- If so, add the p' as a new continuation, fail the current branch, and do update the stack
      Just{} | traceShow ("nt/just", n, i) False -> undefined
      Just (stack0, stack1) -> 
        ([], appendStack stack0 (update (SelfCont stack0 p' :) stack1))

  go i xs (Success x) = state $ \stack ->
    case stack of
      -- If there's something on the stack we can either:
      -- use it to continue parsing, or ignore it and pop it from the stack
      SCons{} | traceShow ("success/scons", i) False -> undefined
      SCons _ _ ks p' stack' -> 
        ( evalState (parse' i xs (p' x)) stack'
          ++ concat [evalState (parse' i xs (p x)) (appendStack s stack) | SelfCont s p <- ks]
        , stack)
      -- If there's nothing on the stack then we succeed iff there is also no remaining input
      SNil | traceShow ("success/snil", i) False -> undefined
      SNil -> ([x | null xs], stack)
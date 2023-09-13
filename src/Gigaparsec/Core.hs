{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}

module Gigaparsec.Core (CFG (CFG), RHS, Result, t, nt, parse, emptyk') where

import Data.Map.Strict (Map)
-- import Data.Set (Set)
import Control.Applicative
import Control.Monad
import Data.Map.Strict qualified as Map
-- import GHC.Base (Any)
import Debug.Trace
import Data.Text qualified as Text
import Data.Text (Text)

import Data.Some
import Data.GADT.Compare

import Data.Functor.Identity
import Data.Bifunctor
import Unsafe.Coerce (unsafeCoerce)
import Data.GADT.Show
import Data.Type.Equality

data RHS f a = Pure a | T Char (RHS f a) | forall x. NT (f x) (x -> RHS f a) | Or (RHS f a) (RHS f a) | Fail
deriving instance Functor (RHS f)

instance Applicative (RHS f) where
  pure = Pure
  (<*>) = ap

instance Alternative (RHS f) where
  (<|>) = Or
  empty = Fail

instance Monad (RHS f) where
  Pure x >>= k = k x
  T c k >>= k' = T c (k >>= k')
  NT f k >>= k' = NT f (k >=> k')
  Or p q >>= k = Or (p >>= k) (q >>= k)
  Fail >>= _ = Fail

data CFG f a = CFG (f a) (forall x. f x -> RHS f x)

data T3 a b c = T3 !a !b !c deriving Show

data Comm f = Comm !(Some f) !Int deriving (Eq, Ord, Show)

newtype Cont f a = Cont { getCont :: Text -> Descr -> a -> Command f }
-- instance Show (Cont f a) where
--   show _ = "<Cont>"

data Descr = Descr Slot !Int !Int
data Slot = Slot -- String [Symbol] [Symbol]
  deriving Show

newtype Rel a b = Rel (Map a [b]) deriving Show

rel :: Ord a => Rel a b -> a -> [b]
rel (Rel m) x = Map.findWithDefault [] x m

relMay :: Ord a => Rel a b -> a -> Maybe [b]
relMay (Rel m) x = Map.lookup x m

initRel :: Ord a => a -> Rel a b -> Rel a b
initRel x (Rel m) = Rel (Map.insertWith (++) x [] m)

addRel :: Ord a => a -> b -> Rel a b -> Rel a b
addRel x y (Rel m) = Rel (Map.insertWith (++) x [y] m)

relSize :: Rel a b -> Int
relSize (Rel m) = Map.size m

-- instance GShow Identity where
--   gshowsPrec _ _ = showString "<Identity>"
-- instance GShow (Cont f) where
--   gshowsPrec _ _ = showString "<Cont>"

-- newtype U = U (Set Descr)
newtype G f = G { getG :: Rel (Comm f) (Slot, Int, Some (Cont f)) } -- deriving Show
newtype P f = P { getP :: Rel (Comm f) (Int, Some Identity) } -- deriving Show

newtype Command f = Command { getCommand :: forall x. T3 (G f) (P f) (Result x) -> T3 (G f) (P f) (Result x) }

newtype M f a = M { getM :: Text -> Descr -> Cont f a -> Command f }

extents :: (GCompare f) => f a -> M f (Maybe [(Int, a)])
extents nt = M $ \inp dsc@(Descr _ _ i) (Cont k) ->
  Command $ \(T3 g p b) -> -- trace ("extents " ++ show i) $
  getCommand
    (k inp dsc (
      let res = relMay (getP p) (Comm (Some nt) i)
      in fmap (map (second (\(Some (Identity x)) -> unsafeCoerce x))) res))
    (T3 g (P (initRel (Comm (Some nt) i) (getP p))) b)

addExtent :: GCompare f => f a -> a -> M f ()
addExtent nt x = M $ \inp dsc@(Descr _ l i) (Cont k) ->
  Command $ \(T3 g p b) -> -- trace ("addExtent " ++ show (nt, l, i)) $
  getCommand (k inp dsc ()) (T3 g (P (addRel (Comm (Some nt) l) (i, Some (Identity x)) (getP p))) b)

resume :: GCompare f => f a -> a -> M f a
resume nt x = M $ \inp (Descr Slot l r) _ ->
  Command $ \(T3 g p b) -> -- trace ("resume " ++ show (l, r)) $ 
    -- if l == r then T3 g p b else
    let cnts = rel (getG g) (Comm (Some nt) l) in
    foldr (\(s, l', Some (Cont k)) go -> go . getCommand (unsafeCoerce k inp (Descr s l' r) x))
      id cnts (T3 g p b)

addCont :: GCompare f => f a -> M f c -> M f c
addCont nt m = M $ \inp dsc@(Descr s l i) k ->
  Command $ \(T3 g p b) -> -- trace ("addCont " ++ show (nt, i)) $
    getCommand (getM m inp dsc k) (T3 (G (addRel (Comm (Some nt) i) (s, l, Some k) (getG g))) p b)

match :: Char -> M f ()
match c = M $ \inp (Descr (Slot {- nt alpha beta -}) l i) (Cont k) ->
  case Text.uncons inp of
    Just (x,inp') | c == x -> k inp' (Descr (Slot {- nt alpha beta -}) l (i + 1)) ()
    _ -> Command id

skip :: Int -> M f ()
skip r = M $ \inp (Descr s l i) (Cont k) -> k (Text.drop (r - i) inp) (Descr s l r) ()

descend :: M f ()
descend = M $ \inp (Descr Slot _ i) (Cont k) -> k inp (Descr Slot i i) ()

traceI :: String -> M f ()
traceI msg = M $ \inp dsc@(Descr _ _ i) k -> trace (show i ++ ": " ++ msg) getCont k inp dsc ()

traceCmd :: String -> M f ()
traceCmd msg = M $ \inp dsc@(Descr _ _ i) k -> Command $ \(T3 g p b) -> getCommand (getCont k inp dsc ()) $ trace (show i ++ ": " ++ msg) (T3 g p b)

instance Functor (M f) where
  fmap f (M p) = M $ \inp dsc (Cont k) ->
    p inp dsc $ Cont $ \inp' dsc' x ->
      k inp' dsc' (f x)
instance Applicative (M f) where
  pure x = M $ \inp dsc (Cont k) -> k inp dsc x
  (<*>) = ap
instance Alternative (M f) where
  empty = M $ \_ _ _ -> Command id
  M p <|> M q = M $ \inp dsc k -> Command (getCommand (q inp dsc k) . getCommand (p inp dsc k))
instance Monad (M f) where
  M p >>= k = M $ \inp dsc k' ->
    p inp dsc $ Cont $ \inp' dsc' x ->
      getM (k x) inp' dsc' k'

-- must have Alternative instance
type Result = []

showOne :: RHS f x -> String
showOne Pure{} = "Pure"
showOne (T c _) = "(T " ++ show c ++ ")"
showOne (NT _ _) = "NT"
showOne (Or _ _) = "Or"
showOne Fail = "Fail"

parse :: forall f a. GCompare f => CFG f a -> Text -> Result a
parse (CFG nt0 prods) inp0 = res where

  T3 _ _ res =
    getCommand
      (getM (parseRHS (NT nt0 pure)) inp0 (Descr Slot 0 0) finish)
      (T3 (G (Rel mempty)) (P (Rel mempty)) empty)

  finish :: Cont f a
  finish = Cont $ \inp _ x -> Command $ \(T3 p g b) -> 
    -- trace "finish" $
      T3 p g (b <|> unsafeCoerce x <$ guard (Text.null inp))

  parseRHS :: RHS f x -> M f x
  -- parseRHS x | trace ("parseRHS " ++ showOne x) False = undefined
  parseRHS (Pure x) = pure x
  parseRHS (T c k) = parseT c *> parseRHS k
  parseRHS (NT f k) = parseNT f >>= parseRHS . k
  parseRHS (Or p q) = parseRHS p <|> parseRHS q
  parseRHS Fail = empty

  parseNT :: f x -> M f x
  parseNT nt = 
    -- if we ever finish parsing nt then resume after this point
    addCont nt $
      -- check if we have already finished parsing this
      extents nt >>= \case
        -- if not,
        Nothing -> do
          -- traceCmd "Nothing"
          -- descend into nt
          descend
          -- traceCmd "Nothing descend"
          -- parse its right hand side
          x <- parseRHS (prods nt)
          -- traceCmd "Nothing parseRHS"
          -- remember that we've parsed it (and to what point int the input)
          addExtent nt x
          -- traceCmd "Nothing addExtent"
          -- resume parsing the stored continuations
          x' <- resume nt x
          -- traceCmd "Nothing resume"
          pure x'
        -- if so,
        Just rs -> do
          -- traceCmd ("Just " ++ show (length rs))
          -- for all successes, skip forward and continue parsing
          asum (map (\(r, x) -> x <$ skip r) rs)

  parseT :: Char -> M f ()
  parseT = match

t :: Char -> RHS f ()
t c = T c (pure ())

nt :: f a -> RHS f a
nt f = NT f pure

data E a where E :: E ()
deriving instance Eq (E a)
deriving instance Ord (E a)
instance GEq E where geq E E = Just Refl
instance GCompare E where gcompare E E = GEQ

emptyk' :: CFG E ()
emptyk' = CFG E $ \E -> nt E <|> pure ()
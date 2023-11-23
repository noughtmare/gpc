{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Map.Strict (Map)
-- import Data.Set (Set)
import Control.Applicative
import Control.Monad
import Data.Map.Strict qualified as Map
-- import GHC.Base (Any)
-- import Debug.Trace
import Test.Tasty.Bench.Fit
import Data.Text qualified as Text
import Data.Text (Text)
import Data.Some
import Data.Functor.Identity
import Data.GADT.Show
import Data.Bifunctor
import Unsafe.Coerce (unsafeCoerce)
import Data.GADT.Compare
import Data.Type.Equality

-- Blog topic: static type safety breaks modularity

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
instance Show (Cont f a) where
  show _ = "<Cont>"

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

instance GShow Identity where
  gshowsPrec _ _ = showString "<Identity>"
instance GShow (Cont f) where
  gshowsPrec _ _ = showString "<Cont>"

-- newtype U = U (Set Descr)
newtype G f = G { getG :: Rel (Comm f) (Slot, Int, Some (Cont f)) } deriving Show
newtype P f = P { getP :: Rel (Comm f) (Int, Some Identity) } deriving Show

newtype Command f = Command { getCommand :: forall x. T3 (G f) (P f) (Maybe x) -> T3 (G f) (P f) (Maybe x) }

newtype M f a = M { getM :: Text -> Descr -> Cont f a -> Command f }

extents :: GCompare f => f a -> M f (Maybe [(Int, a)])
extents nt = M $ \inp dsc@(Descr _ _ i) (Cont k) ->
  Command $ \(T3 g p b) -> -- trace ("extents " ++ show (nt, i)) $
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
  Command $ \(T3 g p b) ->
    let cnts = rel (getG g) (Comm (Some nt) l) in -- trace ("resume " ++ show (nt, l, cnts)) $
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

-- traceI :: String -> M ()
-- traceI msg = M $ \inp dsc@(Descr _ _ i) k -> trace (show i ++ ": " ++ msg) getCont k inp dsc ()

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

parseCFG :: forall f a. GCompare f => CFG f a -> Text -> T3 (G f) (P f) (Maybe a)
parseCFG (CFG nt0 prods) inp0 =
  getCommand
    (getM (parseRHS (NT nt0 pure)) inp0 (Descr Slot 0 0) final)
    (T3 (G (Rel mempty)) (P (Rel mempty)) Nothing) where

  final :: Cont f a
  final = Cont $ \inp _ x -> Command $ \(T3 p g b) -> (T3 p g (b <|> unsafeCoerce x <$ guard (Text.null inp)))

  parseRHS :: RHS f x -> M f x
  parseRHS (Pure x) = pure x
  parseRHS (T c k) = parseT c *> parseRHS k
  parseRHS (NT f k) = parseNT f >>= parseRHS . k
  parseRHS (Or p q) = parseRHS p <|> parseRHS q
  parseRHS Fail = empty

  parseNT :: f x -> M f x
  parseNT nt = addCont nt $
    extents nt >>= \case
      Nothing -> do
        descend
        x <- parseRHS (prods nt)
        addExtent nt x
        resume nt x
      Just rs -> asum (map (\(r, x) -> x <$ skip r) rs)

  parseT :: Char -> M f ()
  parseT = match

t :: Char -> RHS f ()
t c = T c (pure ())

nt :: f a -> RHS f a
nt f = NT f pure

data E a where E :: E Int

deriving instance Eq (E a)
deriving instance Ord (E a)
instance GEq E where
  geq E E = Just Refl
instance GCompare E where
  gcompare E E = GEQ
deriving instance Show (E a)

example :: CFG E Int
example = CFG E $ \E -> nt E *> t '+' *> nt E <|> 0 <$ t 'a'

-- >>> parseCFG example "a+a+a+a+a+a"
-- (G {getG = Rel (fromList [(Comm "E" 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 2,[(Slot,2,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 4,[(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 6,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 8,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 10,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,10,<Cont>),(Slot,0,<Cont>)])])},P {getP = Rel (fromList [(Comm "E" 0,[11,11,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,9,7,5,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,9,11,11,11,9,7,5,3,1]),(Comm "E" 2,[11,11,11,11,9,11,11,11,9,11,11,9,7,11,11,11,9,11,11,9,7,5,3]),(Comm "E" 4,[11,11,11,9,11,11,9,7,5]),(Comm "E" 6,[11,11,9,7]),(Comm "E" 8,[11,9]),(Comm "E" 10,[11])])},True)

data N a where N :: N Int
deriving instance Eq (N a)
deriving instance Ord (N a)
deriving instance Show (N a)
instance GEq N where
  geq N N = Just Refl
instance GCompare N where
  gcompare N N = GEQ
instance GShow N where
  gshowsPrec _ N = showString "N"

example3 :: CFG N Int
example3 = CFG N $ \N -> (+ 1) <$ t 'a' <*> nt N <|> pure 0

example4 :: CFG N Int
example4 = CFG N $ \N -> (+ 1) <$> nt N <* t 'a' <|> pure 0

-- >>> parseCFG example3 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm (Some N) 0,[(Slot,0,Some <Cont>)]),(Comm (Some N) 1,[(Slot,0,Some <Cont>)]),(Comm (Some N) 2,[(Slot,1,Some <Cont>)]),(Comm (Some N) 3,[(Slot,2,Some <Cont>)]),(Comm (Some N) 4,[(Slot,3,Some <Cont>)])])})
--    (P {getP = Rel (fromList [(Comm (Some N) 0,[(0,Some <Identity>),(1,Some <Identity>),(2,Some <Identity>),(3,Some <Identity>),(4,Some <Identity>)]),(Comm (Some N) 1,[(1,Some <Identity>),(2,Some <Identity>),(3,Some <Identity>),(4,Some <Identity>)]),(Comm (Some N) 2,[(2,Some <Identity>),(3,Some <Identity>),(4,Some <Identity>)]),(Comm (Some N) 3,[(3,Some <Identity>),(4,Some <Identity>)]),(Comm (Some N) 4,[(4,Some <Identity>)])])})
--    (Just 4)

-- >>> parseCFG example4 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm (Some N) 0,[(Slot,0,Some <Cont>),(Slot,0,Some <Cont>)])])})
--    (P {getP = Rel (fromList [(Comm (Some N) 0,[(4,Some <Identity>),(3,Some <Identity>),(2,Some <Identity>),(1,Some <Identity>),(0,Some <Identity>)])])})
--    (Just 4)

main :: IO ()
-- main = print (parseCFG example "a+a+a")

main = do
  result <-
    fits $
      mkFitConfig
        (\n -> (\(T3 _ _ b) -> b) $ parseCFG example4 (Text.replicate (fromIntegral n) (Text.pack "a")))
        (1000, 1000000)
  mapM_ print result

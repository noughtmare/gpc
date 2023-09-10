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

data RHS f a = Pure a | T Char (RHS f a) | NT f (RHS f a) | Or (RHS f a) (RHS f a) | Fail
  deriving (Show, Functor)

instance Applicative (RHS f) where
  pure = Pure
  Pure f <*> k = fmap f k
  T c k <*> k' = T c (k <*> k')
  NT f k <*> k' = NT f (k <*> k')
  Or p q <*> k = Or (p <*> k) (q <*> k)
  Fail <*> _ = Fail

instance Alternative (RHS f) where
  (<|>) = Or
  empty = Fail

data CFG f = CFG f (f -> RHS f ())

data T3 a b c = T3 !a !b !c deriving Show

data Comm f = Comm !f !Int deriving (Eq, Ord, Show)

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

-- newtype U = U (Set Descr)
newtype G f = G { getG :: Rel (Comm f) (Slot, Int, Cont f ()) } deriving Show
newtype P f = P { getP :: Rel (Comm f) Int } deriving Show

newtype Command f = Command { getCommand :: T3 (G f) (P f) Bool -> T3 (G f) (P f) Bool }

newtype M f a = M { getM :: Text -> Descr -> Cont f a -> Command f }

extents :: Ord f => f -> M f (Maybe [Int])
extents nt = M (\inp dsc@(Descr _ _ i) k ->
  Command $ \(T3 g p b) -> -- trace ("extents " ++ show (nt, i)) $
  getCommand (getCont k inp dsc (relMay (getP p) (Comm nt i))) (T3 g (P (initRel (Comm nt i) (getP p))) b))

addExtent :: Ord f => f -> M f ()
addExtent nt = M $ \inp dsc@(Descr _ l i) k ->
  Command $ \(T3 g p b) -> -- trace ("addExtent " ++ show (nt, l, i)) $
  getCommand (getCont k inp dsc ()) (T3 g (P (addRel (Comm nt l) i (getP p))) b)

resume :: Ord f => f -> M f ()
resume nt = M $ \inp (Descr Slot l r) _ ->
  Command $ \(T3 g p b) ->
    let cnts = rel (getG g) (Comm nt l) in -- trace ("resume " ++ show (nt, l, cnts)) $
    foldr (\(s, l', Cont k) go -> go . getCommand (k inp (Descr s l' r) ()))
      id cnts (T3 g p b)

addCont :: Ord f => f -> M f () -> M f ()
addCont nt m = M $ \inp dsc@(Descr s l i) k ->
  Command $ \(T3 g p b) -> -- trace ("addCont " ++ show (nt, i)) $
    getCommand (getM m inp dsc k) (T3 (G (addRel (Comm nt i) (s, l, k) (getG g))) p b)

match :: Char -> M f ()
match c = M $ \inp (Descr (Slot {- nt alpha beta -}) l i) k ->
  case Text.uncons inp of
    Just (x,inp') | c == x -> getCont k inp' (Descr (Slot {- nt alpha beta -}) l (i + 1)) ()
    _ -> Command id

skip :: Int -> M f ()
skip r = M $ \inp (Descr s l i) k -> getCont k (Text.drop (r - i) inp) (Descr s l r) ()

descend :: M f ()
descend = M $ \inp (Descr Slot _ i) k -> getCont k inp (Descr Slot i i) ()

-- traceI :: String -> M ()
-- traceI msg = M $ \inp dsc@(Descr _ _ i) k -> trace (show i ++ ": " ++ msg) getCont k inp dsc ()

instance Functor (M f) where
  fmap f (M p) = M $ \inp dsc k -> p inp dsc (Cont (\inp' dsc' x -> getCont k inp' dsc' (f x)))
instance Applicative (M f) where
  pure x = M $ \inp dsc k -> getCont k inp dsc x
  (<*>) = ap
instance Alternative (M f) where
  empty = M $ \_ _ _ -> Command id
  M p <|> M q = M $ \inp dsc k -> Command (getCommand (q inp dsc k) . getCommand (p inp dsc k))
instance Monad (M f) where
  M p >>= k = M $ \inp dsc k' ->
    p inp dsc $ Cont $ \inp' dsc' x ->
      getM (k x) inp' dsc' k'

parseCFG :: forall f. Ord f => CFG f -> Text -> T3 (G f) (P f) Bool
parseCFG (CFG nt0 prods) inp0 =
  getCommand
    (getM (parseRHS (NT nt0 (pure ()))) inp0 (Descr Slot 0 0) final)
    (T3 (G (Rel mempty)) (P (Rel mempty)) False) where

  final :: Cont f ()
  final = Cont $ \inp _ _ -> Command $ \(T3 p g b) -> (T3 p g (b || Text.null inp))

  parseRHS :: RHS f () -> M f ()
  parseRHS (Pure ()) = pure ()
  parseRHS (T c k) = parseT c *> parseRHS k
  parseRHS (NT f k) = parseNT f *> parseRHS k
  parseRHS (Or p q) = parseRHS p <|> parseRHS q
  parseRHS Fail = empty

  parseNT :: f -> M f ()
  parseNT nt = addCont nt $
    extents nt >>= \case
      Nothing -> do
        descend
        parseRHS (prods nt)
        addExtent nt
        resume nt
      Just rs -> asum (map skip rs)

  parseT :: Char -> M f ()
  parseT = match

t :: Char -> RHS f ()
t c = T c (pure ())

nt :: f -> RHS f ()
nt f = NT f (pure ())

data E = E deriving (Eq, Ord, Show)

example :: CFG E
example = CFG E $ \E -> nt E *> t '+' *> nt E <|> t 'a'

-- >>> parseCFG example "a+a+a+a+a+a"
-- (G {getG = Rel (fromList [(Comm "E" 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 2,[(Slot,2,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 4,[(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 6,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 8,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 10,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,10,<Cont>),(Slot,0,<Cont>)])])},P {getP = Rel (fromList [(Comm "E" 0,[11,11,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,9,7,5,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,9,11,11,11,9,7,5,3,1]),(Comm "E" 2,[11,11,11,11,9,11,11,11,9,11,11,9,7,11,11,11,9,11,11,9,7,5,3]),(Comm "E" 4,[11,11,11,9,11,11,9,7,5]),(Comm "E" 6,[11,11,9,7]),(Comm "E" 8,[11,9]),(Comm "E" 10,[11])])},True)

data N = N deriving (Eq, Ord, Show)

example3 :: CFG N
example3 = CFG N $ \N -> t 'a' *> nt N <|> pure ()

example4 :: CFG N
example4 = CFG N $ \N -> nt N *> t 'a' <|> pure ()

-- >>> parseCFG example3 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm N 0,[(Slot,0,<Cont>)]),(Comm N 1,[(Slot,0,<Cont>)]),(Comm N 2,[(Slot,1,<Cont>)]),(Comm N 3,[(Slot,2,<Cont>)]),(Comm N 4,[(Slot,3,<Cont>)])])})
--    (P {getP = Rel (fromList [(Comm N 0,[0,1,2,3,4]),(Comm N 1,[1,2,3,4]),(Comm N 2,[2,3,4]),(Comm N 3,[3,4]),(Comm N 4,[4])])})
--    True

-- >>> parseCFG example4 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm N 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)])])})
--    (P {getP = Rel (fromList [(Comm N 0,[4,3,2,1,0])])})
--    True

main :: IO ()
-- main = print (parseCFG example "a+a+a")

main = do
  result <-
    fits $
      mkFitConfig
        (\n -> (\(T3 _ _ b) -> b) $ parseCFG example4 (Text.replicate (fromIntegral n) (Text.pack "a")))
        (1000, 1000000)
  mapM_ print result

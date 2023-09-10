{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
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

data CFG = CFG String [(String, [[Symbol]])]

data Symbol = T Char | NT String deriving Show

data T3 a b c = T3 !a !b !c deriving Show

data Comm = Comm !String !Int deriving (Eq, Ord, Show)

newtype Cont a = Cont { getCont :: Text -> Descr -> a -> Command }
instance Show (Cont a) where
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
newtype G = G { getG :: Rel Comm (Slot, Int, Cont ()) } deriving Show
newtype P = P { getP :: Rel Comm Int } deriving Show

newtype Command = Command { getCommand :: T3 G P Bool -> T3 G P Bool }

newtype M a = M { getM :: Text -> Descr -> Cont a -> Command }

extents :: String -> M (Maybe [Int])
extents nt = M (\inp dsc@(Descr _ _ i) k ->
  Command $ \(T3 g p b) -> -- trace ("extents " ++ show (nt, i)) $
  getCommand (getCont k inp dsc (relMay (getP p) (Comm nt i))) (T3 g (P (initRel (Comm nt i) (getP p))) b))

addExtent :: String -> M ()
addExtent nt = M $ \inp dsc@(Descr _ l i) k ->
  Command $ \(T3 g p b) -> -- trace ("addExtent " ++ show (nt, l, i)) $
  getCommand (getCont k inp dsc ()) (T3 g (P (addRel (Comm nt l) i (getP p))) b)

resume :: String -> M ()
resume nt = M $ \inp (Descr Slot l r) _ ->
  Command $ \(T3 g p b) ->
    let cnts = rel (getG g) (Comm nt l) in -- trace ("resume " ++ show (nt, l, cnts)) $
    foldr (\(s, l', Cont k) go -> go . getCommand (k inp (Descr s l' r) ()))
      id cnts (T3 g p b)

addCont :: String -> M () -> M ()
addCont nt m = M $ \inp dsc@(Descr s l i) k ->
  Command $ \(T3 g p b) -> -- trace ("addCont " ++ show (nt, i)) $
    getCommand (getM m inp dsc k) (T3 (G (addRel (Comm nt i) (s, l, k) (getG g))) p b)

match :: Char -> M ()
match c = M $ \inp (Descr (Slot {- nt alpha beta -}) l i) k ->
  case Text.uncons inp of
    Just (x,inp') | c == x -> getCont k inp' (Descr (Slot {- nt alpha beta -}) l (i + 1)) ()
    _ -> {- trace ("match fail: " ++ show c) $ -} Command id

skip :: Int -> M ()
skip r = M $ \inp (Descr s l i) k -> getCont k (Text.drop (r - i) inp) (Descr s l r) ()

descend :: M ()
descend = M $ \inp (Descr Slot _ i) k -> getCont k inp (Descr Slot i i) ()

-- traceI :: String -> M ()
-- traceI msg = M $ \inp dsc@(Descr _ _ i) k -> trace (show i ++ ": " ++ msg) getCont k inp dsc ()

instance Functor M where
  fmap f (M p) = M $ \inp dsc k -> p inp dsc (Cont (\inp' dsc' x -> getCont k inp' dsc' (f x)))
instance Applicative M where
  pure x = M $ \inp dsc k -> getCont k inp dsc x
  (<*>) = ap
instance Alternative M where
  empty = M $ \_ _ _ -> Command id
  M p <|> M q = M $ \inp dsc k -> Command (getCommand (q inp dsc k) . getCommand (p inp dsc k))
instance Monad M where
  M p >>= k = M $ \inp dsc k' ->
    p inp dsc $ Cont $ \inp' dsc' x ->
      getM (k x) inp' dsc' k'

(!) :: Eq k => [(k, v)] -> k -> v
xs ! x = case lookup x xs of Just y -> y

parseCFG :: CFG -> Text -> T3 G P Bool
parseCFG (CFG nt0 prods) inp0 =
  getCommand
    (getM (parseAlts [[NT nt0]]) inp0 (Descr Slot 0 0) final)
    (T3 (G (Rel mempty)) (P (Rel mempty)) False) where

  final :: Cont ()
  final = Cont $ \inp _ _ -> Command $ \(T3 p g b) -> (T3 p g (b || Text.null inp))

  parseAlts :: [[Symbol]] -> M ()
  -- parseAlts alts | trace ("Alts " ++ show alts) False = undefined
  parseAlts alts = asum (map parseSeq alts)

  parseSeq :: [Symbol] -> M ()
  -- parseSeq s | trace ("Seq  " ++ show s) False = undefined
  parseSeq s = foldr (>>) (pure ()) . map parseSym $ s

  parseSym :: Symbol -> M ()
  -- parseSym s | trace ("Sym  " ++ show s) False = undefined
  parseSym (NT nt) = parseNT nt
  parseSym (T t) = parseT t

  parseNT :: String -> M ()
  -- parseNT nt | trace ("NT   " ++ show nt) False = undefined
  parseNT nt = addCont nt $
    extents nt >>= \case
      Nothing -> do
        descend
        parseAlts (prods ! nt)
        addExtent nt
        resume nt
      Just rs -> asum (map skip rs)

  parseT :: Char -> M ()
  parseT = match

example :: CFG
example = CFG "E" [("E", [[NT "E", T '+', NT "E"], [T 'a']])]

-- >>> parseCFG example "a+a+a+a+a+a"
-- (G {getG = Rel (fromList [(Comm "E" 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 2,[(Slot,2,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 4,[(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 6,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 8,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 10,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,10,<Cont>),(Slot,0,<Cont>)])])},P {getP = Rel (fromList [(Comm "E" 0,[11,11,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,9,7,5,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,9,11,11,11,9,7,5,3,1]),(Comm "E" 2,[11,11,11,11,9,11,11,11,9,11,11,9,7,11,11,11,9,11,11,9,7,5,3]),(Comm "E" 4,[11,11,11,9,11,11,9,7,5]),(Comm "E" 6,[11,11,9,7]),(Comm "E" 8,[11,9]),(Comm "E" 10,[11])])},True)

example3 :: CFG
example3 = CFG "N" [("N", [[T 'a', NT "N"], []])]

example4 :: CFG
example4 = CFG "N" [("N", [[NT "N", T 'a'], []])]

-- >>> parseCFG example3 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm "N" 0,[(Slot,0,<Cont>)]),(Comm "N" 1,[(Slot,0,<Cont>)]),(Comm "N" 2,[(Slot,1,<Cont>)]),(Comm "N" 3,[(Slot,2,<Cont>)]),(Comm "N" 4,[(Slot,3,<Cont>)])])})
--    (P {getP = Rel (fromList [(Comm "N" 0,[0,1,2,3,4]),(Comm "N" 1,[1,2,3,4]),(Comm "N" 2,[2,3,4]),(Comm "N" 3,[3,4]),(Comm "N" 4,[4])])})
--    True

-- >>> parseCFG example4 (Text.pack "aaaa")
-- T3 (G {getG = Rel (fromList [(Comm "N" 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)])])})
--    (P {getP = Rel (fromList [(Comm "N" 0,[4,3,2,1,0])])})
--    True

main :: IO ()
-- main = print (parseCFG example "a+a+a")

main = do
  result <-
    fits $
      mkFitConfig
        (\n -> (\(T3 _ _ b) -> b) $ parseCFG example3 (Text.replicate (fromIntegral n) (Text.pack "a")))
        (1000, 1000000)
  mapM_ print result

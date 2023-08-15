
import Data.List qualified as List
import Test.Tasty.Bench.Fit (fit, mkFitConfig)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Debug.Trace

data CFG = CFG String [(String, [[Symbol]])]

data Symbol = T Char | NT String

(!) :: Eq k => [(k, v)] -> k -> v
xs ! x = case lookup x xs of Just y -> y

lfpFrom :: Eq t => t -> (t -> t) -> t
lfpFrom x0 f = go (0 :: Int) x0 where
  go n _ | traceShow n False = undefined
  go n x = let y = f x in if x == y then x else go (n + 1) y

type Table = [(String, IntMap IntSet)]

denoteCFG :: CFG -> Text -> IntSet
denoteCFG (CFG start g) xs = m ! start IntMap.! 0
  where
    m :: Table
    m =
      lfpFrom
        [(nt, IntMap.fromList [(i, IntSet.empty) | i <- [0.. Text.length xs]]) | nt <- nts]
        ( \m' ->
            [ (nt, IntMap.fromList [(i, IntSet.unions $ map (\p -> denoteProd xs p m' i) (g ! nt)) | i <- [0 .. Text.length xs]])
            | nt <- nts
            ]
        )

    nts = map fst g

bind :: IntSet -> (Int -> IntSet) -> IntSet
bind s k = foldMap k $ IntSet.elems s

denoteProd :: Text -> [Symbol] -> Table -> Int -> IntSet
denoteProd _ [] _ i = IntSet.singleton i
denoteProd xs (s : ss) m i = denoteSymbol xs s m i `bind` \j -> denoteProd xs ss m j

denoteSymbol :: Text -> Symbol -> Table -> Int -> IntSet
denoteSymbol xs (T c) _ i
  | i < Text.length xs && c == Text.index xs i = IntSet.singleton (i + 1)
  | otherwise = IntSet.empty
denoteSymbol _ (NT nt) m i = m ! nt IntMap.! i

example :: CFG
example = CFG "E" [("E", [[NT "E", T '+', NT "E"], [T 'a']])]

main :: IO ()
main = print $ denoteCFG example (Text.pack ('a' : concat (replicate 1000 "+a")))
-- main = print =<< fit (mkFitConfig (\n -> denoteCFG example (Text.pack ('a' : concat (replicate (fromIntegral n) "+a")))) (0, 500))




-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE GADTs #-}
-- import Data.List qualified as List
-- import Test.Tasty.Bench.Fit (fit, mkFitConfig)
-- import Control.DeepSeq
--
-- data Free f a = Pure a | forall x. Free (f x) (x -> Free f a)
--
-- data CFG f a = CFG (f a) (forall x. f x -> [Free (Symbol f) x])
--
-- data Symbol f a where
--   T :: Char -> Symbol f ()
--   NT :: f a -> Symbol f a
--
-- class Funny f where
--   fun :: Applicative g => (f a -> g b) -> g (f a -> b)
--
-- class EqCon f where
--   eqCon :: Con f [] -> Con f [] -> Bool
--
-- splits :: String -> [(String, String)]
-- splits [] = [([], [])]
-- splits xs@(x : xs') = ([], xs) : map (\(y, z) -> (x : y, z)) (splits xs')
--
-- (!) :: Eq k => [(k, v)] -> k -> [v]
-- xs ! x = map snd $ filter ((== x) . fst) xs
--
-- lfpFrom :: (t -> t -> Bool) -> t -> (t -> t) -> t
-- lfpFrom eq x f = let y = f x in if eq x y then x else lfpFrom eq y f
--
-- newtype Con f g = Con { appCon :: forall x. f x -> g x }
--
-- denoteCFG :: forall f a. EqCon f => CFG f a -> String -> [a]
-- denoteCFG (CFG start g) xs = (\c -> appCon c start) =<< m ! xs
--   where
--     m :: [(String, Con f [])]
--     m =
--       lfpFrom ((and .) . zipWith (\(x1,x2) (y1,y2) -> x1 == y1 && eqCon x2 y2))
--         [(xs', Con (const [])) | xs' <- List.tails xs]
--         ( \m' ->
--             [ (xs', Con (\nt -> (\p -> denoteProd p m' xs') =<< (g nt)))
--             | xs' <- List.tails xs
--             ]
--         )
--
-- denoteProd :: Free (Symbol f) a -> [(String, Con f [])] -> String -> [a]
-- denoteProd (Pure x) = \_ xs -> [x | null xs]
-- denoteProd (Free s k) = \m xs -> (\(y, z) -> denoteSymbol s m y >>= \x -> denoteProd (k x) m z) =<< (splits xs)
--
-- denoteSymbol :: Symbol f a -> [(String, Con f [])] -> String -> [a]
-- denoteSymbol (T c) _ [x] = [() | c == x]
-- denoteSymbol T{} _ _ = []
-- denoteSymbol (NT nt) m xs = (\c -> appCon c nt) =<< m ! xs
--
-- data Expr = Plus Expr Expr | A deriving Show
--
-- data E a where E :: E Expr
--
-- instance EqCon E where
--   eqCon (Con f) (Con g) = length (f E) == length (g E)
--
-- -- instance Funny E where
-- --   fun g = let y = g E in _
--
-- instance NFData Expr where
--   rnf (Plus x y) = rnf (x, y)
--   rnf A = ()
--
-- example :: CFG E Expr
-- example = CFG E (\case E -> [Free (NT E) $ \x -> Free (T '+') $ \() -> Free (NT E) $ \y -> Pure $ Plus x y, Free (T 'a') $ \() -> Pure A])
--
-- main :: IO ()
-- main = print =<< fit (mkFitConfig (\n -> null $ denoteCFG example ('a' : concat (replicate (fromIntegral n) "+a"))) (0, 8))
--
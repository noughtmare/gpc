{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

import Gigaparsec

import Control.Applicative ( Alternative((<|>)) )
import Data.Char ( intToDigit )
import Data.Foldable ( asum, traverse_ )
import Data.GADT.Compare
import Data.Type.Equality

data E a where
  E :: E Int
  N :: Int -> E Int
  D :: Int -> E Int
  NDots :: E ()
  NDotsGo :: Int -> E ()
deriving instance Eq (E a)
deriving instance Ord (E a)
instance GEq E where
  geq E E = Just Refl
  geq (N x) (N y) | x == y = Just Refl
  geq (D x) (D y) | x == y = Just Refl
  geq NDots NDots = Just Refl
  geq (NDotsGo x) (NDotsGo y) | x == y = Just Refl
  geq _ _ = Nothing
instance GCompare E where
  gcompare E E = GEQ
  gcompare (N x) (N y) =
    case compare x y of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT
  gcompare (D x) (D y) =
    case compare x y of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT
  gcompare NDots NDots = GEQ
  gcompare (NDotsGo x) (NDotsGo y) =
    case compare x y of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT
  gcompare E _ = GLT
  gcompare _ E = GGT
  gcompare N{} _ = GLT
  gcompare _ N{} = GGT
  gcompare D{} _ = GLT
  gcompare _ D{} = GGT
  gcompare NDots _ = GLT
  gcompare _ NDots = GGT

digit :: Int -> RHS E Int
digit b = asum [i <$ t (intToDigit i) | i <- [0..b - 1]]

number :: Int -> RHS E Int
number b = (\x y -> b * x + y) <$> nt (N b) <*> nt (D b)
  <|> nt (D b)

expr :: RHS E Int
expr = (*) <$> nt E <* t '*' <*> nt E
  <|> (+) <$> nt E <* t '+' <*> nt E 
  <|> number 10

ndots :: RHS E ()
ndots = nt (N 10) >>= nt . NDotsGo

ndotsGo :: Int -> RHS E ()
ndotsGo 0 = pure ()
ndotsGo n = t '.' *> nt (NDotsGo (n - 1))

mkE :: E a -> CFG E a
mkE e = CFG e $ \case
  E -> expr
  N b -> number b
  D b -> digit b
  NDots -> ndots
  NDotsGo n -> ndotsGo n

main :: IO ()
main = do
  -- simple left-recursive
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse (mkE (N 2)) x))
    [ "0"
    , "1"
    , "00"
    , "01"
    , "11"
    , "00000"
    , "01011"
    , "11111"
    ]
  putStrLn "Should fail:"
  traverse_ (\x -> print (x, parse (mkE (N 2)) x))
    [ ""
    , "X"
    , "01X00"
    , "1001X"
    , "X1101"
    ]

  -- more complicated left-recursive
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse (mkE E) x))
    [ "1+1" 
    , "1+2+3"
--    , "1+2+3+4+5+6+7+8+9"
    , "1+2*3"
    ]

  -- monadic
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse (mkE NDots) x))
    [ "5....."
    , "3..."
    , "10.........."
    ]
  putStrLn "Should fail:"
  traverse_ (\x -> print (x, parse (mkE NDots) x))
    [ "5...."
    , "5......"
    , "3....."
    , "10........"
    ]


-- data E a where E :: E Int

-- deriving instance Eq (E a)
-- deriving instance Ord (E a)
-- instance GEq E where
--   geq E E = Just Refl
-- instance GCompare E where
--   gcompare E E = GEQ
-- deriving instance Show (E a)

example :: CFG E Int
example = CFG E $ \E -> nt E *> t '+' *> nt E <|> 0 <$ t 'a'

-- >>> parseCFG example "a+a+a+a+a+a"
-- (G {getG = Rel (fromList [(Comm "E" 0,[(Slot,0,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 2,[(Slot,2,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 4,[(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 6,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 8,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,0,<Cont>)]),(Comm "E" 10,[(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,2,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,0,<Cont>),(Slot,4,<Cont>),(Slot,0,<Cont>),(Slot,6,<Cont>),(Slot,8,<Cont>),(Slot,10,<Cont>),(Slot,0,<Cont>)])])},P {getP = Rel (fromList [(Comm "E" 0,[11,11,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,9,7,5,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,11,9,11,11,11,9,7,11,11,9,11,11,11,9,11,11,11,9,7,5,3,1]),(Comm "E" 2,[11,11,11,11,9,11,11,11,9,11,11,9,7,11,11,11,9,11,11,9,7,5,3]),(Comm "E" 4,[11,11,11,9,11,11,9,7,5]),(Comm "E" 6,[11,11,9,7]),(Comm "E" 8,[11,9]),(Comm "E" 10,[11])])},True)

-- data N a where N :: N Int
-- deriving instance Eq (N a)
-- deriving instance Ord (N a)
-- deriving instance Show (N a)
-- instance GEq N where
--   geq N N = Just Refl
-- instance GCompare N where
--   gcompare N N = GEQ
-- instance GShow N where
--   gshowsPrec _ N = showString "N"

example3 :: CFG E Int
example3 = CFG E $ \E -> (+ 1) <$ t 'a' <*> nt E <|> pure 0

example4 :: CFG E Int
example4 = CFG E $ \E -> (+ 1) <$> nt E <* t 'a' <|> pure 0

-- Turns out example3 takes quadratic space, I hope this can be fixed

-- >>> parse example3 "aaaa"
-- [4]

-- >>> parse example4 "aaaa"
-- [4]

-- main :: IO ()
-- -- main = print (parseCFG example "a+a+a")
-- 
-- main = do
--   print $ parseCFG example3 (Text.pack "aaaa")
--   print $ parseCFG example4 (Text.pack "aaaa")
-- --  result <-
-- --    fits $
-- --      mkFitConfig
-- --        (\n -> (\(T3 _ _ b) -> b) $ parseCFG example4 (Text.replicate (fromIntegral n) (Text.pack "a")))
-- --        (1000, 1000000)
-- --  mapM_ print result
-- 

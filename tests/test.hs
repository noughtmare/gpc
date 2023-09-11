{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Gigaparsec
import Data.Foldable (traverse_)
import Control.Applicative (Alternative((<|>)), asum)
import Data.Char (intToDigit)
import Data.GADT.Compare
import Data.Type.Equality
import Data.List (sort)

main :: IO ()
main = defaultMain tests

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

expr2 :: RHS E Int
expr2 = nt (N 10)
  <|> (+) <$> nt E <* t '+' <*> nt E

ndots :: RHS E ()
ndots = nt (N 10) >>= nt . NDotsGo

ndotsGo :: Int -> RHS E ()
ndotsGo 0 = pure ()
ndotsGo n = t '.' *> nt (NDotsGo (n - 1))

mkE :: E a -> CFG E a
mkE = mkE' False

mkE2 :: E a -> CFG E a
mkE2 = mkE' True

mkE' :: Bool -> E a -> CFG E a
mkE' e2 e = CFG e $ \case
  E -> if e2 then expr2 else expr
  N b -> number b
  D b -> digit b
  NDots -> ndots
  NDotsGo n -> ndotsGo n

tests :: TestTree
tests = testGroup "Tests" [unitTests]

emptyk :: CFG E Int
emptyk = CFG E $ \E -> nt E <|> pure 0

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "base 2 number positive" $
    traverse_ (\(x, y) -> parse (mkE (N 2)) x @?= [y])
      [ ("0",     0)
      , ("1",     1)
      , ("00",    0)
      , ("01",    1)
      , ("11",    3)
      , ("00000", 0)
      , ("01011", 11)
      , ("11111", 31)
      ]
  , testCase "base 2 number negative" $
    traverse_ (\x -> parse (mkE (N 2)) x @?= [])
      [ ""
      , "X"
      , "01X00"
      , "1001X"
      , "X1101"
      ]
  , testCase "expression positive" $
    traverse_ (\(x, y) -> sort (parse (mkE E) x) @?= y)
      [ ("1+1", [2])
      , ("1+2+3", [6,6])
      , ("1+2*3", [7,9])
      ]
  , testCase "expr2 positive" $
    traverse_ (\(x, y) -> parse (mkE2 E) x @?= y)
      [ ("1+2", [3])
      , ("1+2+3", [6,6])
      , ("1+2+3+4", [10,10,10,10,10])
      ]
  , testCase "ndots positive" $
    traverse_ (\x -> parse (mkE NDots) x @?= [()])
      [ "5....."
      , "3..."
      , "10.........."
      ]
  , testCase "ndots negative" $
    traverse_ (\x -> parse (mkE NDots) x @?= [])
      [ "5...."
      , "5......"
      , "3....."
      , "10"
      ]
  , localOption (Timeout 1000000 "1s") $
    testCase "emptyk positive" $ 
      parse emptyk "" @?= [0]
  ]

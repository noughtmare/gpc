{-# LANGUAGE TemplateHaskellQuotes #-}
import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Gigaparsec
import Data.Foldable (traverse_)
import Control.Applicative (Alternative((<|>)), asum)
import Data.Char (intToDigit)

main :: IO ()
main = defaultMain tests

digit :: Int -> Parser Int
digit b = asum [i <$ char (intToDigit i) | i <- [0..b - 1]]

number :: Int -> Parser Int
number b = 'number
  ::= (\x y -> b * x + y) <$> number b <*> digit b
  <|> digit b

expr :: Parser Int
expr = 'expr
  ::= (*) <$> expr <* char '*' <*> expr
  <|> (+) <$> expr <* char '+' <*> expr 
  <|> number 10

ndots :: Parser ()
ndots = number 10 >>= go where
  go 0 = pure ()
  go n = char '.' *> go (n - 1)


tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "base 2 number positive" $
    traverse_ (\(x, y) -> parse (number 2) x @?= [y])
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
    traverse_ (\x -> parse (number 2) x @?= [])
      [ ""
      , "X"
      , "01X00"
      , "1001X"
      , "X1101"
      ]
  , testCase "expression positive" $
    traverse_ (\(x, y) -> parse expr x @?= y)
      [ ("1+1", [2])
      , ("1+2+3", [6,6])
      , ("1+2*3", [9,7])
      ]
  , testCase "ndots positive" $
    traverse_ (\x -> parse ndots x @?= [()])
      [ "5....."
      , "3..."
      , "10.........."
      ]
  , testCase "ndots negative" $
    traverse_ (\x -> parse ndots x @?= [])
      [ "5...."
      , "5......"
      , "3....."
      , "10........"
      ]
  , testCase "fail" $
    assertBool "fail" False
  ]
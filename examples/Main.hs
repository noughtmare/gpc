{-# LANGUAGE TemplateHaskellQuotes #-}

import Gigaparsec

import Control.Applicative ( Alternative((<|>)) )
import Data.Char ( intToDigit )
import Data.Foldable ( asum, traverse_ )

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

main :: IO ()
main = do
  -- simple left-recursive
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse (number 2) x))
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
  traverse_ (\x -> print (x, parse (number 2) x))
    [ ""
    , "X"
    , "01X00"
    , "1001X"
    , "X1101"
    ]

  -- more complicated left-recursive
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse expr x))
    [ "1+1" 
    , "1+2+3"
--    , "1+2+3+4+5+6+7+8+9"
    , "1+2*3"
    ]

  -- monadic
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse ndots x))
    [ "5....."
    , "3..."
    , "10.........."
    ]
  putStrLn "Should fail:"
  traverse_ (\x -> print (x, parse ndots x))
    [ "5...."
    , "5......"
    , "3....."
    , "10........"
    ]
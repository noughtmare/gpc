import Gigaparsec ( Parser, reify, nt, parse, decode, char )

import Control.Applicative ( asum, Alternative((<|>)) )
import Control.Monad ( void )
import Data.Char ( intToDigit )

many :: Parser a -> Parser [a]
many p = res where res = nt $ (:) <$> p <*> res <|> pure []

-- does not work: many p = nt $ (:) <$> p <*> many p <|> pure []

p1 :: Parser ()
p1 = a *> a where
    a = nt $ void (char 'a') <|> e
    e = nt $ pure ()

p2 :: Parser Int
p2 =
  nt $ (*) <$> p2 <* char '*' <*> p2
  <|> (+) <$> p2 <* char '+' <*> p2
  <|> asum [x <$ char (intToDigit x) | x <- [0..9]]

main :: IO ()
main = print (decode (parse (g, z) "1+2*3") z 0 5) where
    (g, z) = reify p2

-- Will print:
-- [7,9]
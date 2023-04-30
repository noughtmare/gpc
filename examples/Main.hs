{-# LANGUAGE GADTs #-}
import Gigaparsec

import Control.Applicative ( asum, Alternative((<|>)) )
import Data.Char ( intToDigit )
import Data.Type.Equality

data Number a where
    Number :: Number Int
deriving instance Show (Number a)
instance EqF Number where
    eqF Number Number = Just Refl
instance OrdF Number where
    compareF Number Number = EQ

number :: Number < f => Alt f Int
number = send Number

data Digit a where
    Digit :: Digit Int
deriving instance Show (Digit a)
instance EqF Digit where
    eqF Digit Digit = Just Refl
instance OrdF Digit where
    compareF Digit Digit = EQ

digit :: Digit < f => Alt f Int
digit = send Digit

-- ergonomics idea: use overloaded labels or template haskell to avoid boilerplate

data Expr a where
    Expr :: Expr Int
deriving instance Show (Expr a)
instance EqF Expr where
    eqF Expr Expr = Just Refl
instance OrdF Expr where
    compareF Expr Expr = EQ

expr :: Expr < f => Alt f Int
expr = send Expr

-- TODO: higher order nonterminals, e.g.:
data Many p a where
    Many :: p a -> Many m [a]

-- TODO: This would require using a free monad(plus) rather than just a free alternative:
data ReplicateM p a where
    ReplicateM :: Int -> p a -> ReplicateM p [a]

gram :: Gram (Expr + Number + Digit + End)
gram = G (\Expr -> (+) <$> expr <* match '+' <*> expr <|> (*) <$> expr <* match '*' <*> expr <|> number)
  <||> G (\Number -> (\x y -> 10 * x + y) <$> number <*> digit <|> digit)
  <||> G (\Digit -> asum [x <$ match (intToDigit x) | x <- [0..9]])
  <||> end

main :: IO ()
main = print (parse gram (inj Expr) "1+2*3")

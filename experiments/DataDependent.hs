{-# LANGUAGE DeriveFunctor #-}
import Control.Applicative
import Data.Char

newtype Parser s a = Parser { parse :: String -> s -> [(a, String, s)] } deriving Functor

instance Applicative (Parser s) where
  pure x = Parser $ \xs s -> [(x, xs, s)]
  Parser p <*> Parser q = Parser $ \xs s -> do
    (f, xs', s') <- p xs s
    (x, xs'', s'') <- q xs' s'
    pure (f x, xs'', s'')

instance Alternative (Parser s) where
  empty = Parser $ \_ _ -> []
  Parser p <|> Parser q = Parser $ \xs s ->
    p xs s ++ q xs s

char :: Char -> Parser s Char
char c = Parser $ \xs s ->
  case xs of
    c' : xs' | c == c' -> [(c, xs', s)]
    _ -> []

put :: Parser s' s -> Parser s a -> Parser s' a
put (Parser p) (Parser q) = Parser $ \xs s -> do
  (s', xs', _) <- p xs s
  (x, xs'', _) <- q xs' s'
  pure (x, xs'', s)

modify :: (s -> [s]) -> Parser s ()
modify f = Parser $ \xs s -> [((), xs, s') | s' <- f s]

dependentReplicate :: Parser s Int -> Parser Int a -> Parser s [a]
dependentReplicate p1 p2 = put p1 rest where
  rest = (:) <$ modify (\s -> [s | s > 0]) <*> p2 <* modify (\s -> [s - 1]) <*> rest
      <|> [] <$ modify (\s -> [s | s == 0])

digit :: Parser s Int
digit = asum [digitToInt <$> char (intToDigit i) | i <- [0..9]]

main :: IO ()
main = print $ parse (dependentReplicate digit (char '.')) "4...." ()
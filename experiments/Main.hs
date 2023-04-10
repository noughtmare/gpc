{-# LANGUAGE DeriveFunctor #-}
import Control.Applicative ( asum, Alternative((<|>), empty, many) )
import Data.Char ( digitToInt, intToDigit )

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

put :: Parser s' s -> Parser (s,s') a -> Parser s' a
put (Parser p) (Parser q) = Parser $ \xs s -> do
  (s', xs', t') <- p xs s
  (x, xs'', (_,t'')) <- q xs' (s',t')
  pure (x, xs'', t'')

modify :: (s -> [s]) -> Parser s ()
modify f = Parser $ \xs s -> [((), xs, s') | s' <- f s]

under :: Parser t a -> Parser (s, t) a
under (Parser p) = Parser $ \xs (s0,t) -> do
    (x, xs', t') <- p xs t
    pure (x, xs', (s0, t'))

dependentReplicate :: Parser s Int -> Parser s a -> Parser s [a]
dependentReplicate p1 p2 = put p1 $
  many (modify (\s -> [s | fst s > 0]) *> under p2 <* modify (\(s,t) -> [(s - 1, t)]))
   <* modify (\s -> [s | fst s == 0])

digit :: Parser s Int
digit = asum [digitToInt <$> char (intToDigit i) | i <- [0..9]]

main :: IO ()
main = do
    print $ parse (dependentReplicate digit (char '.')) "4..." ()
    print $ parse (dependentReplicate digit (char '.')) "4...." ()
    print $ parse (dependentReplicate digit (char '.')) "4....." ()
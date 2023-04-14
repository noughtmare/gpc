{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LexicalNegation #-}
{-# LANGUAGE RankNTypes #-}
import Control.Applicative ( asum, Alternative((<|>), empty, many) )
import Data.Char ( digitToInt, intToDigit )
import Data.Bifunctor
import Data.Functor.Const
import qualified Data.IntMap as M
import GHC.Exts (Any)

data Env = Env !Int (M.IntMap Any)
newtype Ref a = Ref Int

emptyEnv :: Env
emptyEnv = undefined

lookupEnv :: Env -> Ref a -> a
lookupEnv = undefined

modifyEnv :: Env -> Ref a -> (a -> a) -> Env
modifyEnv = undefined

freshEnv :: Env -> a -> (Ref a, Env)
freshEnv = undefined

newtype Parser a = Parser { parse :: String -> Env -> [(a, String, Env)] } deriving Functor

instance Applicative Parser where
  pure x = Parser $ \xs s -> [(x, xs, s)]
  Parser p <*> Parser q = Parser $ \xs s -> do
    (f, xs', s') <- p xs s
    (x, xs'', s'') <- q xs' s'
    pure (f x, xs'', s'')

instance Alternative Parser where
  empty = Parser $ \_ _ -> []
  Parser p <|> Parser q = Parser $ \xs s ->
    p xs s ++ q xs s

char :: Char -> Parser Char
char c = Parser $ \xs s ->
  case xs of
    c' : xs' | c == c' -> [(c, xs', s)]
    _ -> []

with :: Parser a -> (Ref a -> Parser b) -> Parser b
with (Parser p) f = Parser $ \s env -> do
    (x, s', env') <- p s env
    let (r, env'') = freshEnv env' x
    parse (f r) s' env''

modify :: Ref s -> (s -> s) -> Parser ()
modify = undefined

guard :: Ref s -> (s -> Bool) -> Parser ()
guard = undefined

dependentReplicate :: Parser Int -> Parser a -> Parser [a]
dependentReplicate p1 p2 = with p1 $ \s ->
  many (guard s (> 0) *> p2 <* modify s (- 1))
   <* guard s (== 0)

digit :: Parser Int
digit = asum [digitToInt <$> char (intToDigit i) | i <- [0..9]]

main :: IO ()
main = do
    print $ map (\(x,y,_) -> (x,y)) $ parse (dependentReplicate digit (char '.')) "4..." emptyEnv
    print $ map (\(x,y,_) -> (x,y)) $ parse (dependentReplicate digit (char '.')) "4...." emptyEnv
    print $ map (\(x,y,_) -> (x,y)) $ parse (dependentReplicate digit (char '.')) "4....." emptyEnv
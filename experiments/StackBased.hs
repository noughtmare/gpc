{-# LANGUAGE PatternSynonyms #-}

import Control.Monad.State
import Data.Foldable (traverse_)
import Data.Coerce (coerce)

type Id = String
-- (new)type Id a = Language.Haskell.TH.Name
newtype Parser = Parser { alts :: [P] }
data P = T Char Parser | NT Id Parser Parser | Success
-- data P a = T Char Parser | forall b. NT (Id b) Parser (b -> Parser) | Success a

success :: Parser
success = Parser [Success]

char :: Char -> Parser
char c = Parser [T c success]

pattern (::=) :: String -> Parser -> Parser
pattern name ::= p = Parser [NT name p (Parser [Success])]
infix 1 ::= -- tighter than $ but looser than <>

-- sequencing parsers (would be <*>/<*/*> from Applicative)
(%>) :: Parser -> Parser -> Parser
Parser ps %> q0 = foldMap (`seqP` q0) ps where
  seqP :: P -> Parser -> Parser
  seqP (T c p) q = Parser [T c (p %> q)]
  seqP (NT n p p') q = Parser [NT n p (p' %> q)]
  seqP Success q = q
infixr 7 %> -- tighter than <>

-- introducing new alternatives (would be <|> from Alternative)
instance Semigroup Parser where
  Parser ps <> Parser qs = Parser (ps <> qs)
instance Monoid Parser where
  mempty = Parser []

newtype Stack = Stack { unStack :: [((Id, Int), [(Stack,Parser)], Parser)] }
  deriving (Semigroup, Monoid)

unwind :: Id -> Int -> Stack -> (Stack, Stack)
unwind n i = coerce . span (\((n',i'),_,_) -> n /= n' || i /= i') . unStack

parse :: Parser -> String -> Bool
parse p0 xs0 = evalState (parse' 0 xs0 p0) (Stack []) where
  parse' i xs = fmap or . traverse (go i xs) . alts

  go :: Int -> String -> P -> State Stack Bool
  go i (x:xs) (T c p) | x == c = parse' (i + 1) xs p
  go _ _ T{} = pure False

  go i xs (NT n p p') = state $ \s -> 
    -- Find out if the current (n, i) combination is already on the stack
    case coerce (unwind n i s) of
      -- If not, push a new empty continuation on the initial stack (stack0) and continue running
      (stack0, []) -> runState (parse' i xs p) (Stack (((n,i), [], p') : unStack stack0))
      -- If so, add the p' as a new continuation, fail the current branch, and do update the stack
      (stack0, (_,q,q'):stack) -> (False, Stack (((n,i), (stack0, p') : q, q') : stack))

  go i xs Success = state $ \stack ->
    case unStack stack of
      -- If there's something on the stack we can either:
      -- use it to continue parsing, or ignore it and pop it from the stack
      (_, ks, p') : stack' -> 
        ( evalState (parse' i xs p') (Stack stack')
          || or [evalState (parse' i xs p) (Stack (unStack s ++ unStack stack)) | (s,p) <- ks]
        , stack)
      -- If there's nothing on the stack then we succeed iff there is also no remaining input
      [] -> (null xs, stack)

digit :: Parser
digit = char '0' <> char '1'

number :: Parser
number = "N" ::= number %> digit <> digit

main :: IO ()
main = do
  putStrLn "Should succeed:"
  traverse_ (\x -> print (x, parse number x))
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
  traverse_ (\x -> print (x, parse number x))
    [ ""
    , "X"
    , "01X00"
    , "1001X"
    , "X1101"
    ]

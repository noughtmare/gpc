{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}

import Gigaparsec

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate)
import Unsafe.Coerce ( unsafeCoerce )
import Control.Applicative ( asum, Alternative((<|>)) )
import Data.Functor.Compose ( Compose(Compose) )
import Control.Monad ( void )
import Data.Reify ( reifyGraph, MuRef(..), Graph(Graph), Unique )
import GHC.Exts (Any)
import System.IO.Unsafe (unsafePerformIO)
-- import Debug.RecoverRTTI ( anythingToString )
import Data.Char (intToDigit)
import Data.Maybe (fromMaybe)

many :: Parser a -> Parser [a]
many p = res where res = nt $ (:) <$> p <*> res <|> pure []

-- does not work: many p = nt $ (:) <$> p <*> many p <|> pure []

p1 :: Parser ()
p1 = void (a *> a) where
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
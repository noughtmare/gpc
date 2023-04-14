{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Gigaparsec.Syntax where

import Gigaparsec.Core

import GHC.Exts (Any)
import Control.Applicative
import Data.Reify
import qualified Data.Map as Map
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)

newtype Parser a = Parser (Alt Parser Action a)
    deriving (Functor, Applicative, Alternative) via Alt Parser Action

instance MuRef (Parser a) where
    type DeRef (Parser a) = ListF (ActionF Any)
    mapDeRef :: forall f u. Applicative f => (forall b. (MuRef b, DeRef (Parser a) ~ DeRef b) => b -> f u) -> Parser a -> f (DeRef (Parser a) u)
    mapDeRef _ (Parser (Alt [])) = pure Nil
    mapDeRef f (Parser (Alt (x:xs))) = Cons <$> helper x <*> mapDeRef f (Parser (Alt xs)) where
        helper :: forall b. AltF Parser Action b -> f (ActionF Any u)
        helper (Pure a) = pure (AscendF (unsafeCoerce a))
        helper (Ap (Match c) r) = MatchF c <$> unsafeCoerce (helper r)
        helper (Ap (Descend y) r) = DescendF <$> f y <*> unsafeCoerce (helper r)

reify :: Parser a -> (G Unique, Name Unique a)
reify acts = (G (Map.fromList [ (u, f x') | (u, x') <- xs ]), Name x) where
    (Graph xs x) = unsafePerformIO $ reifyGraph acts

    f :: ListF (ActionF Any) Unique -> [AltF (Name Unique) Action Any]
    f Nil = []
    f (Cons h t) = g h ++ f t

    g :: forall a. ActionF a Unique -> [AltF (Name Unique) Action a]
    g (AscendF r) = [Pure r]
    g (MatchF c r) = Ap (Match c) <$> g r
    g (DescendF u r) = Ap (Descend (Name u)) <$> g r

nt :: Parser a -> Parser a
nt xs = Parser $ Alt [Ap (Descend xs) (pure id)]

char :: Char -> Parser Char
char c = Parser (Alt [Ap (Match c) (pure (const c))])
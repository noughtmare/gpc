{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Gigaparsec.Syntax (Parser, reify, char, nt) where

import Gigaparsec.Core

import GHC.Exts (Any)
import Control.Applicative ( Const(..), Alternative )
import Data.Reify
import qualified Data.Map as Map
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)
import Data.Kind ( Type )

type Parser :: Type -> Type
newtype Parser a = Parser (Alt Parser Action a)
    deriving (Functor, Applicative, Alternative) via Alt Parser Action

data AltListF a f = Nil | Cons (AltF (Const f) Action a) (AltListF a f)

instance MuRef (Parser a) where
    type DeRef (Parser a) = AltListF Any
    mapDeRef :: forall f u. Applicative f => (forall b. (MuRef b, DeRef (Parser a) ~ DeRef b) => b -> f u) -> Parser a -> f (DeRef (Parser a) u)
    mapDeRef _ (Parser (Alt [])) = pure Nil
    mapDeRef f (Parser (Alt (x:xs))) = Cons <$> helper x <*> mapDeRef f (Parser (Alt xs)) where
        helper :: forall b. AltF Parser Action b -> f (AltF (Const u) Action Any)
        helper (Pure a) = pure (Pure (unsafeCoerce a))
        helper (Ap (Match c) r) = Ap (Match c) <$> unsafeCoerce (helper r)
        helper (Ap (Descend y) r) = Ap . Descend . Const <$> f y <*> unsafeCoerce (helper r)

reify :: Parser a -> (G Unique, Name Unique a)
reify acts = (G (Map.fromList [ (u, f x') | (u, x') <- xs ]), Name x) where
    (Graph xs x) = unsafePerformIO $ reifyGraph acts

    f :: AltListF Any Unique -> [AltF (Name Unique) Action Any]
    f Nil = []
    f (Cons h t) = g h ++ f t

    g :: forall a. AltF (Const Unique) Action a -> [AltF (Name Unique) Action a]
    g (Pure r) = [Pure r]
    g (Ap (Match c) r) = Ap (Match c) <$> g r
    g (Ap (Descend u) r) = Ap (Descend (Name (getConst u))) <$> g r

nt :: Parser a -> Parser a
nt xs = Parser $ Alt [Ap (Descend xs) (pure id)]

char :: Char -> Parser Char
char c = Parser (Alt [Ap (Match c) (pure (const c))])

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}

module Gigaparsec.Core where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Unsafe.Coerce ( unsafeCoerce )
import GHC.Exts (Any)
import Data.Maybe (fromMaybe)
import Data.Kind
import Control.Applicative
import Data.Functor.Compose

data ActionF a f = AscendF a | MatchF Char (ActionF (() -> a) f) | forall b. DescendF f (ActionF (b -> a) f)
instance Show f => Show (ActionF a f) where
    show AscendF{} = "AscendF"
    show (MatchF c xs) = "(MatchF "  ++ show c ++ " " ++ show xs ++ ")"
    show (DescendF x xs) = "(DescendF " ++ show x ++ " " ++ show xs ++ ")"
data ListF a f = Nil | Cons (a f) (ListF a f) deriving Show

data Action m a where
    Match :: Char -> Action m ()
    Descend :: m a -> Action m a 

-- Free alternative, see https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html
-- But this one is higher-order.

type Alt :: (Type -> Type) -> ((Type -> Type) -> Type -> Type) -> Type -> Type
newtype Alt m f a = Alt [AltF m f a]
    deriving (Functor, Applicative, Alternative) via Compose [] (AltF m f)
type AltF :: (Type -> Type) -> ((Type -> Type) -> Type -> Type) -> Type -> Type
data AltF m f a = Pure a | forall b. Ap (f m b) (AltF m f (b -> a))
deriving instance Functor (AltF m f)
instance Applicative (AltF m f) where
    pure = Pure
    Pure f <*> q = fmap f q
    Ap x p <*> q = Ap x (flip <$> p <*> q)

type Name :: Type -> Type -> Type
newtype Name n a = Name n deriving Show

newtype G n = G (Map n [AltF (Name n) Action Any])

lookupG :: forall n a. Ord n => G n -> Name n a -> [AltF (Name n) Action a]
lookupG (G m) (Name n) = unsafeCoerce (m Map.! n)

compareName :: Ord n => Name n a -> Name n b -> Ordering
compareName (Name x) (Name y) = compare x y

compareSlot :: Ord n => Slot n a -> Slot n b -> Ordering
compareSlot (Slot x1 x2 x3 _ _) (Slot y1 y2 y3 _ _) = compareName x1 y1 <> compare x2 y2 <> compare x3 y3

compareDescriptor :: Ord n => Descriptor n a -> Descriptor n b -> Ordering
compareDescriptor (Descriptor x1 x2 x3 _) (Descriptor y1 y2 y3 _) = compareSlot x1 y1 <> compare x2 y2 <> compare x3 y3

data Deps n a b where
    Self :: Deps n a a
    Dep :: Name n b -> Int -> Int -> Deps n a c -> Deps n a (b -> c)
deriving instance Show n => Show (Deps n a b)

data Slot n a = forall b. Slot !(Name n a) !Int !Int (Deps n a b) (AltF (Name n) Action b)
data Descriptor n a = Descriptor (Slot n a) !Int !Int String
data SomeDescriptor n = forall a. SomeDescriptor (Descriptor n a)
instance Ord n => Eq (SomeDescriptor n) where
    SomeDescriptor x == SomeDescriptor y = compareDescriptor x y == EQ
instance Ord n => Ord (SomeDescriptor n) where
    compare (SomeDescriptor x) (SomeDescriptor y) = compareDescriptor x y

initialDescriptor :: Name n a -> String -> Int -> AltF (Name n) Action a -> SomeDescriptor n
initialDescriptor n xs i act = SomeDescriptor (Descriptor (Slot n i 0 Self act) 0 0 xs)

newtype WaitForAscend n = WA (Map (n, Int) [Int -> String -> SomeDescriptor n])
newtype WaitForDescend n = WD (Map (n, Int) [(Int, String)])

emptyWA :: WaitForAscend n
emptyWA = WA Map.empty

lookupWA :: forall a n. Ord n => WaitForAscend n -> Name n a -> Int -> [Int -> String -> SomeDescriptor n]
lookupWA (WA m) (Name n) k = fromMaybe [] (m Map.!? (n, k))

insertWA :: Ord n => Name n a -> Int -> (Int -> String -> SomeDescriptor n) -> WaitForAscend n -> WaitForAscend n
insertWA (Name n) k f (WA m) = WA (Map.insertWith (++) (n, k) [f] m)

emptyWD :: WaitForDescend n
emptyWD = WD Map.empty

lookupWD :: forall a n. Ord n => WaitForDescend n -> Name n a -> Int -> [(Int, String)]
lookupWD (WD m) (Name n) k = fromMaybe [] (m Map.!? (n, k))

insertWD :: Ord n => Name n a -> Int -> (Int, String) -> WaitForDescend n -> WaitForDescend n
insertWD (Name n) k x (WD m) = WD (Map.insertWith (++) (n, k) [x] m)

parse :: forall n a. Ord n => (G n, Name n a) -> String -> Set (SomeDescriptor n)
parse (g, z) xs0 = go Set.empty emptyWA emptyWD (zipWith (initialDescriptor z xs0) [0..] (lookupG g z)) where
    go :: Set (SomeDescriptor n) -> WaitForAscend n -> WaitForDescend n -> [SomeDescriptor n] -> Set (SomeDescriptor n)
    go u wa wd (d : rs) | d `Set.member` u = go u wa wd rs
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x a i ds (Ap (Match c) r)) l k xs)) : rs)
        | c' : xs' <- xs, c == c' = go (Set.insert d u) wa wd (SomeDescriptor (Descriptor (Slot x a (i + 1) ds (($ ()) <$> r)) l (k + 1) xs') : rs)
        | otherwise = go u wa wd rs
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x a i ds (Ap (Descend n) next)) l k xs)) : rs)
        = go (Set.insert d u) (insertWA n k (\r xs' -> SomeDescriptor (Descriptor (Slot x a (i + 1) (Dep n k r ds) next) l r xs')) wa) wd $ concat
            [ [ SomeDescriptor (Descriptor (Slot n a' 0 Self acts) k k xs) | (a', acts) <- zip [0..] (lookupG g n) ]
            , [ SomeDescriptor (Descriptor (Slot x a (i + 1) (Dep n k r ds) next) l r xs') | (r, xs') <- lookupWD wd n k ]
            , rs
            ]
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x _ _ _ (Pure _)) k r xs)) : rs)
        = go (Set.insert d u) wa (insertWD x k (r, xs) wd)
            ([ f r xs | f <- lookupWA wa x k ] ++ rs)
    go u _ _ [] = u

decode :: forall n a. (Show n, Ord n) => Set (SomeDescriptor n) -> Name n a -> Int -> Int -> [a]
decode ds0 = lookupM where
    m :: Map (n, Int, Int) [Any]
    m = Map.fromListWith (++)
        [ ((x, l, r), map unsafeCoerce (go ds [a]))
        | SomeDescriptor (Descriptor (Slot (Name x) _ _ ds (Pure a)) l r _) <- Set.toList ds0
        ]

    lookupM :: forall c. Name n c -> Int -> Int -> [c]
    lookupM (Name n) l r = maybe [] (map unsafeCoerce) (m Map.!? (n, l, r)) 

    go :: forall b c. Deps n b c -> [c] -> [b]
    go Self x = x
    go (Dep n l r xs) fs = go xs $ fs <*> lookupM n l r
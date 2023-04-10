{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}

module Gigaparsec ( Parser, reify, nt, parse, decode, char ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate)
import Control.Applicative (Alternative)
import Unsafe.Coerce ( unsafeCoerce )
import Data.Functor.Compose ( Compose(Compose) )
import Data.Reify ( reifyGraph, MuRef(..), Graph(Graph), Unique )
import GHC.Exts (Any)
import System.IO.Unsafe (unsafePerformIO)
-- import Debug.RecoverRTTI ( anythingToString )
import Data.Maybe (fromMaybe)

data ActionF a f = AscendF a | MatchF Char (ActionF a f) | forall b. DescendF f (ActionF (b -> a) f) | FailF | ChooseF (ActionF a f) (ActionF a f)
instance Show f => Show (ActionF a f) where
    show AscendF{} = "AscendF"
    show (MatchF c xs) = "(MatchF "  ++ show c ++ " " ++ show xs ++ ")"
    show (DescendF x xs) = "(DescendF " ++ show x ++ " " ++ show xs ++ ")"
    show FailF = "FailF"
    show ChooseF{} = "ChooseF"
data ListF a f = Nil | Cons (a f) (ListF a f) deriving Show

data Action' n a = Ascend' a | Match' Char (Action' n a) | forall b. Descend' (Actions n b) (Action' n (b -> a)) | Fail' | Choose' (Action' n a) (Action' n a)
deriving instance Functor (Action' n)
newtype Actions n a = Actions [Action' n a]
    deriving (Functor)
    deriving (Applicative, Alternative) via (Compose [] (Action' n))

instance Applicative (Action' n) where
    pure = Ascend'
    Ascend' f <*> x = fmap f x
    Match' c k1 <*> k2 = Match' c (k1 <*> k2)
    Descend' n k1 <*> k2 = Descend' n (flip <$> k1 <*> k2)
    Fail' <*> _ = Fail'
    Choose' x y <*> z = Choose' (x <*> z) (y <*> z)


instance MuRef (Actions n a) where
    type DeRef (Actions n a) = ListF (ActionF Any)
    mapDeRef :: forall f u. Applicative f => (forall b. (MuRef b, DeRef (Actions n a) ~ DeRef b) => b -> f u) -> Actions n a -> f (DeRef (Actions n a) u)
    mapDeRef _ (Actions []) = pure Nil
    mapDeRef f (Actions (x:xs)) = Cons <$> helper x <*> mapDeRef f (Actions xs) where
        helper :: forall b. Action' n b -> f (ActionF Any u)
        helper (Ascend' a) = pure (AscendF (unsafeCoerce a))
        helper (Match' c r) = MatchF c <$> helper r
        helper (Descend' y r) = DescendF <$> f y <*> unsafeCoerce (helper r)
        helper Fail' = pure FailF
        helper (Choose' l r) = ChooseF <$> helper l <*> helper r

newtype Name n a = Name n deriving Show

reify :: Actions Unique a -> (G Unique, Name Unique a)
reify acts = (G (Map.fromList [ (u, f x') | (u, x') <- xs ]), Name x) where
    (Graph xs x) = unsafePerformIO $ reifyGraph acts

    f :: ListF (ActionF Any) Unique -> [Action Unique Any]
    f Nil = []
    f (Cons h t) = g h ++ f t

    g :: forall a. ActionF a Unique -> [Action Unique a]
    g (AscendF r) = [Ascend r]
    g (MatchF c r) = Match c <$> g r
    g (DescendF u r) = Descend (Name u) <$> g r
    g FailF = []
    g (ChooseF l r) = g l ++ g r

data Action n a = Ascend a | Match Char (Action n a) | forall b. Descend (Name n b) (Action n (b -> a))
deriving instance Functor (Action n)
instance Applicative (Action n) where
    pure = Ascend
    Ascend f <*> x = fmap f x
    Match c k1 <*> k2 = Match c (k1 <*> k2)
    Descend n k1 <*> k2 = Descend n (flip <$> k1 <*> k2)
instance Show n => Show (Action n a) where
    show (Ascend _) = "Ascend" -- ++ anythingToString x ++ ")"
    show (Match c _) = "(Match " ++ show c ++ ")"
    show (Descend (Name n) _) = "(Descend " ++ show n ++ ")"

newtype G n = G (Map n [Action n Any])

lookupG :: forall n a. Ord n => G n -> Name n a -> [Action n a]
lookupG (G m) (Name n) = unsafeCoerce (m Map.! n)

nt :: Actions n a -> Actions n a
nt xs = Actions [Descend' xs (pure id)]

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

data Slot n a = forall b. Slot !(Name n a) !Int !Int (Deps n a b) (Action n b)
data Descriptor n a = Descriptor (Slot n a) !Int !Int String
data SomeDescriptor n = forall a. SomeDescriptor (Descriptor n a)
instance Ord n => Eq (SomeDescriptor n) where
    SomeDescriptor x == SomeDescriptor y = compareDescriptor x y == EQ
instance Ord n => Ord (SomeDescriptor n) where
    compare (SomeDescriptor x) (SomeDescriptor y) = compareDescriptor x y
instance Show n => Show (SomeDescriptor n) where
    show (SomeDescriptor (Descriptor (Slot (Name x) a i deps act) l k _)) =
        unwords ["<", show x, "::=", "(" ++ show deps ++ ")", show act, intercalate ", " [show a, show i, show l, show k], ">"]

initialDescriptor :: Name n a -> String -> Int -> Action n a -> SomeDescriptor n
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
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x a i ds (Match c r)) l k xs)) : rs)
        | c' : xs' <- xs, c == c' = go (Set.insert d u) wa wd (SomeDescriptor (Descriptor (Slot x a (i + 1) ds r) l (k + 1) xs') : rs)
        | otherwise = go u wa wd rs
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x a i ds (Descend n next)) l k xs)) : rs)
        = go (Set.insert d u) (insertWA n k (\r xs' -> SomeDescriptor (Descriptor (Slot x a (i + 1) (Dep n k r ds) next) l r xs')) wa) wd $ concat
            [ [ SomeDescriptor (Descriptor (Slot n a' 0 Self acts) k k xs) | (a', acts) <- zip [0..] (lookupG g n) ]
            , [ SomeDescriptor (Descriptor (Slot x a (i + 1) (Dep n k r ds) next) l r xs') | (r, xs') <- lookupWD wd n k ]
            , rs
            ]
    go u wa wd (d@(SomeDescriptor (Descriptor (Slot x _ _ _ (Ascend _)) k r xs)) : rs)
        = go (Set.insert d u) wa (insertWD x k (r, xs) wd)
            ([ f r xs | f <- lookupWA wa x k ] ++ rs)
    go u _ _ [] = u

decode :: forall n a. (Show n, Ord n) => Set (SomeDescriptor n) -> Name n a -> Int -> Int -> [a]
decode ds0 = lookupM where
    m :: Map (n, Int, Int) [Any]
    m = Map.fromListWith (++)
        [ ((x, l, r), map unsafeCoerce (go ds [a]))
        | SomeDescriptor (Descriptor (Slot (Name x) _ _ ds (Ascend a)) l r _) <- Set.toList ds0
        ]

    lookupM :: forall c. Name n c -> Int -> Int -> [c]
    lookupM (Name n) l r = maybe [] (map unsafeCoerce) (m Map.!? (n, l, r)) 

    go :: forall b c. Deps n b c -> [c] -> [b]
    go Self x = x
    go (Dep n l r xs) fs = go xs $ fs <*> lookupM n l r


char :: Char -> Actions n Char
char c = Actions [Match' c (pure c)]

type Parser a = Actions Unique a
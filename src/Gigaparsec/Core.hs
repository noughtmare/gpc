
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Gigaparsec.Core where -- (parse, match, send, G(G), Gram, (<||>), type (+), End, end, Alt, type (<)(..), OrdF(..), EqF(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor.Compose ( Compose(Compose) )
import Data.Proxy ( Proxy(..) )
import Data.Type.Equality
import qualified Data.List as List
import Data.Bifunctor (second, Bifunctor (bimap))
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import Data.List (foldl')
import Control.Applicative (Alternative)
-- import Debug.Trace (traceShow)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (ap, (>=>))

data (f + g) a = L (f a) | R (g a) deriving Show

type family Equal a b where
    Equal a a = True
    Equal a b = False

class f < g where
    inj :: f a -> g a

instance In (Equal f g) f g h => f < (g + h) where
    inj = injIn (Proxy :: Proxy (Equal f g))

class In b f g h where
    injIn :: Proxy b -> f a -> (g + h) a

instance (f ~ g) => In True f g h where
    injIn Proxy = L
instance f < h => In False f g h where
    injIn Proxy = R . inj

instance (OrdF f, OrdF g) => OrdF (f + g) where
    compareF (L x) (L y) = compareF x y
    compareF (L _) (R _) = LT
    compareF (R _) (L _) = GT
    compareF (R x) (R y) = compareF x y

data Match a where
    Match :: Char -> Match ()
deriving instance Show (Match a)

instance OrdF Match where
    compareF (Match x) (Match y) = compare x y

send :: (f < g) => f a -> Alt g a
send x = Alt [FreeF (inj x) pure]

match :: (Match < f) => Char -> Alt f ()
match c = send (Match c)

-- Free(r) monadplus, see https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html
-- But this one also satisfies right distributivity: f <*> (x <|> y) = (f <*> x) <|> (f <*> y)

newtype Alt f a = Alt { alternatives :: [AltF f a] }
    deriving (Functor, Applicative, Alternative) via Compose [] (AltF f)
deriving instance (forall x. Show (f x)) => Show (Alt f a)

instance Monad (Alt f) where
    Alt xs >>= k = Alt $ xs >>= \case
        Pure x -> alternatives (k x)
        FreeF m k' -> [FreeF m (k' >=> k)]

data AltF f a = Pure a | forall c. FreeF (f c) (c -> Alt f a)
deriving instance Functor (AltF f)
instance Applicative (AltF f) where
    pure = Pure
    (<*>) = ap
instance Monad (AltF f) where
    Pure x >>= k = k x
    FreeF m k1 >>= k2 = FreeF m (k1 >=> Alt . pure . k2)

instance (forall x. Show (f x)) => Show (AltF f a) where
    show Pure{} = "<Pure>"
    show (FreeF m _) = "<FreeF (" ++ show m ++ ") k>"

-- instance OrdF f => OrdF (AltF f) where
--     compareF Pure{} Pure{} = EQ
--     compareF Pure{} _ = LT
--     compareF _ Pure{} = GT
--     compareF (FreeF x k1) (FreeF y k2) = compareF x y

-- showAp :: (forall x. Show (f x)) => Ap f a -> String
-- showAp Pure{} = "Pure"
-- showAp (Ap x xs) = "(Ap (" ++ show x ++ ") (" ++ showAp xs ++ "))"

newtype G f g = G { lookupG :: forall a. f a -> Alt (Match + g) a }

class OrdF f where
    compareF :: f a -> f b -> Ordering

data SomeF f where
    SomeF :: f a -> SomeF f

deriving instance (forall x. Show (f x)) => Show (SomeF f)
instance OrdF f => Eq (SomeF f) where
    SomeF x == SomeF y = compareF x y == EQ
instance OrdF f => Ord (SomeF f) where
    compare (SomeF x) (SomeF y) = compareF x y

class EqF f where
    eqF :: f a -> f b -> Maybe (a :~: b)
instance (EqF f, EqF g) => EqF (f + g) where
    eqF (L x) (L y) = eqF x y
    eqF (R x) (R y) = eqF x y
    eqF _ _ = Nothing

data End a deriving (Show)
instance EqF End where
    eqF x _ = case x of
instance OrdF End where
    compareF x _ = case x of

infixr +
infixr <||>

(<||>) :: G f h -> G g h -> G (f + g) h
G f <||> G g = G $ \case
    L y -> f y
    R y -> g y

type Gram f = G f f

end :: G End g
end = G (\case)

-- optimization idea: infer follow restrictions from grammar definition to prune branches earlier

-- naiveDFS :: forall f g a. g < f => Gram f -> g a -> String -> [(a, String)]
-- naiveDFS (G g) nt0 xs0 = (`go` xs0) =<< alternatives (g (inj nt0)) where
--     go :: forall b. Ap (Match + f) b -> String -> [(b, String)] 
--     go (Pure x) xs = [(x, xs)]
--     go (Ap (L (Match c)) next) xs
--      | c':xs' <- xs, c == c' = map (\(f, xs'') -> (f (), xs'')) (go next xs')
--      | otherwise = []
--     go (Ap (R nt) next) xs = do
--         next1 <- alternatives (g nt)
--         (x,xs') <- go next1 xs
--         (f,xs'') <- go next xs'
--         pure (f x, xs'')

data Cursor f = forall a. Cursor (f a) !Int (AltF (Match + f) a)
-- instance OrdF f => Eq (Cursor f) where
--     Cursor x1 x2 x3 == Cursor y1 y2 y3 = compareF x1 y1 == EQ && x2 == y2
-- instance OrdF f => Ord (Cursor f) where
--     compare (Cursor x1 x2 x3) (Cursor y1 y2 y3) = compareF x1 y1 <> compare x2 y2

instance (forall x. Show (f x)) => Show (Cursor f) where
    show (Cursor x y z) = "(Cursor (" ++ show x ++ ") (" ++ show y ++ ") (" ++ show z ++ "))"

newtype MyMap f = MyMap (Map (SomeF f, Int) (Any -> [Cursor f]))
instance (forall x. Show (f x), Show (SomeF f)) => Show (MyMap f) where
    show (MyMap m) = "(MyMap " ++ show (map (second ($ undefined)) $ Map.toList m) ++ ")"

myEmpty :: MyMap f
myEmpty = MyMap Map.empty

myInsert :: OrdF f => f a -> Int -> (a -> [Cursor f]) -> MyMap f -> MyMap f
myInsert nt i f (MyMap m) = MyMap (Map.insertWith (\g h x -> g x ++ h x) (SomeF nt, i) (unsafeCoerce f) m)

myLookup :: OrdF f => f a -> Int -> a -> MyMap f -> [Cursor f]
myLookup nt i x (MyMap m) =
    case Map.lookup (SomeF nt, i) m of
        Just f -> unsafeCoerce f x
        Nothing -> []

data PState f = PState !Int !(MyMap f) ![Cursor f]
deriving instance (forall x. Show (f x), Show (SomeF f)) => Show (PState f)

-- FIXME: there are still problems with epsilon productions.

step :: (OrdF f) => Gram f -> Char -> PState f -> PState f
step (G g) c (PState i wa0 alts0) =
    uncurry (PState (i + 1)) $ bimap fst concat (List.mapAccumL (stepF g c i) (wa0, Set.empty) alts0)

stepF :: OrdF f => (forall x. f x -> Alt (Match + f) x) -> Char -> Int -> (MyMap f, Set (SomeF f)) -> Cursor f -> ((MyMap f, Set (SomeF f)), [Cursor f])
--  | traceShow ("stepF", cursor) False = undefined
stepF g c i = go where
    go (wa,done) (Cursor nt j alt) =
        case alt of
            Pure x ->
                second concat $ List.mapAccumL go (wa,done) $ myLookup nt j x wa
            FreeF (L (Match c')) k
                | c == c' -> ((wa, done), Cursor nt j <$> alternatives (k ()))
                | otherwise -> ((wa, done), [])
            FreeF (R nt') k ->
                let wa' = myInsert nt' i (\x -> Cursor nt j <$> alternatives (k x)) wa in
                second concat $ List.mapAccumL go (wa', Set.insert (SomeF nt') done)
                    [Cursor nt' i alts | Set.notMember (SomeF nt') done, alts <- alternatives $ g nt']

successes :: (EqF f, OrdF f) => PState f -> f a -> [a]
successes (PState _ wa cs0) nt0 = go cs0 where
    go [] = []
    go (Cursor nt i (Pure x) : cs) =
        case eqF nt0 nt of
            Just Refl | i == 0 -> x : go cs
            _ -> go (myLookup nt i x wa ++ cs)
    go (_ : cs) = go cs

traceShowIt :: Show b => b -> b
traceShowIt x = x -- traceShow x x

parse :: (forall x. Show (f x), EqF f, OrdF f, g < f) => Gram f -> g a -> String -> [a]
parse (G g) nt [] = successes (PState 0 myEmpty [Cursor (inj nt) 0 alts | alts <- alternatives $ g (inj nt)]) (inj nt)
parse g nt (c:cs) = successes (foldl' (\s c' -> traceShowIt $ step g c' s) (traceShowIt (initialPState g (inj nt) c)) cs) (inj nt)
    where
        initialPState (G g) nt c = uncurry (PState 1) $ bimap fst concat $ 
            List.mapAccumL (stepF g c 0) (myEmpty, Set.singleton (SomeF nt))
                [Cursor nt 0 aps | aps <- alternatives $ g nt]


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

module Gigaparsec.Core (parse, match, send, G(G), Gram, (<||>), type (+), End, end, Alt, type (<)(..), OrdF(..), EqF(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor.Compose ( Compose(Compose) )
import Control.Applicative.Free ( Ap(..) )
import Data.Proxy ( Proxy(..) )
import Data.Type.Equality
import qualified Data.List as List
import Data.Bifunctor (second)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import Data.List (foldl')
import Control.Applicative (Alternative)

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

send :: f < g => f a -> Alt g a
send x = Alt [Ap (inj x) (Pure id)]

match :: Match < f => Char -> Alt f ()
match c = send (Match c)

-- Free alternative, see https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html
-- But this one also satisfies right distributivity: f <*> (x <|> y) = (f <*> x) <|> (f <*> y)

newtype Alt f a = Alt { alternatives :: [Ap f a] }
    deriving (Functor, Applicative, Alternative) via Compose [] (Ap f)

showAp :: (forall x. Show (f x)) => Ap f a -> String
showAp Pure{} = "Pure"
showAp (Ap x xs) = "(Ap (" ++ show x ++ ") (" ++ showAp xs ++ "))"

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

-- optimization idea: infer follow restrictions from grammar definition
-- to prune branches earlier

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

data Cursor f = forall a. Cursor (f a) !Int (Ap (Match + f) a)
instance (forall x. Show (f x)) => Show (Cursor f) where
    show (Cursor x y z) = "(Cursor (" ++ show x ++ ") (" ++ show y ++ ") (" ++ showAp z ++ "))"

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

myExists :: OrdF f => f a -> Int -> f b -> Int -> MyMap f -> Bool
myExists nt' i nt j (MyMap m) =
    case Map.lookup (SomeF nt', i) m of
        Just f -> any (\(Cursor nt'' j' _) -> compareF nt nt'' == EQ && j' == j) (f undefined)
        Nothing -> False

data PState f = PState !Int !(MyMap f) ![Cursor f]
deriving instance (forall x. Show (f x), Show (SomeF f)) => Show (PState f)

initialPState :: Gram f -> f a -> PState f
initialPState (G g) nt = PState 0 myEmpty [Cursor nt 0 aps | aps <- alternatives $ g nt]

step :: forall f. (OrdF f) => Gram f -> Char -> PState f -> PState f
step (G g) c (PState i wa0 aps) = uncurry (PState (i + 1)) $ second concat (List.mapAccumL stepAp wa0 aps) where
    stepAp :: MyMap f -> Cursor f -> (MyMap f, [Cursor f])
    -- stepAp _ cursor | traceShow ("stepAp", cursor) False = undefined
    stepAp wa (Cursor nt j ap) =
        case ap of
            Pure x ->
                -- This might loop infinitely if a nonterminal in the grammar has an empty production
                second concat $ List.mapAccumL stepAp wa $ {-filter (\(Cursor nt' j' ap') -> j /= j' || compareF nt' nt /= EQ || not (isPure ap')) -} myLookup nt j x wa
            Ap (L (Match c')) next
                | c == c' -> (wa, [Cursor nt j (fmap ($ ()) next)])
                | otherwise -> (wa, [])
            Ap (R nt') next
                -- this feels like a hack, it should also keep track of which alternative of nt we are in
                | not (myExists nt' i nt j wa) ->
                    let
                        wa' = myInsert nt' i (\x -> [Cursor nt j (($ unsafeCoerce x) <$> next)]) wa
                    in
                        second concat $ List.mapAccumL stepAp wa' [Cursor nt' i aps' | aps' <- alternatives $ g nt']
                | otherwise -> (wa, [])

--     isPure :: Ap f a -> Bool
--     isPure Pure{} = True
--     isPure _ = False

successes :: (EqF f, OrdF f) => PState f -> f a -> [a]
successes (PState _ wa cs0) nt0 = go cs0 where
    go [] = []
    go (Cursor nt i (Pure x) : cs) =
        case eqF nt0 nt of
            Just Refl | i == 0 -> x : go cs
            _ -> go (myLookup nt i x wa ++ cs)
    go (_ : cs) = go cs

parse :: (EqF f, OrdF f) => Gram f -> f a -> String -> [a]
parse g nt xs = successes (foldl' (flip (step g)) (initialPState g nt) xs) nt
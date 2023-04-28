
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

module Gigaparsec.Core where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Control.Applicative ( asum, Alternative((<|>)) )
import Data.Functor.Compose ( Compose(Compose) )
import Control.Applicative.Free ( hoistAp, Ap(..) )
import Data.Proxy ( Proxy(..) )
import Data.Char (intToDigit)

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

hoistAlt :: (forall x. f x -> g x) -> Alt f a -> Alt g a
hoistAlt f (Alt xs) = Alt (fmap (hoistAp f) xs)

data Pa f a b where
    Erup :: Pa f a a
    Pa :: Pa f a b -> f c -> Pa f (c -> a) b
deriving instance (forall c. Show (f c)) => Show (Pa f a b)

comparePa :: OrdF f => Pa f a b -> Pa f c d -> Ordering
comparePa Erup Erup = EQ
comparePa Erup _ = LT
comparePa _  Erup = GT
comparePa (Pa xs x) (Pa ys y) = compareF x y <> comparePa xs ys

showAp :: (forall x. Show (f x)) => Ap f a -> String
showAp Pure{} = "Pure"
showAp (Ap x xs) = "(Ap (" ++ show x ++ ") (" ++ showAp xs ++ "))"

compareAp :: OrdF f => Ap f a -> Ap f b -> Ordering
compareAp Pure{} Pure{} = EQ
compareAp Pure{} _ = LT
compareAp _  Pure{} = GT
compareAp (Ap x xs) (Ap y ys) = compareF x y <> compareAp xs ys

newtype G f g = G { lookupG :: forall a. f a -> Alt (Match + g) a }

data Slot f a = forall b. 
    Slot
        !(f a) -- ^ The name of the current nonterminal
        (Pa (Match + f) b a) -- ^ The processed dependencies
        (Ap (Match + f) b) -- ^ The actions that still need to be done

instance (forall x. (Show (f x))) => Show (Slot f a) where
    show (Slot x y z) = "(Slot (" ++ show x ++ ") (" ++ show y ++ ") (" ++ showAp z ++ "))"

data Descriptor f = forall a.
    Descriptor
        !(Slot f a)
        !Int -- ^ The left extent
        !Int -- ^ The pivot
        String -- ^ The remainder of the input (to the right of the pivot) 
deriving instance (forall x. (Show (f x))) => Show (Descriptor f)
instance (OrdF f) => Eq (Descriptor f) where
    x == y = compare x y == EQ
instance (OrdF f) => Ord (Descriptor f) where
    compare (Descriptor x1 x2 x3 _) (Descriptor y1 y2 y3 _) = compareSlot x1 y1 <> compare x2 y2 <> compare x3 y3

class OrdF f where
    compareF :: f a -> f b -> Ordering

data SomeF f where
    SomeF :: f a -> SomeF f
instance OrdF f => Eq (SomeF f) where
    SomeF x == SomeF y = compareF x y == EQ
instance OrdF f => Ord (SomeF f) where
    compare (SomeF x) (SomeF y) = compareF x y

compareSlot :: OrdF f => Slot f a -> Slot f b -> Ordering
compareSlot (Slot x1 x2 x3) (Slot y1 y2 y3) = compareF x1 y1 <> comparePa x2 y2 <> compareAp x3 y3

compareDescriptor :: OrdF f => Descriptor f -> Descriptor f -> Ordering
compareDescriptor (Descriptor x1 x2 x3 _) (Descriptor y1 y2 y3 _) = compareSlot x1 y1 <> compare x2 y2 <> compare x3 y3

initialDescriptor :: f a -> String -> Ap (Match + f) a -> Descriptor f
initialDescriptor nt xs act = Descriptor (Slot nt Erup act) 0 0 xs

data EPN n = forall a.
    EPN
        !(Slot n a)
        !Int -- ^ left extent
        !Int -- ^ previous pivot
        !Int -- ^ pivot

newtype WaitForAscend f = WA (Map (SomeF f, Int) [Int -> String -> Descriptor f])

emptyWA :: WaitForAscend n
emptyWA = WA Map.empty

lookupWA :: forall a f. OrdF f => WaitForAscend f -> f a -> Int -> [Int -> String -> Descriptor f]
lookupWA (WA m) nt k = fromMaybe [] (m Map.!? (SomeF nt, k))

insertWA :: OrdF f => f a -> Int -> (Int -> String -> Descriptor f) -> WaitForAscend f -> WaitForAscend f
insertWA nt k f (WA m) = WA (Map.insertWith (++) (SomeF nt, k) [f] m)

newtype WaitForDescend f = WD (Map (SomeF f, Int) [(Int, String)])

emptyWD :: WaitForDescend n
emptyWD = WD Map.empty

lookupWD :: forall a f. OrdF f => WaitForDescend f -> f a -> Int -> [(Int, String)]
lookupWD (WD m) nt k = fromMaybe [] (m Map.!? (SomeF nt, k))

insertWD :: OrdF f => f a -> Int -> (Int, String) -> WaitForDescend f -> WaitForDescend f
insertWD nt k x (WD m) = WD (Map.insertWith (++) (SomeF nt, k) [x] m)

-- TODO: also generate a set of EPNs
--
-- consider discarding the Pa data structure and just store a list of results in the descriptors (that might remove the need for EPNs?)
-- when comparing the 'Pure' case we must always assume that they are different and just append the two input lists to form the result.
parse :: forall a f g. (OrdF f, g < f) => Gram f -> g a -> String -> Set (Descriptor f)
parse g z xs0 = go Set.empty emptyWA emptyWD (map (initialDescriptor (inj z) xs0) (alternatives (lookupG g (inj z)))) where
    go :: Set (Descriptor f) -> WaitForAscend f -> WaitForDescend f -> [Descriptor f] -> Set (Descriptor f)

    -- If we've already processed this descriptor then we can skip it
    go u wa wd (d : rs) | d `Set.member` u = go u wa wd rs

    -- If we're currently 'Match'ing a character and that character appears in the input text then we can continue
    go u wa wd (d@(Descriptor (Slot x ds (Ap (L (Match c)) r)) l k xs) : rs)
        | c' : xs' <- xs, c == c' = go (Set.insert d u) wa wd (Descriptor (Slot x (Pa ds (L (Match c))) r) l (k + 1) xs' : rs)
        -- otherwise we skip this descriptor
        | otherwise = go u wa wd rs

    -- If we're descending into a nonterminal then we check if something was already waiting for us to descend.
    go u wa wd (d@(Descriptor (Slot x ds (Ap (R nt) next)) l k xs) : rs)
        = go (Set.insert d u) (insertWA nt k (Descriptor (Slot x (Pa ds (R nt)) next) l) wa) wd $
            case lookupWD wd nt k of
                -- If nothing was waiting for this then we start descending by adding initial descriptors the nonterminal we are descending into.
                [] -> [ Descriptor (Slot nt Erup acts) k k xs | acts <- alternatives (lookupG g nt) ] ++ rs
                -- If something was waiting for us then we can take over where they left off.
                _ -> [ Descriptor (Slot x (Pa ds (R nt)) next) l r xs' | (r, xs') <- lookupWD wd nt k ] ++ rs

    -- If we have reached the end of a descriptor then we ascend.
    go u wa wd (d@(Descriptor (Slot x _ (Pure _)) k r xs) : rs)
        = go (Set.insert d u) wa (insertWD x k (r, xs) wd)
            ([ f r xs | f <- lookupWA wa x k ] ++ rs)

    -- If we have no more work then parsing is done!
    go u _ _ [] = u

-- TODO: reimplement a correct decoding function
-- decode :: forall a f. Set (Descriptor f) -> f a -> Int -> Int -> [a]
-- decode ds0 = lookupM where
--     m :: Map (n, Int, Int) [Any]
--     m = Map.fromListWith (++)
--         [ ((x, l, r), map unsafeCoerce (go ds [a]))
--         | Descriptor (Descriptor (Slot nt _ _ ds (Pure a)) l r _) <- Set.toList ds0
--         ]
-- 
--     lookupM :: forall c. f c -> Int -> Int -> [c]
--     lookupM nt l r = maybe [] (map unsafeCoerce) (m Map.!? (n, l, r)) 
-- 
--     go :: forall b c. Deps f b c -> [c] -> [b]
--     go Self x = x
--     go (Dep n l r xs) fs = go xs $ fs <*> lookupM n l r

data End a deriving (Show)
instance OrdF End where
    compareF x _ = case x of

data Number a where
    Number :: Number Int
deriving instance Show (Number a)
instance OrdF Number where
    compareF Number Number = EQ

number :: Number < f => Alt f Int
number = send Number

data Digit a where
    Digit :: Digit Int
deriving instance Show (Digit a)
instance OrdF Digit where
    compareF Digit Digit = EQ

digit :: Digit < f => Alt f Int
digit = send Digit

-- ergonomics idea: use overloaded labels or template haskell to avoid boilerplate

data Expr a where
    Expr :: Expr Int
deriving instance Show (Expr a)

instance OrdF Expr where
    compareF Expr Expr = EQ

expr :: Expr < f => Alt f Int
expr = send Expr

-- TODO: higher order nonterminals, e.g.:
data Many p a where
    Many :: p a -> Many m [a]

-- TODO: This would require using a free monad(plus) rather than just a free alternative:
data ReplicateM p a where
    ReplicateM :: Int -> p a -> ReplicateM p [a]

infixr +
infixr <||>

(<||>) :: G f h -> G g h -> G (f + g) h
G f <||> G g = G $ \case
    L y -> f y
    R y -> g y

type Gram f = G f f

end :: G End a
end = G (\case)

-- optimization idea: infer follow restrictions from grammar definition

gram :: Gram (Expr + Number + Digit + End)
gram = G (\Expr -> (+) <$> expr <* match '+' <*> expr <|> number)
  <||> G (\Number -> (\x y -> 10 * x + y) <$> number <*> digit <|> digit)
  <||> G (\Digit -> asum [x <$ match (intToDigit x) | x <- [0..9]])
  <||> end

ex1 :: Set (Descriptor (Expr + Number + Digit + End))
ex1 = parse gram Expr "123+456"

-- >>> ex1
-- fromList [Descriptor (Descriptor (Slot (L Expr) (Erup) ((Ap (R (L Expr)) ((Ap (L (Match '+')) ((Ap (R (L Expr)) (Pure)))))))) 0 0 "123+456"),Descriptor (Descriptor (Slot (L Expr) (Erup) ((Ap (R (L Expr)) ((Ap (L (Match '+')) ((Ap (R (L Expr)) (Pure)))))))) 4 4 "456"),Descriptor (Descriptor (Slot (L Expr) (Erup) ((Ap (R (R (L Number))) (Pure)))) 0 0 "123+456"),Descriptor (Descriptor (Slot (L Expr) (Erup) ((Ap (R (R (L Number))) (Pure)))) 4 4 "456"),Descriptor (Descriptor (Slot (L Expr) (Pa (Pa Erup (R (L Expr))) (L (Match '+'))) ((Ap (R (L Expr)) (Pure)))) 0 4 "456"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (L Expr))) ((Ap (L (Match '+')) ((Ap (R (L Expr)) (Pure)))))) 0 3 "+456"),Descriptor (Descriptor (Slot (L Expr) (Pa (Pa (Pa Erup (R (L Expr))) (L (Match '+'))) (R (L Expr))) (Pure)) 0 5 "56"),Descriptor (Descriptor (Slot (L Expr) (Pa (Pa (Pa Erup (R (L Expr))) (L (Match '+'))) (R (L Expr))) (Pure)) 0 6 "6"),Descriptor (Descriptor (Slot (L Expr) (Pa (Pa (Pa Erup (R (L Expr))) (L (Match '+'))) (R (L Expr))) (Pure)) 0 7 ""),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 0 1 "23+456"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 0 2 "3+456"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 0 3 "+456"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 4 5 "56"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 4 6 "6"),Descriptor (Descriptor (Slot (L Expr) (Pa Erup (R (R (L Number)))) (Pure)) 4 7 ""),Descriptor (Descriptor (Slot (R (L Number)) (Erup) ((Ap (R (R (L Number))) ((Ap (R (R (R (L Digit)))) (Pure)))))) 0 0 "123+456"),Descriptor (Descriptor (Slot (R (L Number)) (Erup) ((Ap (R (R (L Number))) ((Ap (R (R (R (L Digit)))) (Pure)))))) 4 4 "456"),Descriptor (Descriptor (Slot (R (L Number)) (Erup) ((Ap (R (R (R (L Digit)))) (Pure)))) 0 0 "123+456"),Descriptor (Descriptor (Slot (R (L Number)) (Erup) ((Ap (R (R (R (L Digit)))) (Pure)))) 4 4 "456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 0 1 "23+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 0 2 "3+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 0 3 "+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 4 5 "56"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 4 6 "6"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (L Number)))) ((Ap (R (R (R (L Digit)))) (Pure)))) 4 7 ""),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (R (L Digit))))) (Pure)) 0 1 "23+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa Erup (R (R (R (L Digit))))) (Pure)) 4 5 "56"),Descriptor (Descriptor (Slot (R (L Number)) (Pa (Pa Erup (R (R (L Number)))) (R (R (R (L Digit))))) (Pure)) 0 2 "3+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa (Pa Erup (R (R (L Number)))) (R (R (R (L Digit))))) (Pure)) 0 3 "+456"),Descriptor (Descriptor (Slot (R (L Number)) (Pa (Pa Erup (R (R (L Number)))) (R (R (R (L Digit))))) (Pure)) 4 6 "6"),Descriptor (Descriptor (Slot (R (L Number)) (Pa (Pa Erup (R (R (L Number)))) (R (R (R (L Digit))))) (Pure)) 4 7 ""),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '1')) (Pure)))) 0 0 "123+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '2')) (Pure)))) 1 1 "23+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '3')) (Pure)))) 2 2 "3+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '4')) (Pure)))) 4 4 "456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '5')) (Pure)))) 5 5 "56"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Erup) ((Ap (L (Match '6')) (Pure)))) 6 6 "6"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '1'))) (Pure)) 0 1 "23+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '2'))) (Pure)) 1 2 "3+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '3'))) (Pure)) 2 3 "+456"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '4'))) (Pure)) 4 5 "56"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '5'))) (Pure)) 5 6 "6"),Descriptor (Descriptor (Slot (R (R (L Digit))) (Pa Erup (L (Match '6'))) (Pure)) 6 7 "")]

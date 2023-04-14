{-# LANGUAGE DerivingVia #-}
module Gigaparsec.Common where
import Data.Kind
import Data.Functor.Compose
import Control.Applicative
import Data.Map (Map)
import GHC.Exts (Any)
import qualified Data.Map as Map
import Unsafe.Coerce

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
newtype Alt m f a = Alt { getAlts :: [AltF m f a] }
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
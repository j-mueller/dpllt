{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module DPLLT.Theory where

import           Control.Applicative
import           Data.Foldable
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Data.Tuple
import           Data.String
import           GHC.Generics

import Prelude hiding (concat)

data Literal a =
  Positive a
  | Negative a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

negate :: Literal a -> Literal a
negate (Positive a) = Negative a
negate (Negative a) = Positive a

atom :: Literal a -> a
atom (Positive a) = a
atom (Negative a) = a

isPositive :: Literal a -> Bool
isPositive (Positive a) = True
isPositive _ = False

-- | A theory T is a set (the type t) of ground literals such that the
--   satisfiability of conjunctions of t's is decidable
--
--   If a list (conjunction) of t's is satisfiable then any sub-list should
--   also be satisfiable
--
--   satisfiable [] = True
--   for all t: satisfiable [Positive t, Negative t] = False
class Theory t where
  satisfiable :: [Literal t] -> Bool

instance (Theory a, Theory b) => Theory (Either a b) where
  satisfiable tls = satisfiable lefts && satisfiable rights where
    lefts  = fold $ fmap (traverse $ either pure (const empty)) tls
    rights = fold $ fmap (traverse $ either (const empty) pure) tls

-- | Theory based on equality of atoms
newtype EqTheory a = EqTheory { unEqTheory :: a }
  deriving (Eq, Ord, Show)

instance (Eq a, Ord a) => Theory (EqTheory a) where
  satisfiable eqs = S.null $ S.intersection (S.map atom l) (S.map atom r) where
    s = S.fromList $ fmap (fmap unEqTheory) eqs
    (l, r) = S.partition isPositive s

-- | A 'Formula (EqTheory String)' gives you basic boolean logic where the
-- | strings are variables.
-- |
-- | This is useful if you want to test some formulas without writing up more
-- | complicated conditions.
instance IsString (EqTheory String) where
  fromString = EqTheory

newtype IndexedTheory i a = IndexedTheory { unIndex :: (i, a) }
  deriving (Eq, Ord, Show)

-- | Partition the set of literals by its index and check that each partition
-- | is satisfiable
instance (Ord a, Theory a, Eq i, Ord i) => Theory (IndexedTheory i a) where
  satisfiable ts = inner ts where
    inner = null . filter not . fmap (satisfiable . S.toList . snd) . group . fmap project
    -- project :: Literal (IndexedTheory i a) -> (i, S.Set (Literal a))
    project = ((,) <$> fst . atom <*> S.singleton . fmap snd) . fmap unIndex
    -- group :: [(i, S.Set (Literal a))] -> [(i, S.Set (Literal a))]
    group = M.toList . M.fromListWith S.union

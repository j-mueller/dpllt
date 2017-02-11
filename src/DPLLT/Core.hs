-- Implementation of the DPLL algorithm with "theories"
--
-- The implementation is based on
-- R. Nieuwenhuis, A. Oliveras and C. Tinelli "Abstract DPLL and Abstract DPLL
-- Modulo Theories" in LPAR 2004 pp. 36-50
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
module DPLLT.Core(
  -- * Boolean formulas
  Formula(..),
  ltl,
  xor,
  implies,
  disjSubFormulas,
  -- * Entailment / satisfiability checking
  entails,
  solvable,
  tautology
) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Logic
import           Data.Either         (lefts)
import           Data.Foldable
import           Data.List           (transpose)
import qualified Data.Set            as S
import           GHC.Generics
import           Prelude             hiding (negate)

import           DPLLT.Theory

data Formula a =
  And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Prim (Literal a)
  deriving (Eq, Ord, Show, Generic)

-- | Turn an atom into a positive literal
ltl :: a -> Formula a
ltl = Prim . Positive

-- | Implication, a -> b
implies :: Formula a -> Formula a -> Formula a
implies a b = (Not a) `Or` b

-- | Exclusive OR
xor :: Formula a -> Formula a -> Formula a
xor a b = (a `Or` b) `And` (Not $ a `And` b)

type Clause a = S.Set (Literal a)

newtype CNF a = CNF { unCNF :: S.Set (Clause a) }
  deriving (Eq, Ord, Show)

singleton :: Literal a -> CNF a
singleton = CNF . S.singleton . S.singleton

emptyCNF :: CNF a
emptyCNF = CNF S.empty

plus :: Ord a => CNF a -> CNF a -> CNF a
plus (CNF l) (CNF r) = CNF $ S.union l r

-- Turn a formula into conjunctive normal form
toCNF :: Ord a => Formula a -> CNF a
toCNF f = case f of
    And l r -> toCNF l `plus` (toCNF r)
    Or l r ->
      let l' = S.toList $ unCNF $ toCNF l in
      let r' = S.toList $ unCNF $ toCNF r in
      CNF $ S.fromList $ fmap (foldl S.union S.empty) $ transpose [l', r']
    Not f' -> case f' of
      Prim a -> singleton $ negate a
      Not a  -> toCNF a
      Or l r -> toCNF $ And (Not l) (Not r)
      And l r -> toCNF $ Or (Not l) (Not r)
    Prim a -> singleton  a

newtype DNF a = DNF { unDNF :: S.Set (Clause a) }
  deriving (Eq, Ord, Show)

-- | Performs one step of the CNF conversion;
conjSubFormulas :: Ord a => Formula a -> Maybe [Formula a]
conjSubFormulas f = case f of
    And l r -> Just [l, r]
    Or l r ->
      let l' = maybe [l] id $ conjSubFormulas l in
      let r' = maybe [r] id $ conjSubFormulas r in
      let interm = transpose [l', r'] in
      let inner xs = case xs of [x, y] -> x `Or` y; [x] -> x in
      let result = fmap inner interm in
      if (result == [l `Or` r])
      then Nothing
      else Just result
    Not f' -> case f' of
      Prim a -> Nothing
      Not a  -> conjSubFormulas a
      Or l r -> Just [Not l, Not r]
      And l r -> conjSubFormulas $ Or (Not l) (Not r)
    Prim a -> Nothing

-- | Performs one step of the DNF conversion; returns either a list with
-- | two or more elements, or Nothing
disjSubFormulas :: Ord a => Formula a -> Maybe [Formula a]
disjSubFormulas f = case f of
  Or l r -> Just [l, r]
  Not f' -> case f' of
    Prim a -> Nothing -- cannot simplify further
    Not a -> disjSubFormulas a
    Or l r -> disjSubFormulas (Not l `And` Not r)
    And l r -> Just [Not l, Not r]
  And l r ->
    let l' = maybe [l] id $ disjSubFormulas l in
    let r' = maybe [r] id $ disjSubFormulas r in
    let interm = transpose [l', r'] in
    let inner xs = case xs of [x, y] -> x `And` y; [x] -> x in
    let result = fmap inner interm in
    if (result == [l `And` r])
    then Nothing
    else Just result
  Prim a -> Nothing

getDisjunctions :: Ord a => DNF a -> [Formula a]
getDisjunctions = fmap (conj . fmap Prim . S.toList) . S.toList . unDNF where
  conj (x:xs) = foldl And x xs

newtype TruthAssignment a = TruthAssignment { unTA :: S.Set (Literal a) }
  deriving (Show)

instance (Ord a) => Monoid (TruthAssignment a) where
  mempty = emptyTA
  mappend (TruthAssignment l) (TruthAssignment r) = TruthAssignment $ l `S.union` r

emptyTA :: TruthAssignment a
emptyTA = TruthAssignment S.empty

addInferred :: Ord a => Literal a -> [Either (Literal a) (TruthAssignment a)] -> [Either (Literal a) (TruthAssignment a)]
addInferred l [] = [Right $ TruthAssignment $ S.singleton l]
addInferred l (x:xs) = case x of
  Left l' -> (Right $ TruthAssignment $ S.singleton l) : (Left l') : xs
  Right (TruthAssignment t) -> (Right $ TruthAssignment $ S.insert l t):xs

addDecision :: Ord a => Literal a -> [Either (Literal a) (TruthAssignment a)] -> [Either (Literal a) (TruthAssignment a)]
addDecision ltl = (:) (Left ltl)

getAll :: Ord a => [Either (Literal a) (TruthAssignment a)] -> TruthAssignment a
getAll = foldMap (either (TruthAssignment . S.singleton) id)

getDecisionLiterals :: Ord a => [Either (Literal a) (TruthAssignment a)] -> [Literal a]
getDecisionLiterals = lefts

data Status = TrueStatus | FalseStatus | Undefined
  deriving (Eq, Ord, Show)

statusIn :: Ord a => TruthAssignment a -> Literal a -> Status
statusIn ta l = case (S.member l $ unTA ta, S.member (negate l) $ unTA ta) of
  (True, _) -> TrueStatus
  (_, True) -> FalseStatus
  _ -> Undefined

statusIn' :: Ord a => TruthAssignment a -> Clause a -> Status
statusIn' ta c =
  let someTrue = not $ S.null $ S.intersection (unTA ta) c in
  let allFalse = all ((==) FalseStatus . statusIn ta) $ S.toList c in
  case (someTrue, allFalse) of
    (True, _) -> TrueStatus
    (_, True) -> FalseStatus
    _ -> Undefined

trueIn :: (Ord a) => TruthAssignment a -> CNF a -> Bool
trueIn ta = all ((==) TrueStatus . statusIn' ta) . S.toList . unCNF

falseIn :: (Ord a) => TruthAssignment a -> CNF a -> Bool
falseIn ta = not . trueIn ta

undefinedIn :: (Ord a) => TruthAssignment a -> Literal a -> Bool
undefinedIn ta = (==) Undefined . statusIn ta

-- | Current state of the search
-- |
-- | The first element is a set of annotated literals. [[Left]]s are decision
-- | literals and [[Right]]s are (sets of) inferred literals.
-- |
-- | The second element is set of clauses (the CNF of some formula). This is the
-- | goal we are trying to solve
type State a = ([Either (Literal a) (TruthAssignment a)], S.Set (Clause a))

-- | Pick one of the goal clauses
pick :: (Ord a, MonadPlus m) => S.Set a -> m (a, S.Set a)
pick s = do
  a <- msum $ fmap return $ S.toList s
  return (a, S.delete a s)

unitProp :: (Ord a, MonadPlus m) => State a -> m (State a)
unitProp (m, clauses) = do
  (c, cs) <- pick clauses
  (l, ls) <- pick c
  guard (statusIn' (getAll m) ls == FalseStatus)
  guard (statusIn (getAll m) l == Undefined)
  return (addInferred l m, clauses)

decide :: (Functor m, Ord a, MonadPlus m) => State a -> m (State a)
decide (m, clauses) = do
  (c, cs) <- pick clauses
  lit <- fmap fst $ pick c
  l' <- msum $ [return lit, return $ negate lit]
  guard (statusIn (getAll m) l' == Undefined)
  return (addDecision l' m, clauses)

-- | Check if there is a conflict in the current state, that is if there is
--   a clause F that is false in M
getConflict :: (Ord a, MonadPlus m) => State a -> m (Clause a)
getConflict (m, clauses) = do
  let ta = getAll m
  msum $ fmap return $ S.toList $ S.filter ((==) FalseStatus . statusIn' ta) clauses

hasConflict :: (Ord a) => State a -> Bool
hasConflict = not . null . observeAll . getConflict

dpll :: (Theory a, Ord a, Functor m, MonadLogic m) => CNF a -> m (TruthAssignment a)
dpll = fmap (getAll . fst) . dpll' . ([],) . unCNF

-- Simple DPLL implementation that uses only two rules
dpll' :: (Ord a, Theory a, Functor m, MonadLogic m) => State a -> m (State a)
dpll' state@(m, clauses) = guard (not $ hasConflict state) >>
  let m' = getAll m in
  if (trueIn m' (CNF clauses))
  then (guard $ satisfiable $ S.toList $ unTA m') >> return (m, clauses)
  else msum [unitProp state, decide state] >>- dpll'

solve :: (Theory a, Ord a) => Formula a -> [TruthAssignment a]
solve = observeAll . dpll . toCNF

solvable :: (Theory a, Ord a) => Formula a -> Bool
solvable = not . null . solve

-- | A tautology is a formula that is always true.
-- | For example, `A ⋁ ¬A` is a tautology
tautology :: (Theory a, Ord a) => Formula a -> Bool
tautology = not . solvable . Not

-- | Check if a conjunctive list of formulas entails another conjunctive
--   list of formulas
--   For example,
--
-- @
-- [A, B] `entails` [A]
-- [A ∧ B] `entails` [A v B]
-- [...] `entails` []
-- @
entails :: (Theory a, Ord a) => [Formula a] -> [Formula a] -> Bool
entails _      []     = True
entails []     (x:xs) = tautology $ foldl And x xs
entails (x:xs) (y:ys) = tautology $ (foldl And x xs) `implies` (foldl And y ys)

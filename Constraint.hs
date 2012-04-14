module Constraint (Domain,
                   universe,
                   nothing,
                   subsumes,
                   supersumes,
                   contains,
                   reduce,
                   expand,
                   reduces,
                   expands,
                   FiniteDomain,
                   elems,
                   ConstraintSystem,
                   relate,
                   restrict,
                   encompass,
                   SolvableConstraints,
                   determinate,
                   solvable,
                   unsolvable,
                   solution) where

import Data.Set (Set)
import qualified Data.Set as Set

class Domain d where
  universe :: d a
  nothing :: d a
  single :: a -> d a 
  enumerated :: [a] -> d a
  subsumes :: d a -> d a -> Bool
  supersumes :: d a -> d a -> Bool
  contains :: d a -> a -> Bool
  reduce :: d a -> d a -> d a
  expand :: d a -> d a -> d a
  reduces :: [d a] -> d a
  reduces t = foldl reduce universe t
  expands :: [d a] -> d a
  expands t = foldl expand nothing t
  
class (Domain d) => FiniteDomain d where
  elems :: d a -> [a]
  
class Constraint c where
  satisfies :: (Domain d) => [d a] -> c (d a) -> Bool
  weak :: (Domain d) => [d a] -> c (d a) -> Bool
  decompose :: (Domain d, Ix i) => 
               c (d a) -> [(i,d a)] -> Maybe [([i],c (d a))]


class ConstraintSystem s where
  constrain :: (Ix i, Domain d, Constraint c)
               => s (d a) -> [i] -> c (d a) -> s (d a)
  
class (ConstraintSystem c) => SolvableConstraints c where
  determinate :: (Domain d) => c (d a) -> Bool
  solvable :: (Domain d) => c (d a) -> Maybe Bool
  unsolvable :: (Domain d) => c (d a) -> Maybe Bool
  solution :: (Domain d) => c (d a) -> Maybe (c (d a))
  
data (FiniteDomain d, Ix i) => FSolver (d a) = 
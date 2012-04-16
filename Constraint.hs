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
  
data Satisfaction = Unsatisfiable | Indeterminate | Weak | Strong 

(|||) :: Satisfaction -> Satisfaction -> Satisfaction
Unsatisfiable ||| _ = Unsatisfiable
_ ||| Unsatisfiable = Unsatisfiable
Indeterminate ||| _ = Indeterminate
_ ||| Indeterminate = Indeterminate
Weak ||| _ = Weak
_ ||| Weak = Weak
Strong ||| Strong = Strong

class Constraint c where
  satisfies :: (Domain d) => [d a] -> c (d a) -> Satisfaction
  decompose :: (Domain d) => 
               c (d a) -> [(i,d a)] -> Maybe [([(i,d a)],c (d a))]
  (+++) :: (Domain d) => c (d a) -> c (d a) -> c (d a)

class ConstraintSystem s where
  getDomain :: (Domain d) => s i (d a) -> i -> d a
  setDomain :: (Domain d) => s i (d a) -> i -> d a -> s i (d a)
  constrain :: (Domain d, Constraint c)
               => s i (d a) -> [i] -> c (d a) -> s i (d a)
  unconstrain :: (Domain d, Constraint c)
                 => s i (d a) -> [i] -> s i (d a)
  constraints :: (Domain d, Constraint c)
                 => s i (d a) -> [([i], c (d a))]
  satisfied :: (Domain d) => s i (d a) -> Satisfaction
  satisfied s = foldl (|||) Strong $ map sat $ constraints s where
    sat (ix,c) = map (`satisfies` c) $ map (getDomain s) ix
  
class (ConstraintSystem s) => SolvableConstraints s where
  solution :: (Domain d) => s (d a) -> Maybe (s (d a))
  


decomposeConstraints :: (ConstraintSystem s, Domain d)
                        => s (d a) -> s (d a)
decomposeConstraints s = where
  deco :: (ConstraintSystem s, Constraint c, Domain d) 
          => s (d a) -> ([i],c (d a)) -> s (d a)
  deco sys (ix,c) = let decomp = decompose c $ 
                                 zip ix (map (getDomain s) ix) in
                    if isJust decomp then 
  
data (FiniteDomain d, Ix i) => FSolver i (d a) = 
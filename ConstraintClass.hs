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
                   Satisfaction,
                   (<&>),
                   Constraint,
                   satisfies,
                   decompose,
                   (+++),
                   ConstraintSystem,
                   getDomain,
                   setDomain,
                   constrain,
                   unconstrain,
                   constraints,
                   satisfied
--                   SolvableConstraints,
  --                 solution
                  
                  ) where

import Data.Set (Set)
import Maybe
import qualified Data.Set as Set

-- | Instances of Domain embody an unknown within a given domain.
class Domain d where
  -- | a representation of all possible values.
  universe :: d a
  -- | null set of values
  nothing :: d a
  -- | A domain variable with a single possible value.  In other words,
  -- a constant
  single :: a -> d a 
  -- | Return a variable which can take on any value in the list.
  enumerated :: [a] -> d a
  -- | a `subsumes` b == True if every allowed value for b is a value for a
  subsumes :: d a -> d a -> Bool
  -- | The opposite of subsumes
  supersumes :: d a -> d a -> Bool
  -- | Is the given value allowed for the domain variable
  contains :: d a -> a -> Bool
  -- | An abstract intersection operation.
  reduce :: d a -> d a -> d a
  -- | Union of allowed values
  expand :: d a -> d a -> d a
  reduces :: [d a] -> d a
  reduces t = foldl reduce universe t
  expands :: [d a] -> d a
  expands t = foldl expand nothing t
  
-- | Domains where the universe is a finite set.
class (Domain d) => FiniteDomain d where
  -- | list all values
  elems :: d a -> [a]
  
{- | Sort of like Bool; constraints use this to indicate how well a collection
 of domain variables satisfies.

 * Unsatisfiable -- No combination of allowed values will work.
 
 * Indeterminate -- Unknown if constraint can be satisfied.
 
 * Weak -- Some combinations of allowed values will satisfy.
 
 * Strong -- All possible combinations of allowed values satisfy.
-}
data Satisfaction = Unsatisfiable | Indeterminate | Weak | Strong 

-- | Combination operator for Satisfaction values.  
-- Least satisfactory wins out.
(<&>) :: Satisfaction -> Satisfaction -> Satisfaction
Unsatisfiable <&> _ = Unsatisfiable
_ <&> Unsatisfiable = Unsatisfiable
Indeterminate <&> _ = Indeterminate
_ <&> Indeterminate = Indeterminate
Weak <&> _ = Weak
_ <&> Weak = Weak
Strong <&> Strong = Strong


class Constraint c where
  satisfies :: (Domain d) => [d a] -> c (d a) -> Satisfaction
  decompose :: (Domain d) => 
               c (d a) -> [(i,d a)] -> Maybe [([(i,d a)],c (d a))]
  (+++) :: (Domain d) => c (d a) -> c (d a) -> c (d a)

class ConstraintSystem s where
  getDomain :: (Domain d, Constraint c) => s i (c (d a)) (d a) -> i -> d a
  setDomain :: (Domain d) => s i (c (d a)) (d a) -> i -> d a 
               -> s i (c (d a)) (d a)
  constrain :: (Domain d, Constraint c)
               => s i (c (d a)) (d a) -> [i] -> c (d a) -> s i (c (d a)) (d a)
  unconstrain :: (Domain d)
                 => s i (c (d a)) (d a) -> [i] -> s i (c (d a)) (d a)
  constraints :: (Domain d, Constraint c)
                 => s i (c (d a)) (d a) -> [([i], c (d a))]
  satisfied :: (Domain d) => s i (c (d a)) (d a) -> Satisfaction
  satisfied s = foldl (<&>) Strong $ concat $ map (sat s) $ constraints s where
    sat :: (Constraint c) => s i (c (d a)) (d a) -> 
           ([i],c (d a)) -> [Satisfaction]
    sat s (ix,c) = map (`satisfies` c) $ map (getDomain s) ix
  
{-  
class (ConstraintSystem s) => SolvableConstraints s where
  solution :: (Domain d) => s i (d a) -> Maybe (s i (d a))
  

-- | Calls decompose on all constraints within the system.
-- If decompose returns a Just value, replace domains with those in the
-- returned list, removes the original constraint, and applies the new
-- constraints from the decomposition.
decomposeConstraints :: (ConstraintSystem s, Domain d)
                        => s i (d a) -> s i (d a)
decomposeConstraints s = foldl deco s $ constraints s where
  -- inserts new domain/vars into system
  replace_doms :: (ConstraintSystem s, Domain d) 
                  => s i (d a) -> [(i,d a)] -> s i (d a)
  replace_doms s t = foldl (\s' (i,d) -> setDomain s' i d) s t
  -- applies new constraint
  apply_decon :: (ConstraintSystem s, Domain d, Constraint c)
                 => s i (d a) -> ([(i,d a)], c (d a)) -> s i (d a)
  apply_decon s (ix_d,c) = constrain (replace_doms s ix_d)
                           (map fst ix_d) c
  -- decomposes constraints, fold over apply_decon to apply each
  -- piece of the decomposition
  --deco :: (ConstraintSystem s, Constraint c, Domain d) 
  --        => s i (d a) -> ([i],c (d a)) -> s i (d a)
  deco sys (ix,c) = let decomp = decompose c $ 
                                 zip ix (map (getDomain s) ix) in
                    if isJust decomp then 
                      foldl apply_decon (unconstrain sys ix) $ fromJust decomp
                      else sys
  
-- data (FiniteDomain d, Ix i) => FSolver i (d a) = 
-}

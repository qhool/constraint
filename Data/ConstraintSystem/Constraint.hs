{-# LANGUAGE Rank2Types #-}
module Data.ConstraintSystem.Constraint (Satisfaction(..),
                                         (<&>),
                                         Constraint(..),
                                         compose) where

import Data.ConstraintSystem.Domain

import Data.Dynamic
import Data.Maybe

{- | Sort of like Bool; constraints use this to indicate how well a collection
 of domain variables satisfies.

 * Unsatisfiable -- No combination of allowed values will work.
 
 * Indeterminate -- Unknown if constraint can be satisfied.
 
 * Weak -- Some combinations of allowed values will satisfy.
 
 * Strong -- All possible combinations of allowed values satisfy.
-}
data Satisfaction = Unsatisfiable | Indeterminate | Weak | Strong deriving( Eq )

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

instance Show Satisfaction where
  show Strong = "Strong"
  show Weak = "Weak"
  show Indeterminate = "Indeterminate"
  show Unsatisfiable = "Unsatisfiable"

data Constraint d a = Constraint {
  satisfies :: (Domain d a) => [Maybe (d a)] -> Satisfaction,
  decompose :: (Domain d a,Ord k) => [(k,Maybe (d a))] -> 
               Maybe [([(k,Maybe (d a))],Constraint d a)],
  (+++) :: (Domain d a) => Constraint d a -> Constraint d a,
  constraint_type :: String,
  arguments :: [Dynamic]
  }
                    
{- simpleConstraint :: (Domain d, Ord k) =>
                    ( [Maybe (d a)] -> Satisfaction ) ->
                    ( [(k,Maybe (d a))] -> 
                      Maybe [([(k,Maybe (d a))],Constraint d)] ) ->
                    Constraint d
simpleConstraint s d = scomp where
  scomp = Constraint s d (compose scomp)
  --d :: [(k,Maybe (d a))] -> Maybe [([(k,Maybe (d a))],Constraint d)] -}
  
compose :: (Domain d a) => Constraint d a -> Constraint d a -> Constraint d a
compose c1 c2 = ccomp where
  ccomp = Constraint s d (compose ccomp) "compose" []
  s ds = (satisfies c1 ds) <&> (satisfies c2 ds)
  d kd = let decomp1 = decompose c1 kd in
    if isJust decomp1 then Just ((fromJust decomp1) ++ [(kd,c2)]) else 
      let decomp2 = decompose c2 kd in 
      if isJust decomp2 then Just ((fromJust decomp2) ++ [(kd,c1)]) else Nothing

{-# LANGUAGE Rank2Types #-}
module Data.ConstraintSystem (Satisfaction,
                              (<&>),
                             ) where

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ConstraintSystem.Domain

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

instance Show Satisfaction where
  show Strong = "Strong"
  show Weak = "Weak"
  show Indeterminate = "Indeterminate"
  show Unsatisfiable = "Unsatisfiable"


{- class Constraint c where
  satisfies :: (Domain d) => [d a] -> c (d a) -> Satisfaction
  decompose :: (Domain d) => c (d a) -> [(i,d a)] -> Maybe [([(i,d a)],c (d a))]
  decompose c di = Nothing
  (+++) :: (Domain d) => c (d a) -> c (d a) -> c (d a)
-}

data Constraint d = Constraint {
  satisfies :: (Domain d) => [Maybe (d a)] -> Satisfaction,
  decompose :: (Domain d,Ord k) => [(k,Maybe (d a))] -> 
               Maybe [([(k,Maybe (d a))],Constraint d)],
  (+++) :: (Domain d) => Constraint d -> Constraint d
  }
                    
{- simpleConstraint :: (Domain d, Ord k) =>
                    ( [Maybe (d a)] -> Satisfaction ) ->
                    ( [(k,Maybe (d a))] -> 
                      Maybe [([(k,Maybe (d a))],Constraint d)] ) ->
                    Constraint d
simpleConstraint s d = scomp where
  scomp = Constraint s d (compose scomp)
  --d :: [(k,Maybe (d a))] -> Maybe [([(k,Maybe (d a))],Constraint d)] -}
  
compose :: (Domain d) => Constraint d -> Constraint d -> Constraint d
compose c1 c2 = ccomp where
  ccomp = Constraint s d (compose ccomp)
  s ds = (satisfies c1 ds) <&> (satisfies c2 ds)
  d kd = let decomp1 = decompose c1 kd in
    if isJust decomp1 then Just ((fromJust decomp1) ++ [(kd,c2)]) else 
      let decomp2 = decompose c2 kd in 
      if isJust decomp2 then Just ((fromJust decomp2) ++ [(kd,c1)]) else Nothing
  
data ConstraintSystem k c d =
  CSys (Map k d) (Map [k] c)

getDomain :: (Domain d, Ord k) =>
             ConstraintSystem k c (d a) -> k -> Maybe (d a)
getDomain (CSys d_map _) key = Map.lookup key d_map

setDomain :: (Domain d, Ord k) =>
             ConstraintSystem k c (d a) -> 
             k -> 
             d a ->
             ConstraintSystem k c (d a)
setDomain (CSys d_map c_map) key dom = CSys (Map.insert key dom d_map) c_map

removeDomain :: (Ord k) =>
             ConstraintSystem k c d -> k ->
             ConstraintSystem k c d 
removeDomain (CSys d_map c_map) key = CSys (Map.delete key d_map) c_map

updateDomain :: (Domain d, Ord k) =>
             ConstraintSystem k c (d a) -> 
             k -> 
             Maybe (d a) ->
             ConstraintSystem k c (d a)
updateDomain s key mDom = if isJust mDom then setDomain s key (fromJust mDom)
                          else removeDomain s key

constrain :: (Domain d, Ord k) =>
             ConstraintSystem k (Constraint d) (d a) -> 
             Constraint d -> 
             [k] -> 
             ConstraintSystem k (Constraint d) (d a) 
constrain (CSys d_map c_map) c ks = CSys d_map (Map.insertWith (+++) ks c c_map)

unconstrain :: (Ord k) => 
               ConstraintSystem k c d ->
               [k] ->
               ConstraintSystem k c d
unconstrain (CSys d_map c_map) ks = CSys d_map (Map.delete ks c_map)

constraints :: (Domain d, Ord k) =>
               ConstraintSystem k (Constraint d) (d a) ->
               [([k],Constraint d)]
constraints (CSys _ c_map) = Map.assocs c_map


satisfied :: (Domain d, Ord k) =>
             ConstraintSystem k (Constraint d) (d a) -> Satisfaction
satisfied (CSys d_map c_map) = foldl (<&>) Strong $ 
                               map csat $ Map.assocs c_map where
  csat (ks,c) = satisfies c $ map (\k -> Map.lookup k d_map) ks


  

-- | Calls decompose on all constraints within the system.
-- If decompose returns a Just value, replace domains with those in the
-- returned list, removes the original constraint, and applies the new
-- constraints from the decomposition.
decomposeConstraints :: (Domain d, Ord k) =>
                        ConstraintSystem k (Constraint d) (d a) ->
                        ConstraintSystem k (Constraint d) (d a)

decomposeConstraints s = foldl deco s $ constraints s where
  -- inserts new domain/vars into system
  replace_doms :: (Domain d, Ord k) => 
                  ConstraintSystem k c (d a) -> 
                  [(k,Maybe (d a))] ->
                  ConstraintSystem k c (d a)
  replace_doms s t = foldl (\s' (key,dom) -> updateDomain s' key dom) s t
  -- applies new constraint
  apply_decon :: (Domain d, Ord k) =>
                 ConstraintSystem k (Constraint d) (d a) -> 
                 ([(k,Maybe (d a))], Constraint d) ->
                 ConstraintSystem k (Constraint d) (d a)
  apply_decon s (ix_d,c) = constrain (replace_doms s ix_d)
                           c (map fst ix_d) 
  -- decomposes constraints, fold over apply_decon to apply each
  -- piece of the decomposition
  deco :: (Domain d, Ord k) => 
          ConstraintSystem k (Constraint d) (d a) -> 
          ([k],Constraint d) ->
          ConstraintSystem k (Constraint d) (d a)
  deco sys (ix,c) = let decomp = decompose c $ 
                                 zip ix (map (getDomain sys) ix) in
                    if isJust decomp then 
                      foldl apply_decon (unconstrain sys ix) $ fromJust decomp
                      else sys
  
-- data (FiniteDomain d, Ix i) => FSolver i (d a) = 


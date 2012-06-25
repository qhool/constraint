module Data.ConstraintSystem (
                             ) where

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ConstraintSystem.Constraint
import Data.ConstraintSystem.Domain

data ConstraintSystem k c d =
  CSys (Map k d) (Map [k] c)
  
constraintSystem :: (Ord k) => [(k,d)] -> [([k],c)] -> ConstraintSystem k c d
constraintSystem d c = CSys (Map.fromList d) (Map.fromList c)

domains :: (Domain d a, Ord k) =>
           ConstraintSystem k c (d a) -> [(k,d a)]
domains (CSys d_map _) = Map.toList d_map

getDomain :: (Domain d a, Ord k) =>
             ConstraintSystem k c (d a) -> k -> Maybe (d a)
getDomain (CSys d_map _) key = Map.lookup key d_map

setDomain :: (Domain d a, Ord k) =>
             ConstraintSystem k c (d a) -> 
             k -> 
             d a ->
             ConstraintSystem k c (d a)
setDomain (CSys d_map c_map) key dom = CSys (Map.insert key dom d_map) c_map

removeDomain :: (Ord k) =>
             ConstraintSystem k c d -> k ->
             ConstraintSystem k c d 
removeDomain (CSys d_map c_map) key = CSys (Map.delete key d_map) c_map

updateDomain :: (Domain d a, Ord k) =>
             ConstraintSystem k c (d a) -> 
             k -> 
             Maybe (d a) ->
             ConstraintSystem k c (d a)
updateDomain s key mDom = if isJust mDom then setDomain s key (fromJust mDom)
                          else removeDomain s key

constrain :: (Domain d a, Ord k) =>
             ConstraintSystem k (Constraint d a) (d a) -> 
             Constraint d a -> 
             [k] -> 
             ConstraintSystem k (Constraint d a) (d a) 
constrain (CSys d_map c_map) c ks = CSys d_map (Map.insertWith (+++) ks c c_map)

unconstrain :: (Ord k) => 
               ConstraintSystem k c d ->
               [k] ->
               ConstraintSystem k c d
unconstrain (CSys d_map c_map) ks = CSys d_map (Map.delete ks c_map)

constraints :: (Domain d a, Ord k) =>
               ConstraintSystem k (Constraint d a) (d a) ->
               [([k],Constraint d a)]
constraints (CSys _ c_map) = Map.assocs c_map


satisfied :: (Domain d a, Ord k) =>
             ConstraintSystem k (Constraint d a) (d a) -> Satisfaction
satisfied (CSys d_map c_map) = foldl (<&>) Strong $ 
                               map csat $ Map.assocs c_map where
  csat (ks,c) = satisfies c $ map (\k -> Map.lookup k d_map) ks


  

-- | Calls decompose on all constraints within the system.
-- If decompose returns a Just value, replace domains with those in the
-- returned list, removes the original constraint, and applies the new
-- constraints from the decomposition.
-- If any constraints are successfully decomposed, returns Just new_system
-- otherwise, Nothing
decomposeConstraints :: (Domain d a, Ord k) =>
                        ConstraintSystem k (Constraint d a) (d a) ->
                        Maybe (ConstraintSystem k (Constraint d a) (d a))

decomposeConstraints s = if_decomp $ foldl deco (0,s) $ constraints s where
  if_decomp (0,sys) = Nothing 
  if_decomp (_,sys) = Just sys
  -- inserts new domain/vars into system
  replace_doms :: (Domain d a, Ord k) => 
                  ConstraintSystem k c (d a) -> 
                  [(k,Maybe (d a))] ->
                  ConstraintSystem k c (d a)
  replace_doms s t = foldl (\s' (key,dom) -> updateDomain s' key dom) s t
  -- applies new constraint
  apply_decon :: (Domain d a, Ord k) =>
                 ConstraintSystem k (Constraint d a) (d a) -> 
                 ([(k,Maybe (d a))], Constraint d a) ->
                 ConstraintSystem k (Constraint d a) (d a)
  apply_decon s (ix_d,c) = constrain (replace_doms s ix_d)
                           c (map fst ix_d) 
  -- decomposes constraints, fold over apply_decon to apply each
  -- piece of the decomposition
  deco :: (Domain d a, Ord k) => 
          (Integer,ConstraintSystem k (Constraint d a) (d a)) -> 
          ([k],Constraint d a) ->
          (Integer,ConstraintSystem k (Constraint d a) (d a))
  deco (n,sys) (ix,c) = let decomp = decompose c $ 
                                 zip ix (map (getDomain sys) ix) in
                    if isJust decomp then 
                      (n+1,(foldl apply_decon (unconstrain sys ix) $ fromJust decomp))
                      else (n,sys)
-- | repeatedly apply decomposeConstraints
-- Returns a Just value if (at least) the first iteration is a Just value
fullyDecompose :: (Domain d a, Ord k) =>
                  ConstraintSystem k (Constraint d a) (d a) ->
                  Maybe (ConstraintSystem k (Constraint d a) (d a))
fullyDecompose s = let dc = decomposeConstraints s in
  if isJust dc then let dc' = fullyDecompose $ fromJust dc 
                    in if isJust dc' then dc' else dc
  else Nothing
  
generateGuesses :: (FiniteDomain d a, Ord k) =>
                   ConstraintSystem k c (d a) ->
                   [ConstraintSystem k c (d a)]
generateGuesses s@(CSys d_map _) = map (uncurry (setDomain s)) $
                                   concat $ map dguesses $ Map.toList d_map where
  dguesses (i,d) = map ((,)i) $ map single $ elems d 

finiteSolver :: (FiniteDomain d a, Ord k) =>
                ConstraintSystem k (Constraint d a) (d a) ->
                Maybe (ConstraintSystem k (Constraint d a) (d a))
finiteSolver s = case (satisfied s) of 
  Unsatisfiable -> Nothing
  Strong        -> Just s               
  _ -> let dc = fullyDecompose s in
    if isJust dc then finiteSolver $ fromJust dc
    else listToMaybe $ catMaybes $ map finiteSolver $ generateGuesses s
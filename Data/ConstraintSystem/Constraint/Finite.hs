module Data.ConstraintSystem.Constraint.Finite () where

import Data.ConstraintSystem.Constraint
import Data.ConstraintSystem.Domain

import Data.List
import Data.Maybe

uniqueConstraint :: (Eq a,FiniteDomain d a) => Constraint d a
uniqueConstraint = self where
  self = Constraint sat dec comp 
         "Data.ConstraintSystem.Constraint.Finite.uniqueConstraint" []
  sat ds = let justds = catMaybes ds
               zeros = filter ((==0).size) justds
               singles = filter ((==1).size) justds
               multis = filter ((>1).size) justds
               in
           if (length justds) == 0 then Indeterminate else
             if (length zeros) > 0 then Unsatisfiable else
               ( case compare (length singles) (size $ expands singles) of
                    GT -> Unsatisfiable
                    _ -> Strong )
               <&>
               ( case compare (length multis) (size $ expands multis) of
                    GT -> Unsatisfiable
                    _ -> if ((==0).length) multis then Strong else Weak )
  --decompose by finding any single-valued domains, and removing them from 
  dec ixds = let (singles,others) = 
                   partition (\(i,d) -> (isJust d) && (((==1).size.fromJust) d)) ixds
                 exp = expands $ map (fromJust.snd) singles
             in if (length singles) == 0 then Nothing      
                else Just [(map (\(i,d) -> (i,fmap (reduce exp) d)) others,
                            uniqueConstraint)]
  comp other | (constraint_type other) == (constraint_type self) = self
             | otherwise = compose self other
                 
              
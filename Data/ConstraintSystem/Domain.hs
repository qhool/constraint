{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Data.ConstraintSystem.Domain (Domain(..),
                                     FiniteDomain(..)
                                    ) where

-- | Instances of Domain embody an unknown within a given domain.
class Domain d a where
  -- | a representation of all possible values.
  universe :: d a
  -- | null set of values
  nothing ::  d a
  -- | A domain variable with a single possible value.  In other words,
  -- a constant
  single :: a -> d a 
  -- | Return a variable which can take on any value in the list.
  enumerated :: [a] -> d a
  -- | a `subsumes` b == True if every allowed value for b is a value for a
  subsumes :: d a -> d a -> Bool
  -- | The opposite of subsumes
  supersumes :: d a -> d a -> Bool
  supersumes x y = subsumes y x
  -- | Is the given value allowed for the domain variable
  contains :: d a -> a -> Bool
  -- | An abstract intersection operation.
  reduce :: d a -> d a -> d a
  -- | Union of allowed values
  expand :: d a -> d a -> d a
  -- | Abstract difference
  remove :: d a -> d a -> d a
  reduces :: [d a] -> d a
  reduces t = foldl reduce universe t
  expands :: [d a] -> d a
  expands t = foldl expand nothing t
  
-- | Domains where the universe is a finite set.
class (Domain d a) => FiniteDomain d a where
  -- | list all values
  elems :: d a -> [a]
  size :: d a -> Int
  


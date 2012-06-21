{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Data.ConstraintSystem.Domain (Domain(..),
                                     FiniteDomain(..)
                                    ) where

import Data.List
import qualified Data.TypeLevel as Typ
import Data.Set (Set)
import qualified Data.Set as Set

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
  reduces :: [d a] -> d a
  reduces t = foldl reduce universe t
  expands :: [d a] -> d a
  expands t = foldl expand nothing t
  
-- | Domains where the universe is a finite set.
class (Domain d a) => FiniteDomain d a where
  -- | list all values
  elems :: d a -> [a]

data ModuloDomain mod a = 
  All | Empty | Listed { values :: Set a }



modulus :: (Typ.Nat mod, Integral a) => ModuloDomain mod a -> a
modulus x = Typ.toNum (gt x) where
  gt :: (Typ.Nat mod) => ModuloDomain mod a -> mod
  gt = undefined
  
applyModulus :: (Typ.Nat mod, Integral a) => 
                ModuloDomain mod a -> 
                ModuloDomain mod a
applyModulus All = All
applyModulus Empty = Empty
applyModulus d@(Listed s) = Listed (Set.map (`mod` (modulus d)) s)

instance (Typ.Nat mod, Integral a) => Domain (ModuloDomain mod) a where
  universe = All
  nothing = Empty
  single x = applyModulus $ Listed (Set.singleton x)
  enumerated xs = applyModulus $ Listed (Set.fromList xs)
  All `subsumes` _ = True
  _ `subsumes` Empty = True
  _ `subsumes` All = False
  Empty `subsumes` _ = False
  (Listed s1) `subsumes` (Listed s2) = s2 `Set.isSubsetOf` s1
  contains All x = True
  contains Empty x = False
  contains d@(Listed s) x = (x `mod` (modulus d)) `Set.member` s
  reduce All d = d
  reduce d All = d
  reduce Empty _ = Empty
  reduce _ Empty = Empty
  reduce (Listed s1) (Listed s2) = let isect = Set.intersection s1 s2 in
    if Set.null isect then Empty else Listed isect
  expand All _ = All
  expand _ All = All
  expand Empty d = d
  expand d Empty = d
  expand (Listed s1) (Listed s2) = Listed (Set.union s1 s2)

instance (Typ.Nat mod, Integral a) => FiniteDomain (ModuloDomain mod) a where
  elems Empty = []
  elems d@(All) = init [0..(modulus d)]
  elems (Listed s1) = Set.toList s1
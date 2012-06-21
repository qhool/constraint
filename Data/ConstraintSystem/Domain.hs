{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}

module Data.ConstraintSystem.Domain (Domain(..),
                                     FiniteDomain(..)
                                    ) where

--import Data.TypeLevel
import Data.List
import qualified Data.TypeLevel as Typ
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Eq
import Data.Type.Bool

-- | Instances of Domain embody an unknown within a given domain.
class Domain d where
  -- | a representation of all possible values.
  universe :: d a
  -- | null set of values
  nothing ::  d a
  -- | A domain variable with a single possible value.  In other words,
  -- a constant
  single :: a -> d a 
  -- | Return a variable which can take on any value in the list.
  enumerated :: (Ord a) => [a] -> d a
  -- | a `subsumes` b == True if every allowed value for b is a value for a
  subsumes :: (Ord a) => d a -> d a -> Bool
  -- | The opposite of subsumes
  supersumes :: (Ord a) => d a -> d a -> Bool
  supersumes x y = subsumes y x
  -- | Is the given value allowed for the domain variable
  contains :: (Ord a) => d a -> a -> Bool
  -- | An abstract intersection operation.
  reduce :: (Ord a) => d a -> d a -> d a
  -- | Union of allowed values
  expand :: (Ord a) => d a -> d a -> d a
  reduces :: (Ord a) => [d a] -> d a
  reduces t = foldl reduce universe t
  expands :: (Ord a) => [d a] -> d a
  expands t = foldl expand nothing t
  
-- | Domains where the universe is a finite set.
class (Domain d) => FiniteDomain d where
  -- | list all values
  elems :: d a -> [a]

data ModuloDomain mod a = 
  All | Empty | Listed { values :: Set a }

modulus :: (Typ.Nat mod, Integral a) => ModuloDomain mod a -> a
modulus x = Typ.toNum (gt x) where
  gt :: (Typ.Nat mod) => ModuloDomain mod a -> mod
  gt = undefined
  
class Mod a where
  modP :: (Integral b) => a -> b -> a
  
class Mod' flag a where
  modP' :: (Integral b) => flag -> a -> b -> a
  
instance (IntegralPred a flag, Mod' flag a) => Mod a where
  modP = modP' (undefined::flag)
  
class IntegralPred a flag | a -> flag where {}
  
instance TypeCast flag TFalse => IntegralPred a flag

instance IntegralPred Int TTrue
instance IntegralPred Integer TTrue

instance Integral a => Mod' TTrue a where
  modP' _ a b = a `mod` b
  
instance Mod' TFalse a where
  modP' _ a b = a

{-
byMod :: (Typ.Nat mod, Integral a) => ModuloDomain mod a -> a -> a
byMod d a = a `mod` (modulus d)

byMod :: (Typ.Nat mod, Ord a) => ModuloDomain mod a -> a -> a
byMod d a = a
-}
  
instance (Typ.Nat mod) => Domain (ModuloDomain mod) where
  universe = All
  nothing = Empty
  single x = Listed (Set.singleton x)
  enumerated xs = Listed (Set.fromList xs)
  All `subsumes` _ = True
  _ `subsumes` Empty = True
  _ `subsumes` All = False
  Empty `subsumes` _ = False
  (Listed s1) `subsumes` (Listed s2) = s2 `Set.isSubsetOf` s1
  contains All x = True
  contains Empty x = False
  contains (Listed s) x = x `Set.member` s
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

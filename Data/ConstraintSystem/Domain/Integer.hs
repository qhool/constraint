{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Data.ConstraintSystem.Domain.Integer (SetDomain(..),
                                             ModuloDomain(..)
                                                      ) where

import Data.ConstraintSystem.Domain
import Data.List
import qualified Data.TypeLevel as Typ
import Data.Set (Set)
import qualified Data.Set as Set

class SetDomain d a where
  empty :: d a
  complete :: d a
  getSet :: d a -> Set a
  fromSet :: Set a -> d a
  isEmpty :: d a -> Bool
  isComplete :: d a -> Bool
  allowed :: d a -> a -> Bool
  
makeCanonical :: SetDomain d a => Set a -> d a
makeCanonical s = if Set.null s then empty else fromSet s
  
filterElements :: (Ord a,SetDomain d a) => d a -> d a
filterElements dom | isEmpty dom = empty
                   | isComplete dom = complete
                   | otherwise = makeCanonical $ Set.filter (allowed dom) $ getSet dom 

instance (Ord a,SetDomain d a) => Domain d a where
  universe = complete
  nothing = empty
  single x = filterElements $ fromSet (Set.singleton x)
  enumerated xs = filterElements $ fromSet (Set.fromList xs)
  subsumes a b | isComplete a = True
               | isEmpty b = True
               | isComplete b = False
               | isEmpty a = False
               | otherwise = Set.isSubsetOf (getSet b) (getSet a)
  contains d x | not (allowed d x) = False
               | isComplete d = True
               | isEmpty d = False
               | otherwise = x `Set.member` (getSet d)
  reduce a b | isComplete a = b
             | isComplete b = a
             | (isEmpty a) || (isEmpty b) = empty
             | otherwise = makeCanonical $ Set.intersection (getSet a) (getSet b)
  expand a b | (isComplete a) || (isComplete b) = complete
             | isEmpty a = b
             | isEmpty b = a
             | otherwise = makeCanonical $ Set.union (getSet a) (getSet b)
                         
data ModuloDomain mod a = 
  All | Empty | Listed { values :: Set a }

modulus :: (Typ.Nat mod, Integral a) => ModuloDomain mod a -> a
modulus x = Typ.toNum (gt x) where
  gt :: (Typ.Nat mod) => ModuloDomain mod a -> mod
  gt = undefined
  
instance (Typ.Nat mod, Integral a) => SetDomain (ModuloDomain mod) a where
  empty = Empty
  complete = All
  getSet Empty = Set.empty
  getSet d@(All) = Set.fromList $ init [0..(modulus d)]
  getSet (Listed s) = s
  fromSet s = Listed s
  isEmpty Empty = True
  isEmpty _ = False
  isComplete All = True
  isComplete _ = False
  allowed d x = (x >= 0) && (x < (modulus d))

instance (Typ.Nat mod, Integral a) => FiniteDomain (ModuloDomain mod) a where
  elems Empty = []
  elems d@(All) = init [0..(modulus d)]
  elems (Listed s1) = Set.toList s1
  size Empty = 0
  size d@(All) = fromIntegral $ modulus d
  size (Listed s1) = Set.size s1

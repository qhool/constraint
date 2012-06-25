{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Data.ConstraintSystem.Domain.Named (NamedVar(..),
                                           NamedDomain(..),
                                           SampleNames(..),
                                           fromList) where

import Data.ConstraintSystem.Domain
import Data.List

class NamedVar v where
  allValues :: [v]
  allValues' :: [v] -> [v]
  allValues' _ = allValues

data NamedDomain a = All | Empty | Listed { values :: [a] } deriving (Show,Eq)

fromList :: (Eq a, NamedVar a) => [a] -> NamedDomain a
fromList xs = if (length xs) == 0 then Empty else
                let xs' = nub xs in
                if 0 == ( length $ (allValues' xs) \\ xs' ) then All else Listed xs'

instance (Eq a, NamedVar a) => Domain NamedDomain a where
  universe = All
  nothing = Empty
  single x = Listed [x]
  enumerated xs = fromList xs
  subsumes All _ = True
  subsumes _ Empty = True
  subsumes Empty _ = False
  subsumes _ All = False
  subsumes (Listed xs) (Listed ys) = 0 == (length $ ys \\ xs)
  contains All _ = True
  contains Empty _ = False
  contains (Listed xs) y = y `elem` xs
  reduce Empty _ = Empty
  reduce _ Empty = Empty
  reduce All b = b
  reduce a All = a
  reduce (Listed xs) (Listed ys) = fromList $ filter (`elem` ys) xs
  expand All _ = All
  expand _ All = All
  expand Empty b = b
  expand a Empty = a
  expand (Listed xs) (Listed ys) = fromList $ xs ++ ys

instance (Eq a, NamedVar a) => FiniteDomain NamedDomain a where
  elems Empty = []
  elems All = allValues
  elems (Listed xs) = nub xs
  size Empty = 0
  size d@(All) = length $ elems d
  size (Listed xs) = length xs
  
data SampleNames = Alpha | Beta | Gamma | Delta deriving(Eq,Show)

instance NamedVar SampleNames where
  allValues = [Alpha,Beta,Gamma,Delta]


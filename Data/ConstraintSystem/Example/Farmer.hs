module Data.ConstraintSystem.Example.Farmer () where

import Data.ConstraintSystem.Domain
import Data.ConstraintSystem.Domain.Named
import Data.ConstraintSystem.Constraint

import Data.Dynamic
import Data.Maybe

data Positions = East | West | Boat deriving(Eq,Show)

instance NamedVar Positions where
  allValues = [East,West,Boat]
  
players = ["Farmer","Dog","Chicken","Corn"]

protectionConstraint :: (FiniteDomain d a) => 
                        Int ->
                        Int ->
                        Constraint d a
protectionConstraint a b = self where
  self = Constraint sat dec comp
         "Data.ConstraintSystem.Example.Farmer.protectionConstraint"
         [toDyn a, toDyn b]
  sat ds = let farmer = fromJust $ ds!!0
               pa = fromJust $ ds!!a
               pb = fromJust $ ds!!b
               in if ((==0).size) $ reduce pa pb then Strong else
                    if ((>0).size) $ reduces [pa,pb,farmer] then Weak else Unsatisfiable
  dec _ = Nothing
  comp other = compose self other
            
pairs :: [a] -> [(a,a)]
pairs (x:y:ys) = (x,y):(pairs (y:ys))
pairs _ = []

triples :: [a] -> [(a,a,a)]
triples (x:y:z:zs) = (x,y,z):(triples (y:z:zs))
triples _ = []

allowedStep :: Positions -> [Positions]
allowedStep Boat = [East,West]
allowedStep x = [x,Boat]

nextStep :: NamedDomain Positions -> NamedDomain Positions
nextStep d = enumerated $ concat $ map allowedStep $ elems d

frst (a,_,_) = a
scnd (_,b,_) = b
thrd (_,_,c) = c

--domains here are the same player, in different turns
movementRule :: Constraint NamedDomain Positions
movementRule = self where
  self = Constraint sat dec comp
         "Data.ConstraintSystem.Example.Farmer.movementRule" []
  sat ds = foldl (<&>) Strong $ map sat' $ pairs $ catMaybes ds
  sat' (a,b) = let nx_a = nextStep a
                   nx_b = nextStep b in
               if (subsumes nx_a b) && (subsumes nx_b a) then Strong else
                 if ((==0).size $ reduce nx_a b) || 
                    ((==0).size $ reduce nx_b a) then Unsatisfiable else Weak
  dec [] = Nothing
  dec ixds = let dummy = ((fst.head) ixds,Nothing) 
                 decs = map dec' $ triples $ dummy:(ixds++[dummy]) in 
             if or $ map frst decs then 
               Just [(map (\(_,ix,md)->(ix,md)) decs,movementRule)] 
             else Nothing
  dec' (a,(ix,Nothing),c) = (False,ix,Nothing)
  dec' (a,(ix,Just b),c) = let a' = snd a
                               c' = snd c
                               nx_a = if isNothing a' then universe 
                                      else nextStep $ fromJust a'
                               nx_c = if isNothing c' then universe
                                      else nextStep $ fromJust c' in
                 if (subsumes nx_a b) && (subsumes nx_c b) then (False,ix,Just b)
                 else (True,ix,Just $ reduces [nx_a,b,nx_c])
  comp = compose self
  
--boatCapacity :: Constraint NamedDomain Positions
--boatCapacity = self where
--  self = Constraint sat dec comp
--  sat ds = 

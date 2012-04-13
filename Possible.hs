module Possible (Possible, 
                 Impossible, Unconstrained, Known, CouldBe)
       where

import Data.Array
import Data.IntSet (IntSet)
import Data.Set (Set)
import Data.List
import Data.Ord
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set

data Possible p = Impossible | Unconstrained | Known a | CouldBe Set a deriving (Show,Eq) 

combinePossible :: (Eq a) => Possible a -> Possible a -> Possible a
combinePossible Impossible x = Impossible
combinePossible x Impossible = Impossible
combinePossible Unconstrained x = x
combinePossible x Unconstrained = x
combinePossible (Known x) (Known y) | x == y = Known x
combinePossible (Known x) (CouldBe s) | x `Set.member` s = Known x
                                      | otherwise = Impossible
combinePossible (CouldBe s) (Known x) | x `Set.member` s = Known x
                                      | otherwise = Impossible

reducePossibilities :: (Eq a) => [Possible a] -> Possible a
reducePossibilities p = foldl combinePossible Unconstrained p


instance Functor Possible where
  fmap f Impossible = Impossible
  fmap f Unconstrained = Unconstrained
  fmap f Known n = Known (f n)
  fmap f CouldBe s = CouldBe (Set.fmap f s)
  (<$) x = Known x
  
instance Applicative Possible where
  pure n = Known n
  (<*>) Impossible x = Impossible 
  (<*>) Unconstrained x = x
  (<*>) (Known f) x = fmap f x
  (<*>) (CouldBe s) x = reducePossibilities $ map (<$>x) $ Set.elems s
  
instance Monad Possible where
  return a = Known a
  Impossible >>= _ = Impossible
  Unconstrained >>= _ = Unconstrained 
  (Known n) >>= f = f n
  (CouldBe s) >>= f = reducePossibilities $ map (<$>x) $ Set.elems s
  
instance MonadPlus Possible where
  mzero = Unconstrained
  mplus a b = combinePossible a b

data (Ix i) => MagicPuzzle i 

type SudokuSquare = Solvable Int

type SudokuPuzzle = Array (Int,Int) SudokuSquare

sudokuValues :: Set Int
sudokuValues = Set.fromList [1..9]

initSquare :: Int -> SudokuSquare
initSquare 0 = CouldBe sudokuValues
initSquare n = Known n

squareFromSet :: Set -> SudokuSquare
squareFromSet s | Set.size s == 1 = Known $ head $ IntSet.toList s
                | otherwise = CouldBe s

initSudoku :: [[Int]] -> SudokuPuzzle
initSudoku rows = let startp = listArray ((1,1),(9,9)) $ map initSquare $ concat rows
                  in mapPuzzle (reduceCoulds startp) startp

toStr :: SudokuPuzzle -> String
toStr p = ( concat $ map (\(i,j) -> ( case (p!(i,j)) of
                                         Known n -> show n
                                         _ -> "-" )
                                    ++ if j == 9 then "\n" else "") $ indices p ) ++ "\n"

isKnown :: SudokuSquare -> Bool
isKnown (Known n) = True
isKnown _ = False

isConflicted :: SudokuSquare -> Bool
isConflicted (Known _) = False
isConflicted (CouldBe t) = ((IntSet.size t) == 0)

countKnown :: Integral a => SudokuPuzzle -> a
countKnown p = sum $ fmap (\s -> if isKnown s then 1 else 0) $ elems p

isSolved :: SudokuPuzzle -> Bool
isSolved p = ((length $ indices p) == (countKnown p)) && (validateState p)

isUnsolvable :: SudokuPuzzle -> Bool
isUnsolvable p = let detsol = deterministicSolver p
                 in (any isConflicted $ elems $ solveBy reduceCoulds detsol) || (not $ validateState detsol)

knownVal :: SudokuSquare -> Int
knownVal (Known n) = n

couldBeVals :: SudokuSquare -> IntSet
couldBeVals (CouldBe t) = t

rowIdx = map (\m -> map (\n -> (n,m)) [1..9]) [1..9]

colIdx = map (\m -> map (\n -> (m,n)) [1..9]) [1..9]

blockIdx = map (\offset -> map (\s -> ((fst s) + (fst offset),(snd s) + (snd offset))) bloc) offsets where
  bloc = [ (i,j) | i <- [0..2], j <- [0..2] ]
  offsets = [ (n,m) | n <- [1,4,7], m <- [1,4,7] ]

squareSets :: SudokuPuzzle -> [[SudokuSquare]]
squareSets puz = map (\ixl -> map (puz!) ixl) (rowIdx ++ colIdx ++ blockIdx)
  
--set of known values in the given squares
takenValues :: [SudokuSquare] -> IntSet
takenValues t = IntSet.fromList $ tvs t where
  tvs (x:xs) | isKnown x = knownVal x : (tvs xs)
             | otherwise = tvs xs
  tvs _ = []
  
possibleValues :: [SudokuSquare] -> IntSet
possibleValues ((Known n):xs) = IntSet.union (IntSet.singleton n) (possibleValues xs)
possibleValues ((CouldBe t):xs) = IntSet.union t (possibleValues xs)
possibleValues _ = IntSet.empty

validateState :: SudokuPuzzle -> Bool
validateState p = all ((==sudokuValues).possibleValues) $ squareSets p

--list of values that none of the squares could be, or are known to be:
freeValues :: [SudokuSquare] -> IntSet
freeValues squares = sudokuValues IntSet.\\ (possibleValues squares) where

section :: SudokuPuzzle -> [(Int,Int)] -> [SudokuSquare]
section p (x:xs) = (p!x):(section p xs)
section p _ = []

crossIdx :: (Int,Int) -> [[(Int,Int)]]
crossIdx (i,j) = [row,col,block] where
  --all 3 of these remove the given index from the list
  row = [ (i,n) | n <- [1..(j-1)] ++ [(j+1)..9] ]
  col = [ (n,j) | n <- [1..(i-1)] ++ [(i+1)..9] ]
  block = filter ((i,j)/=) $ head $ filter ((i,j)`elem`) blockIdx
  
crossSections :: SudokuPuzzle -> (Int,Int) -> [[SudokuSquare]]
crossSections p i = map (section p) $ crossIdx i

mapPuzzle :: ( ((Int,Int),SudokuSquare) -> SudokuSquare ) -> SudokuPuzzle -> SudokuPuzzle
mapPuzzle f p = array (bounds p) $ map (\(i,e) -> (i, f (i,e))) $ assocs p 

solveBy :: (SudokuPuzzle -> ((Int,Int),SudokuSquare) -> SudokuSquare ) -> SudokuPuzzle -> SudokuPuzzle
solveBy f p = fst $ head $ dropWhile (\(s,s') -> (s/=s')) --wait for iteration state to settle
              [ (sols!!i,sols!!(i+1)) | i <- [1..] ] where
  sols = iterate (\p' -> mapPuzzle (f p') p') p
  
--solution methods:  
  
--remove values from CouldBe that appear elsewhere in the row, column, or block:
reduceCoulds :: SudokuPuzzle -> ((Int,Int),SudokuSquare) -> SudokuSquare
reduceCoulds _ (_,(Known n)) = Known n
reduceCoulds p (ix,(CouldBe t)) = let xsect = crossSections p ix
                                  in squareFromSet (t IntSet.\\ (IntSet.unions $ map takenValues $ xsect))

--check if there is a single value which doesn't appear in any 
uniqueCoulds :: IntSet -> [SudokuSquare] -> SudokuSquare
uniqueCoulds t squares = squareFromSet (IntSet.intersection t (freeValues squares))

onlyCould :: SudokuPuzzle -> ((Int,Int),SudokuSquare) -> SudokuSquare
onlyCould _ (_,(Known n)) = Known n
onlyCould p (ix,(CouldBe t)) = let xsect = crossSections p ix
                               in head $ ( filter (isKnown) $ map (uniqueCoulds t) $ xsect ) ++ [CouldBe t] 

catSolvers :: [( SudokuPuzzle -> ((Int,Int),SudokuSquare) -> SudokuSquare )]
              -> ( SudokuPuzzle -> ((Int,Int),SudokuSquare) -> SudokuSquare )
catSolvers (f:fs) = (\p (ix,square) -> ((f p) . (\s -> (ix,s)) . ((catSolvers fs) p)) (ix,square))
catSolvers _ = (\p (ix,square) -> square)

deterministicSolver :: SudokuPuzzle -> SudokuPuzzle
deterministicSolver = solveBy (catSolvers [reduceCoulds, onlyCould])

tryOptions :: SudokuPuzzle -> [SudokuPuzzle]
tryOptions p = let trysquares = sortBy (comparing (((-1)*).IntSet.size.couldBeVals.snd)) 
                                $ filter (not.isKnown.snd) $ assocs p
               in concat $ map (\ts -> map (\n -> p//[(fst ts,Known n)]) $ IntSet.elems $ couldBeVals $ snd ts) trysquares
                  
trySolverMax :: Int -> SudokuPuzzle -> SudokuPuzzle
trySolverMax max p | max == 0 = p
                   | otherwise = let detsol = deterministicSolver p
                                 in if isSolved detsol then detsol 
                                    else head ((filter isSolved $ map ( trySolverMax (max-1) ) 
                                                $ filter (not.isUnsolvable) $ tryOptions detsol)++[detsol])

trySolver p = trySolverMax (-1) p

testPuz = initSudoku [
  [0, 0, 3, 0, 2, 0, 6, 0, 0],
  [9, 0, 0, 3, 0, 5, 0, 0, 1],
  [0, 0, 1, 8, 0, 6, 4, 0, 0],
  [0, 0, 8, 1, 0, 2, 9, 0, 0],
  [7, 0, 0, 0, 0, 0, 0, 0, 8],
  [0, 0, 6, 7, 0, 8, 2, 0, 0],
  [0, 0, 2, 6, 0, 9, 5, 0, 0],
  [8, 0, 0, 2, 0, 3, 0, 0, 9],
  [0, 0, 5, 0, 1, 0, 3, 0, 0]
  ]
module Data.ConstraintSystem.Example.Sudoku (SudokuSquare,
                                             Sudoku,
                                             initSudoku,
                                             sudokuToStr,
                                             testPuz,
                                             rowIdx,
                                             colIdx,
                                             blockIdx) where

import Data.ConstraintSystem
import Data.ConstraintSystem.Domain
import Data.ConstraintSystem.Domain.Integer
import Data.ConstraintSystem.Constraint
import Data.ConstraintSystem.Constraint.Finite
import Data.Maybe
import qualified Data.TypeLevel as Typ

sudokuIndices :: [(Int,Int)]
sudokuIndices = concat colIdx

rowIdx :: [[(Int,Int)]]
rowIdx = map (\m -> map (\n -> (n,m)) [1..9]) [1..9]

colIdx :: [[(Int,Int)]]
colIdx = map (\m -> map (\n -> (m,n)) [1..9]) [1..9]

blockIdx :: [[(Int,Int)]]
blockIdx = map (\offset -> map (\s -> ((fst s) + (fst offset),(snd s) + (snd offset))) bloc) offsets where
  bloc = [ (i,j) | i <- [0..2], j <- [0..2] ]
  offsets = [ (n,m) | n <- [1,4,7], m <- [1,4,7] ]
  
crossSections = rowIdx ++ colIdx ++ blockIdx

type SudokuSquare = ModuloDomain Typ.D9

type Sudoku = ConstraintSystem (Int,Int) (Constraint SudokuSquare Int) (SudokuSquare Int)

sudokuConstraints :: [([(Int,Int)],Constraint SudokuSquare Int)]
sudokuConstraints = zip crossSections $ repeat uniqueConstraint

initSudoku :: [[Int]] -> Sudoku
initSudoku rows = constraintSystem (concat $ map build_row $ zip [1..9] rows) 
                  sudokuConstraints
  where
  build_row (i,r) = zip (map ((,)i) [1..9]) $ map build_sq r
  build_sq n = if n > 0 then single (n-1) else universe
  
  
sudokuToStr :: Sudoku -> String
sudokuToStr p = ( concat $ 
                  map (\(i,j) -> 
                        ( sqStr (i,j) )
                          ++ if j == 9 then "\n" else "" ) $ 
                        sudokuIndices ) ++ "\n" 
  where
  sqStr ix = let md = getDomain p ix in
    if isNothing md then "?" else
      let d = fromJust md in
      if size d == 1 then show $ ((head $ elems d) + 1)
      else "-"


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
          
testPuz2 = initSudoku [
  [0, 0, 3,    0, 2, 1,    6, 0, 0],
  [9, 0, 0,    3, 0, 5,    0, 0, 1],
  [0, 0, 1,    8, 0, 6,    4, 0, 0],
  
  [0, 0, 8,    1, 0, 2,    9, 0, 0],
  [7, 2, 0,    5, 0, 0,    0, 0, 8],
  [0, 0, 6,    7, 0, 8,    2, 0, 0],
  
  [0, 0, 2,    6, 0, 9,    5, 0, 0],
  [8, 0, 0,    2, 5, 3,    0, 0, 9],
  [0, 0, 5,    0, 1, 0,    3, 0, 0]
  ]
           
testPuz3 = initSudoku [
  [1, 0, 0,    0, 0, 0,    0, 0, 4],
  [2, 0, 0,    0, 0, 0,    0, 3, 0],
  [3, 0, 0,    0, 0, 0,    1, 0, 0],
  
  [4, 0, 0,    0, 0, 3,    0, 0, 0],
  [5, 0, 0,    0, 0, 5,    0, 0, 0],
  [6, 0, 0,    0, 0, 0,    0, 0, 0],
  
  [7, 0, 0,    0, 0, 0,    0, 0, 0],
  [8, 0, 0,    0, 0, 0,    0, 0, 0],
  [0, 2, 3,    4, 5, 6,    7, 8, 9]
  ]
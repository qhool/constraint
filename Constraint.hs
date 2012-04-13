module Domain () where

class Domain d where
  universe :: d a
  nothing :: d a
  contains :: d a -> d a -> Bool
  reduce :: d a -> d a -> d a
  expand :: d a -> d a -> d a
  reduces :: [d a] -> d a
  expands :: [d a] -> d a

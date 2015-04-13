module Main where

import Tree

---------- MAIN FUCTION FOR ORDER LIST ----------
abbSort ::  (Ord a) => [a] -> [a]
abbSort (x:xs) = treeToList( listToTree(x:xs) )
-------------------------------------------------

---------------- SELECTION SORT -----------------
selSort :: (Ord a) => [a] -> [a]
selSort [] = []
selSort xs = let x = minimum xs in x : selSort (remove x xs) 
  where remove _ [] = []
        remove a (x:xs)
          | x == a = xs
          | otherwise = x : remove a xs

{- EXTRACTED FROM : http://rosettacode.org/wiki/Sorting_algorithms/Selection_sort -}
-------------------------------------------------



main = abbSort [1,3,4,5,7,3,23,4,4,5,645,64,7,3,34,6,456,45]
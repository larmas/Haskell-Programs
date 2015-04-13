module Tree ( BinTree(Null,Node), treeToList, listOrd, isABB, listToTree, insABB, takeFirst, getMin, rList) where

import System.Random

data BinTree a = Null | Node (BinTree a) a (BinTree a) deriving Show

------------- CONVERT THE TREE AT LIST ---------
treeToList :: (Ord a) => BinTree a -> [a]
treeToList Null = []
treeToList ( Node i r d ) =  treeToList ( i ) ++ [r] ++ treeToList ( d ) 
------------------------------------------------

------ VERIFY IF THE TREE IS IN ORDEN OR NOT----
listOrd ::(Ord a) =>[a]->Bool
listOrd [] = True
listOrd [x] = True
listOrd ( x : y : xs ) = ( x <= y ) && listOrd ( y : xs )

isABB :: (Ord a) =>BinTree a -> Bool
isABB ( Node i r d ) = listOrd ( treeToList ( Node i r d ))
--------------------------------------------------

------- CONVERT THE LIST AT TREE ----------------
listToTree::(Ord a) => [a] -> BinTree a
listToTree []  = Null
listToTree (x:xs) = insABB (listToTree xs ) $! x 
-------------------------------------------------

----- INSERT AN ELEMENT IN THE TREE --------------
insABB :: (Ord a) => BinTree a -> a -> BinTree a
insABB Null x = (Node Null x Null)
insABB (Node i r d) x | x <= r = (Node (insABB i x) r d)
					  | otherwise = (Node i r (insABB d x))
-------------------------------------------------

--RETURN THE MIN ELEMENT AND THE REST THE LIST---
takeFirst :: (Ord a) => [a] -> ( a , BinTree a)
takeFirst [x] = ( x , Null )
takeFirst (x:xs) = ( x , listToTree xs )

getMin :: ( Ord  a )  =>  BinTree  a  ->  ( a ,  BinTree  a ) 
getMin ( Node Null x Null ) = ( x , Null) 
getMin ( Node  i  r  d )  =  takeFirst ( treeToList ( Node  i  r  d ))
-------------------------------------------------

------------ CREATE A RANDOM LIST ---------------
rList n = take n $! (randoms (mkStdGen (0)))::[Integer]
-------------------------------------------------

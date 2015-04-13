take1 :: [a] -> Int -> [a] -- take first element of list
take1 [] n = []
take1 xs 0 = []
take1 (x:xs) n = x : take1 xs (n-1)

drop1 :: [a] -> Int -> [a] --drop first element of list
drop1 [] n = []
drop1 xs 0 = xs
drop1 (x:xs) n = drop1 xs (n-1)

abs1 :: Int -> Int --valor absolute
abs1 n |n >= 0 = n
      | n < 0 = -n
      
list :: Int -> [Int] -- list by compression
list n = [y | y <- [0..n], 0 == (  mod y 2)]

birthday :: (Int,Int,Int) -> (Int,Int,Int) -> Int --calculate how much age you have
birthday (a,b,c) (d,e,f) | b>e = abs1(c-f) -1  
                         | b==e && a>d = abs1(c-f)-1 
                         | b==e && a<=d = abs1(c-f)
                         | b<e = abs1(c-f)


fElem :: [a] -> a  -- return first elemnt of a list
fElem (x:xs) = x                         

whipList :: [a] -> [a] --return the list without first element
whipList [] = []
whiplist (x:xs) = xs

lastElem :: [a] -> a  --return last element of the list
lastElem [x] = x
lastElem (x:xs) = lastElem xs

whitoutLast :: [a] -> [a] --return the list without last element
whitoutLast [] = []
whitoutLast [x] = []
whitoutLast (x:xs) = x : whitoutLast xs

prime :: Int -> Bool -- verify if a number is prime or not
prime 0 = False
prime 1 = False
prime n = equalList [] [ y | y <- [2..n-1], 0 == mod n y ]

listPrimeLess :: Int -> [Int] -- create a list with the primes less to n
listPrimeLess n = [y | y <- [1.. n-1] , True == prime y ]


invert ::[a] -> [a] --return the orden reverse of a list
invert [] = []
invert (x:xs) = invert xs ++ [x]

equalList  :: [Int] -> [Int] -> Bool -- verify if two list are equal
equalList [] [] = True
equalList [] xs = False
equalList xs [] = False
equalList (x:xs) (y:ys) | x == y = equalList xs ys
                        | otherwise = False
                        
palindrome :: [Int] -> Bool -- verify if a list is capicua or her orden is equal to inverse
palindrome [] = True
palindrome (x:xs) = equalList (x:xs) (invert(x:xs))
--1
merge :: [Int] -> [Int] -> [Int]
merge [] ys = ys
merge xs [] = xs
merge [] [] = []
merge (x:xs) (y:ys)| x <= y = (x : (y :  merge xs ys))
                      | x > y = (y : (x : merge xs ys))

--2
ordList :: Ord a => [a] -> [a]
ordList [] = []
ordList (x:xs) = ordList [y | y <- xs, y <= x] ++ [x] ++ ordList [z | z <-xs, z>x]

--3
baseTwo :: Int -> Int
baseTwo 0 = 1
baseTwo n = 2 * baseTwo (n-1)

--4				  
bin :: Int -> [Int]
bin 0 = [0]
bin 1 = [1]
bin n = bin(div n 2) ++ [mod n 2]	

--5
decimal :: [Int] -> Bool
decimal xs | mod (calcBin (baseList (length xs-1)) xs) 2 == 0 = True
		   | otherwise = False

baseList :: Int -> [Int]
baseList 0 = [1]
baseList n = 2^n : (baseList (n-1))

calcBin :: [Int] -> [Int] -> Int
calcBin [] [] = 0
calcBin (x:xs) (y:ys) |y == 1 = x + calcBin xs ys
					  | otherwise = calcBin xs ys

--6
square :: Int -> Bool
square 0 = True
square n |cant [x|x<- [1..n], n==x*x] == 0 = False
		 | otherwise = True

--7


--8
sumar :: [Float] -> Float
sumar [] = 0
sumar [x] = x
sumar (x:xs) = x + sumar xs

promedio :: [Float] -> Float
promedio (x:xs) = (sumar (x:xs)) / (cant (x:xs))

cant :: [a] -> Float
cant [] = 0
cant [x] = 1
cant (x:xs) = 1 + cant xs

--9
repeeat :: Int -> a -> [a]
repeeat 0 x = []
repeeat n x = x : repeeat (n-1) x

--10
index :: [Int] -> Int -> Int
index (x:xs) 0 = x
index [] n = -99999
index (x:xs) n = index xs (n-1)

--11 a
minord ::Ord a => [a] -> a
minord (x:xs) = head (ordList(x:xs))

--11 b
minfold :: Ord a => [a] -> a
minfold = foldl1 min		

--metodo de inserscion
insert :: Ord a => a -> [a] -> [a]
insert a [] = [a]
insert a (x:xs) | a <= x = a : x : xs
				| otherwise = x : insert a xs

insertShort :: Ord a => [a] -> [a]
insertShort  = foldr insert []				
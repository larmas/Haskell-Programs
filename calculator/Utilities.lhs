> module Utilities where

> joinWith :: [a] -> [[a]] -> [a]
> joinWith zs = foldr1 op  
>               where op xs ys = xs ++ zs ++ ys

> splitBy :: (a -> Bool) -> [a] -> ([a],[a])
> splitBy p [] = ([],[])
> splitBy p (x:xs) = if p x then (x:ys,zs) else (ys,x:zs)
>                    where (ys,zs) = splitBy p xs

> partitions :: Int -> [a] -> [[[a]]]
> partitions 0 []         = [[]]
> partitions (n+1) []     = []
> partitions 0 (x:xs)     = []
> partitions (n+1) (x:xs) 
>    = [[x]:yss | yss <- partitions n xs] ++
>      [(x:ys):yss | ys:yss <- partitions (n+1) xs]


> inits :: [a] -> [[a]]
> inits [] = [[]]
> inits (x:xs) = []: map (x:) (inits xs)


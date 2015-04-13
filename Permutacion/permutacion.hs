--PRACTICA 2
-- ejercicio 2 inciso 1
permutar :: Eq a=>[a]->[[a]]
permutar [] = [[]]
permutar (xs) = concat [map((++)[y]) (permutar(cut y xs )) | y<-xs ]

cut:: Eq a=> a->[a]->[a]
cut x [] = []
cut x (y:ys) | x==y = ys
						 | otherwise = [y]++(cut x ys)

-- ejercicio 2 inciso 2			 


subConjunto :: Eq a=>[a]->[[a]]
subConjunto [] = [[]]
subConjunto (xs) = concat [map((++)[y]) (subConjunto(soltar y xs )) | y<-xs ] ++ [[]]

soltar :: Eq a=> a->[a]->[a]
soltar x [] = []
soltar x (y:ys) | x==y = ys
							  | otherwise = (soltar x ys)
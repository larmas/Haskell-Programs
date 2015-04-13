anagrama :: String -> String -> Bool
anagrama "" "" = True
anagrama (x:xs) "" = False
anagrama "" (y:ys) = False
anagrama (x:xs) (y:ys) =  anagrama xs (find x (y:ys))



find :: Char -> String -> String
find x "" = ""
find x (y:ys) |(x == y) = ys
	     			  |otherwise = y:find x ys

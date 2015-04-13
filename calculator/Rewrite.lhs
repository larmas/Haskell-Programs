> module Rewrite where
> import Expressions (Expr(..),composeExprs)
> import Laws (Law)
> import Calculations (Calculation,Step)
> import Substitutions (applySub)
> import Match (matches)

The purpose of this module is to define the function calculate:

> calculate:: ([Law], [Law]) -> Expr -> Calculation
> calculate pls x = (x, repeatedly (rewrites pls) x)

> rewrites :: ([Law], [Law]) -> Expr -> [Step]
> rewrites (llaws,rlaws) x
>  = concat ([rewrite law sx x | law <- llaws, sx <- subExprs x] ++
>            [rewrite law sx x | sx <- subExprs x, law <- rlaws])

> rewrite :: Law -> SubExpr -> Expr -> [Step]
> rewrite (name, lhs, rhs) (loc, y) x 
>  = [(name, replace x loc (applySub s rhs)) | s <- matches (lhs, y)]

> repeatedly :: (Expr -> [Step]) -> Expr -> [Step]
> repeatedly rw x = if null steps then [] else (n,y):repeatedly rw y
>                   where steps = rw x
>                         (n,y) = head steps

> type SubExpr   = (Location, Expr)
> data Location  = All | Seg Int Int | Pos Int Location

> subExprs :: Expr -> [SubExpr]
> subExprs (Var v) = [(All, Var v)]
> subExprs (Con f xs) = [(All, Con f xs)] ++ subterms xs
> subExprs (Compose xs) 
>   = [(All, Compose xs)] ++ segments xs ++ reverse (subterms xs)

> subterms :: [Expr] -> [SubExpr]
> subterms xs 
>   = [(Pos j loc, y) | j <- [0 .. n-1], (loc,y) <- subExprs (xs!!j)]
>     where n = length xs

> segments :: [Expr] -> [SubExpr]
> segments xs = [(Seg j k, Compose (take k (drop j xs))) | 
>                 k <- [2..n-1], j <- [n-k,n-k-1..0]]
>               where n = length xs

> replace :: Expr -> Location -> Expr -> Expr
> replace x All y = y
> replace (Con f xs) (Pos j loc) y 
>  = Con f (take j xs ++ 
>    [replace (xs!!j) loc y] ++ drop (j+1) xs)
> replace (Compose xs) (Pos j loc) y
>  = composeExprs (take j xs ++ 
>    [replace (xs!!j) loc y] ++ drop (j+1) xs)
> replace (Compose xs) (Seg j k) y
>  = composeExprs (take j xs ++ [y] ++ drop (j+k) xs)
 


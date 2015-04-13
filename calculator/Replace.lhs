Subexpressions and replacement

> module Replace where
> import Expressions

> type SubExpr   = (Location, Expr)
> data Location  = Top | Seg Int Int | Pos Int Location

> subExprs :: Expr -> [SubExpr]
> subExprs (Var v)      = [(Top, Var v)]
> subExprs (Con f xs)   = [(Top, Con f xs)] ++ subterms xs
> subExprs (Compose xs) = [(Top, Compose xs)] ++ segments xs ++ subterms xs

> subterms :: [Expr] -> [SubExpr]
> subterms xs = [(Pos j loc, y) | j <- [0 .. length xs - 1], 
>                                 (loc,y) <- subExprs (xs!!j)]

> segments :: [Expr] -> [SubExpr]
> segments xs = [(Seg j k, Compose (take k (drop j xs))) | 
>                 k <- [2..n-1], j <- [0..n-k]]
>               where n = length xs


> replace :: Expr -> Location -> Expr -> Expr
> replace x Top y = y
> replace (Con f xs) (Pos j loc) y 
>       = Con f (take j xs ++ [replace (xs!!j) loc y] ++ drop (j+1) xs)
> replace (Compose xs) (Pos j loc) y
>       = compose (take j xs ++ [replace (xs!!j) loc y] ++ drop (j+1) xs)
> replace (Compose xs) (Seg j k) y
>       = compose (take j xs ++ [y] ++ drop (j+k) xs)
 

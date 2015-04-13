> module Match where
> import Expressions (Expr(..),composeExprs)
> import Substitutions (Subst,extendSub)
> import Utilities (partitions)

The purpose of this module is to define matches:

> matches :: (Expr, Expr) -> [Subst]
> matches (x,y) = match (x,y) []

> match :: (Expr, Expr) -> Subst -> [Subst]
> match (Var v, x) s = extendSub s (v,x)
> match (Con f xs, Var v) s = []
> match (Con f xs, Con g ys) s = if f == g then 
>                                matchlist (zip xs ys) s else []
> match (Con f xs, Compose ys) s = []
> match (Compose xs, Var v) s = []
> match (Compose xs, Con g ys) s = []
> match (Compose xs, Compose ys) s 
>         = concat (map (listmatch s) (align xs ys))
>           where listmatch s xys = matchlist xys s

> matchlist :: [(Expr, Expr)] -> Subst -> [Subst]
> matchlist [] s       = [s]
> matchlist (xy:xys) s = concat (map (matchlist xys) (match xy s))

> align :: [Expr] -> [Expr] -> [[(Expr, Expr)]]
> align xs ys 
>   = [zip xs (map composeExprs zs) 
>        | zs <- partitions (length xs) ys]



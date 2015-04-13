> module Substitutions where
> import Expressions (VarName,Expr (..),composeExprs)

> type Subst = [(VarName, Expr)]

> binding :: Subst -> VarName -> Expr
> binding [] v        = Var v
> binding ((u,x):s) v = if u == v then x else binding s v

> applySub :: Subst -> Expr -> Expr
> applySub s (Var v)      = binding s v
> applySub s (Con f xs)   = Con f (map (applySub s) xs)
> applySub s (Compose xs) = composeExprs (map (applySub s) xs)

> extendSub :: Subst -> (VarName, Expr) -> [Subst]
> extendSub s (v,x) 
>  | y == x      = [s]
>  | y == Var v  = [(v,x):s]
>  | otherwise   = []
>    where y = binding s v

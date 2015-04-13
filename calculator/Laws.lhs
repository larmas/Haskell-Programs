> module Laws where
> import MyParseLib
> import Expressions (Expr,expr,complexity)

> type Law     = (LawName, Expr, Expr)
> type LawName = String

> basicLaw :: Law -> Bool
> basicLaw (name, lhs, rhs) = (complexity lhs > complexity rhs)

> parseLaw :: String -> Law
> parseLaw = applyParser law

> law :: Parser Law
> law = do space         
>          name <- some (sat (/=':'))
>          symbol ":"
>          x <- expr
>          symbol "="
>          y <- expr
>          return (name,x,y)


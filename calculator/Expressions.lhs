> module Expressions where
> import MyParseLib
> import Utilities 

> data Expr    = Var VarName | Con ConName [Expr] | Compose [Expr]
>                deriving (Eq, Show)
> type VarName = Char
> type ConName = String

> complexity :: Expr -> Int
> complexity (Var v)      = 1
> complexity (Con f xs)   = 1
> complexity (Compose xs) = length xs

> composeExprs :: [Expr] -> Expr
> composeExprs xs 
>   = if null (tail xs) then head xs 
>     else Compose (concat (map decompose xs))

> decompose :: Expr -> [Expr]
> decompose (Var v)      = [Var v]
> decompose (Con f xs)   = [Con f xs]
> decompose (Compose xs) = xs

Printing expressions:

> printExpr :: Expr -> String
> printExpr (Var v) = [v]
> printExpr (Con f xs)
>  | null xs    = f
>  | single xs  = f ++ " " ++ printExpr (head xs)
>  | otherwise  = f ++ " (" ++ joinWith ", " (map printExpr xs) ++ ")"
> printExpr (Compose xs) = joinWith " . " (map printExpr xs)


> single :: [Expr] -> Bool
> single xs  = simpleton (head xs) && null (tail xs)

> simpleton :: Expr -> Bool
> simpleton (Var v)    = True 
> simpleton (Con f xs) = null xs 
> simpleton (Compose xs) = False


Parsing expressions:

> parseExpr :: String -> Expr
> parseExpr = applyParser expr

> expr :: Parser Expr
> expr = do {xs <- somewith (symbol ".") term; 
>            return (composeExprs xs)}

> term :: Parser Expr
> term = do space
>           c <- letter
>           cs <- many alphanum
>           if null cs
>              then return (Var c)
>              else do xs <- argument
>                      return (Con (c:cs) xs) 

> argument :: Parser [Expr]
> argument = tuple `orelse` (notuple `orelse` return [])

> tuple :: Parser [Expr]
> tuple = do symbol "("
>            xs <- somewith (symbol ",") expr
>            symbol ")"
>            return xs 

> notuple :: Parser [Expr]
> notuple = do space
>              c <- letter
>              cs <- many alphanum
>              if null cs
>                 then return [Var c]
>                 else return [Con (c:cs) []]

Parsing equations:

> parseEqn :: String -> (Expr, Expr)
> parseEqn = applyParser eqn

> eqn :: Parser (Expr, Expr)
> eqn = do space
>          x <- expr
>          symbol "="
>          y <- expr
>          return (x,y)


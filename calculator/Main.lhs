Chapter 12: An automatic calculator
Created: 19th Sept, 1997 by Richard Bird
Last modified: 6 Nov, 1998.

> module Main where
> import Calculations (Calculation,printCalc,printnCalc,pasteCalc)
> import Expressions (Expr,parseExpr,printExpr,parseEqn)
> import Laws (Law,basicLaw)
> import Rewrite (calculate)
> import Utilities (joinWith,splitBy)

This module defines two basic functions for conducting proofs:
The first is as on page 380 of the book, except that I have
replaced the name "partition" by "splitBy":

> simplify     :: [Law] -> String -> IO ()
> simplify laws = putStr . printCalc . calculate (basic, others) . 
>                 parseExpr
>                 where (basic, others) = splitBy basicLaw laws

The second is on page 379:

> prove     :: [Law] -> String -> IO ()
> prove laws = putStr . printCalc . 
>              proveEqn (basic,others) . parseEqn
>              where (basic, others) = splitBy basicLaw laws

> proveEqn :: ([Law], [Law]) -> (Expr, Expr) -> Calculation
> proveEqn pls (lhs,rhs)
>    = pasteCalc (calculate pls lhs) (calculate pls rhs)

------------------------------------------------------------------
Here are some useful test routines:

> putExpr :: String -> IO ()
> putExpr = putStr . printExpr . parseExpr

Both nprove and nsimplify make use of printnCalc, which
prints a given number of steps only.

> nprove :: Int -> [Law] -> String -> IO ()
> nprove n laws = putStr . printnCalc n . 
>                 proveEqn (splitBy basicLaw laws) . 
>                 parseEqn

> nsimplify :: Int -> [Law] -> String -> IO ()
> nsimplify n laws = putStr . printnCalc n . 
>                    calculate (splitBy basicLaw laws) . 
>                    parseExpr


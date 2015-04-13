> module Calculations where
> import Expressions (Expr,printExpr)
> import Laws (LawName)
> import Utilities (inits)

> type Calculation = (Expr, [Step])
> type Step        = (LawName, Expr)

The main purpose of this module is to define

> printCalc :: Calculation -> String
> printCalc (x,ss) = "\n  " ++ printExpr x ++ 
>                    "\n" ++ concat (map printStep ss)

> printnCalc :: Int -> Calculation -> String
> printnCalc n (x,ss) 
>          = "\n  " ++ printExpr x ++ 
>            "\n" ++ concat (map printStep (take n ss))

> printStep :: Step -> String
> printStep (why,x)  = "=   {" ++ why ++ "}\n" ++ 
>                      "  " ++ printExpr x ++ "\n"

The code is unsatisfactory because we really want to pretty
print calculations, so that expressions are broken across
lines in a meaningful way.

We also have to implement pasting two calculations together.

> pasteCalc :: Calculation -> Calculation -> Calculation
> pasteCalc lhc rhc 
>   = (fst lhc, snd lhc ++ link x y ++ shuffle rhc)
>     where x = conclusion lhc
>           y = conclusion rhc

> link :: Expr -> Expr -> [Step]
> link x y = if x == y then [] else [("... ??? ...", y)]

> shuffle :: Calculation -> [Step]
> shuffle (x, ss) = snd (foldl shunt (x,[]) ss)
>                   where shunt (x,rs) (r,y) = (y,(r,x):rs)

> conclusion :: Calculation -> Expr
> conclusion (x, steps) = if null steps then x 
>                         else snd (last steps)

The code for pasteCalc compares only final conclusions for 
equality. In some proofs, two intermediate expressions may 
be equal, thus shortening the proof. Unfortunately, what is 
given below seriously slows down the calculator:

*> pasteCalc :: Calculation -> Calculation -> Calculation
*> pasteCalc lhc rhc 
*>  = if conclusion lhc /= conclusion rhc
*>    then (fst lhc, [("... ??? ...", fst rhc)])
*>    else head [(fst phlc, snd phlc ++ shuffle prhc)
*>               | phlc <- precalcs lhc, prhc <- precalcs rhc,
*>                 conclusion phlc == conclusion prhc]

*> precalcs :: Calculation -> [Calculation]
*> precalcs (x,steps) = [(x,ss) | ss <- inits steps]

*> shuffle :: Calculation -> [Step]
*> shuffle (x, ss) = snd (foldl shunt (x,[]) ss)
*>                   where shunt (x,rs) (r,y) = (y,(r,x):rs)




> module MyParseLib
>    (Parser, plus, orelse, item, many, some, manywith, somewith,
>     sat, char, string, digit, lower, upper, letter, alphanum,
>     ident, space, token, symbol, applyParser) where

> newtype Parser a = MkP (String -> [(a,String)])

> papply :: Parser a -> String -> [(a,String)]
> papply (MkP f) s = f s

> instance Functor Parser where
>   map f p = MkP g
>             where g s = [(f x, s') | (x,s') <- papply p s]

> instance Monad Parser where
>   return x = MkP f  
>              where f s = [(x,s)]
>   p >>= q  = MkP f
>              where f s = [(y,s'') | (x,s')  <- papply p s,
>                                     (y,s'') <- papply (q x) s']

> instance MonadZero Parser where
>   zero = MkP f
>          where f s = []

> plus :: Parser a -> Parser a -> Parser a
> p `plus` q = MkP f
>              where f s = papply p s ++ papply q s


> orelse :: Parser a -> Parser a -> Parser a
> p `orelse` q = MkP f
>                where f s = if null rs then papply q s else rs
>                            where rs = papply p s

The primitive parser

> item :: Parser Char
> item = MkP f
>        where f []     = []
>              f (c:cs) = [(c,cs)]


> many :: Parser a -> Parser [a]
> many p = some p `orelse` return []

> some :: Parser a -> Parser [a]
> some p = do {x <- p; xs <- many p; return (x:xs)}

> manywith :: Parser b -> Parser a -> Parser [a]
> manywith q p = somewith q p `orelse` return []

> somewith :: Parser b -> Parser a -> Parser [a]
> somewith q p = do {x <- p; xs <- many (do {q;p}); return (x:xs)}

Some useful parsers

> sat :: (Char -> Bool) -> Parser Char
> sat p = do {c <- item; if p c then return c else zero}

> char :: Char -> Parser ()
> char x = do {sat (==x); return ()}

> string :: String -> Parser ()
> string []     = return ()
> string (c:cs) = do {char c; string cs; return ()}

> digit :: Parser Char
> digit = sat isDigit

> lower :: Parser Char
> lower = sat isLower

> upper :: Parser Char
> upper = sat isUpper

> letter :: Parser Char
> letter = sat isAlpha

> alphanum :: Parser Char
> alphanum = sat isAlphanum

> ident :: Parser String
> ident = do {c <- lower; cs <- many alphanum; return (c:cs)}

> space :: Parser ()
> space = many (sat isSpace) >> return ()

> token :: Parser a -> Parser a
> token p = do {space; x <- p; space; return x}

> symbol :: String -> Parser ()
> symbol = token . string

> applyParser :: Parser a -> String -> a
> applyParser p = fst . head . papply p








> module Examples where
> import Laws
> import Main

> pairs 
>  = map parseLaw [
>     "definition fst:      fst . pair (f,g) = f",
>     "definition snd:      snd . pair (f,g) = g",
>     "cross after pair:    cross (f,g) . pair (h,k) = pair (f.h, g.k)",
>     "cross functor:       cross (f,g) . cross (h,k) = cross (f.h, g.k)",
>     "pair absorption:     pair (f,g) . h = pair (f.h, g.h)"]

--     "definition cross:    cross (f,g) = pair (f.fst,g.snd)",

> ifs
>  = map parseLaw [
>    "if over composition:  if (p, f, g) . h = if (p.h, f.h, g.h)",
>    "composition over if:  h . if (p, f, g) = if (p, h . f, h . g)"]

> cases
>  = map parseLaw [
>    "definition case:      case (f,g) . Left = f",
>    "definition case:      case (f,g) . Right = g",
>    "plus functor:         case (f,g) . plus (h,k) = case (f.h, g.k)",
>    "definition plus:      plus (f,g) = case (Left.f, Right.g)",
>    "case absorption:      h . case (f,g) = case (h.f,h.g)"]

> tests
>  = map parseLaw [
>    "definition test:     case (f,g) . test True = f",
>    "definition test:     case (f,g) . test False = g",
>    "test leapfrog law:   test p . f = plus (f,f) . test (p.f)"]

> ids 
>  = map parseLaw [
>    "left-identity id:     id . f = f",
>    "right-identity id:    f . id = f"]

> maps
>  = map parseLaw [
>    "map functor:          map f . map g = map (f.g)",
>    "map identity:         map id = id"]

> nils
>  = map parseLaw [
>    "nil constant:         nil . f = nil",
>    "nil natural:          map f . nil = nil"]

> wraps
>  = map parseLaw [
>    "wrap natural:         map f . wrap = wrap . f",
>    "wrap singleton:       head . wrap = id"]

> concats
>  = map parseLaw [
>    "concat after nil:       concat . nil = nil",
>    "concat after wrap:      concat . wrap = id",
>    "concat after map wrap:  concat . map wrap = id",
>    "concat after concat:    concat . concat = concat . map concat",
>    "concat natural:         map f . concat = concat . map (map f)"]

> zips
>  = map parseLaw [
>    "definition unzip:     unzip = pair (map fst, map snd)", 
>    "zip inverse law:      zip . unzip = id",
>    "zip natural:          map (cross (f,g)) . zip = zip . cross (map f, map g)",
>    "unzip natural:        cross (map f, map g) . unzip = unzip . map (cross (f,g))",
>    "zip after pair:       zip . pair(map f, map g) = map (pair(f,g))"]

> filters
>  = map parseLaw [
>    "definition filter:    filter p = concat . map (box p)",
>    "definition box:       box p = if (p, wrap, nil)"]

> mss 
>  = map parseLaw [
>    "definition mss:       mss = listmax . map sum . segs",
>    "definition segs:      segs = concat . map inits . tails",
>    "definition listmax:   listmax = foldr1 max",
>    "definition sum:       sum = foldl (zero, add)"]

> scans = map parseLaw [
>         "definition scanl:    map (foldl (e,f)) . inits = scanl (e,f)",
>         "definition scanr:    map (foldr (e,f)) . tails = scanr (e,f)",
>         "fold-scan fusion:    foldr1 f . scanl (e,g) = foldr (e, join (f,g))",
>         "bookkeeping law:      foldr1 f . concat = foldr1 f . map (foldr1 f)"]

> parties 
>  = map parseLaw [
>    "definition party:    party   = best . parties",
>    "definition parties:  parties = cat . pair (aparties, bparties)",
>    "definition abparty:  abparty = pair (aparty, bparty)",
>    "definition aparty:   aparty  = best . aparties",
>    "definition bparty:   bparty  = best . bparties",
>    "definition aparties: aparties . Dept h = map (Cons h) . cp . map bparties",
>    "definition bparties: bparties . Dept h = cp . map parties",
>    "best after map:      best . map (Cons x) = Cons x . best",
>    "best over cp:        best . cp = concat . map best",
>    "best over cat:       best . cat = better . cross (best, best)"]


> others2 = map parseLaw [
>           "def abparty:  best.bparties = snd.abparty2",
>           "def abparty:  best.aparties = better.abparty2"]


> rose 
>  = map parseLaw [
>    "definition foldR:    foldR f . Node = f . cross (id, map (foldR f))",
>    "definition unfoldR:  unfoldR f = Node . cross (id, map (unfoldR f)) . f",
>    "definition hyloR:    foldR f . unfoldR g = hyloR (f,g)"]

> meertens
>  = map parseLaw [
>    "definition meertens: meertens = map fst . filter eq . flatten . gtree",
>    "definition flatten:  flatten  = foldR op",
>    "definition gtree:    gtree    = snip . unfoldR step . start",
>    "definition snip:     snip . Node = Node . cross (id, tail)",
>    "tail natural:        tail . map f = map f . tail"]

> idlist
>  = map parseLaw [
>    "id on lists:        idlist = map id"]

> basics = ids ++ pairs ++ ifs ++ cases ++ tests ++ maps ++ nils ++ wraps ++
>          zips ++ filters ++ concats

Example proofs:

> ex0 = prove pairs "cross (f,g) . pair (h,k) = pair (f.h, g.k)"
> ex1 = prove cases "plus (f,g) . plus (h,k) = plus (f.h,g.k)"
> ex2 = prove (basics++idlist) "filter p = map fst . filter snd . zip . pair (idlist,map p)"
> ex3 = simplify (mss++basics++scans) "mss"
> ex4 = simplify (parties++basics) "party"

> ex5 = simplify (basics++meertens++rose) "flatten . gtree"
> ex6 = prove basics "filter p . map f = map f . filter (p.f)"

> tx2 n = nprove n (basics++idlist) "filter p = map fst . filter snd . zip . pair (idlist,map p)"
> tx3 n = nsimplify n (mss++basics++scans) "mss"
> tx4 n = nsimplify n (parties++basics) "party"
> tx5 n = nsimplify n (basics++meertens++rose) "flatten . gtree"
> tx6 n = nprove n basics "filter p . map f = map f . filter (p.f)"

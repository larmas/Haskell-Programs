
We start with the given definitions:

     matchl = concat.map unify.cplist.map match
     unify  = foldr (concat.map union.cpr, wrap.nil)
     cplist = foldr (map cons.cpp, wrap.nil)

(matchlist is abbreviated to matchl.) Rather than use foldr,
we will define the second two functions recursively. This
will help to maintain the presence of informative names in 
calculations. The laws are:

> defs1 
>  = map parseLaw [
>    "def matchl:  matchl      = star unify.cplist.map match",
>    "def unify:   unify.nil   = wrap.nil",
>    "def unify:   unify.cons  = star union.cpr.cross(id,unify)",
>    "def cplist:  cplist.nil  = wrap.nil",
>    "def cplist:  cplist.cons = map cons.cpp.cross(id,cplist)"]

To keep expressions short in calculations, we have introduced the 
abbreviation

     star f = concat . map f

Some basic laws of star are:

> stars
>  = map parseLaw [
>    "star after map:    star f . map g = star (f . g)",
>    "star after concat: star f . concat = star (star f)",
>    "star after wrap:   star f . wrap = f",
>    "star after nil:    star f . nil = nil",
>    "star after star:   star (star f . g) = star f . star g"]

The "star after star" law is an easy consequence of "star after concat"
and "star after map".

Other basic laws are:

> ids
>  = map parseLaw [
>    "id left unit:       id.f = f",
>    "id right unit:      f.id = f"]

> functors
>  = map parseLaw [
>    "cross functor:  cross(f,g) . cross(h,k) = cross(f.h, g.k)",
>    "idpair rule:    cross(id,id) = id",
>    "map functor:    map f . map g = map (f.g)",
>    "map after nil:  map f . nil = nil",
>    "map after cons: map f . cons = cons . cross(f,map f)"]

Our aim now is to express matchl as an instance of foldr. For the proof 
we will need a claim:

> claims
>  = map parseLaw [
>    "claim: star (cpr.cross(id,g)).cpp = cpp.cross(id,star g)"]

To prove the claim, we use the following facts:

> cps = cpps ++ cpls ++ cprs

> cpps 
>  = map parseLaw [
>    "def cpp:          cpp = star cpr . cpl"]

> cpls
>  = map parseLaw [
>    "cpl after nil:    cpl . cross(nil,g) = nil",
>    "cpl after wrap:   cpl . cross(wrap,g) = wrap.cross(id,g)",
>    "cpl after map:    cpl . cross(map f, g) = map (cross(f,g)).cpl",
>    "cpl after concat: cpl . cross(concat,g) = star cpl . cpl",
>    "cpl after id:     cpl . cross(id,g) = map(cross(id,g)).cpl",
>    "cpl after star:   cpl . cross(star f,g) = star (cpl.cross(f,g)).cpl"]

> cprs
>  = map parseLaw [
>    "cpr after nil:    cpr . cross(f,nil) = nil",
>    "cpr after wrap:   cpr . cross(f,wrap) = wrap.cross(f,id)",
>    "cpr after map:    cpr . cross(f,map g) = map (cross(f,g)) . cpr",
>    "cpr after concat: cpr . cross(f,concat) = star cpr . cpr",
>    "cpr after id:     cpr . cross(f,id) = map (cross(f,id)).cpr",
>    "cpr after star:   cpr . cross(f,star g) = star (cpr.cross(f,g)).cpr"]

The "cpl after star" and "cpr after star" laws are easy consequences of the
associated "after concat" and "after map" laws. The "after id" laws are
instances of the corresponding "after map" laws, introduced to avoid the
use of the law id = map id.

> laws1 = stars ++ cps ++ ids ++ functors

> pf1 = prove laws1 "star (cpr.cross(id,g)).cpp = cpp.cross(id,star g)"

Now for the main proof:

> laws2 = defs1 ++ stars ++ claims ++ ids ++ functors

> pf2 = prove laws2 "matchl.nil  = wrap.nil"
> pf3 = prove laws2 "matchl.cons = star union.cpp.cross (match,matchl)"

We install the results as new laws:

> results1
>  = map parseLaw [
>    "matchl-1:  matchl.nil  = wrap.nil",
>    "matchl-2:  matchl.cons = cup.cross (match,matchl)"]

For brevity -- and for another reason -- we have introduced

     cup = star union . cpp

The point is that cup is associative and has wrap.nil as unit:

     cup (xs, cup (ys,zs)) = cup (cup (xs,ys), zs)
     cup (xs, [[]])        = xs
     cup ([[]],ys)         = ys

These laws are a consequence of the definition of union, and we will not
prove them. They are embodied as laws in the following form:

> cups
>  = map parseLaw [
>    "cup associative: cup.cross(id,cup.f) = cup.cross(cup,id).assl.cross(id,f)",
>    "right iden cup:  cup.cross(id,wrap.nil) = fst",
>    "left iden cup:   cup.cross(wrap.nil,id) = snd"]

The associative law for cup is really

      cup.cross(id,cup) = cup.cross(cup,id).assl

The form above is needed to avoid using the cross functor law in the 
backwards direction, thereby invoking a loop in calculations. 

The combinator assl satisfies  

     assl (a, (b,c)) = ((a,b),c)

Hence we have the naturality property:

> assls
>  = map parseLaw [
>    "assl natural:  assl.cross(f,cross(g,h)) = cross(cross(f,g),h).assl",
>    "assl help:     assl.cross(f,id) = cross(cross(f,id),id).assl"]

The second law is introduced to avoid using cross(id,id)=id in the reverse
direction.

Our aim now is to eliminate expensive computations of cup. To this end, 
we start by defining

> defs2
>  = map parseLaw [
>    "def matchlss:   matchlss = cup.cross (id, matchl)",
>    "def matchss:    matchss  = cup.cross (id, match)"]

> laws3 = results1 ++ defs2 ++ functors ++ ids ++ cups ++ assls

> pf4 = prove laws3 "matchlss.cross(id,nil)  = fst"
> pf5 = prove laws3 "matchlss.cross(id,cons) = matchlss.cross(matchss,id).assl"

At the point level, we have shown

        matchlss (ss,[]) = ss
        matchlss (ss,p:ps) = matchlss (matchss (ss,p),ps)

Hence curry matchlss = foldl (curry matchss). We install the results
as new laws:

> results2
>  = map parseLaw [
>    "matchlss-1: matchlss.cross(f,nil) = f.fst",
>    "matchlss-2: matchlss.cross(f,cons) = matchlss.cross(matchss,id).assl.cross(f,id)"]

These laws have been generalised to avoid using the cross functor law in the
reverse direction.

**************************************************************************
This is still not the result we are after because the first argument of
matchlss and matchss is a list of substitutions, whereas we want a single
substitution. The idea is to define

> defs3
>  = map parseLaw [
>    "def matchls:     matchls = star union.cpr.cross(id,matchl)",
>    "def matchs:      matchs  = star union.cpr.cross(id,match)"]

Compare these definitions to the definitions of matchlss and matchss,
restated by expanding the definition of cup in defs2:

> defs4
>  = map parseLaw [
>    "def matchlss:   matchlss = star union.cpp.cross (id, matchl)",
>    "def matchss:    matchss  = star union.cpp.cross (id, match)"]

We can express matchlss in terms of matchls, and matchss in terms of
matchs:

> laws4 = defs3 ++ defs4 ++ laws1

> pf6 = prove laws4 "matchlss = star matchls.cpl"
> pf7 = prove laws4 "matchss = star matchs.cpl"

We install these as new laws:

> results3
>  = map parseLaw [
>    "matchlss new: matchlss = star matchls.cpl",
>    "matchss new:  matchss = star matchs.cpl"]

Given these results, we can also express matchls in terms of matchlss,
and matchs in terms of matchss:

> laws5 = results3 ++ laws1

> pf8 = prove laws5 "matchls = matchlss.cross(wrap,id)"
> pf9 = prove laws5 "matchs  = matchss.cross(wrap,id)"

We install these results as new laws:

> results4
>  = map parseLaw [
>    "matchls new: matchls = matchlss.cross(wrap,id)",
>    "matchs new:  matchs  = matchss.cross(wrap,id)"]

Finally, we can show

> laws6 = results2 ++ results4 ++ ids ++ functors ++ assls

> pf10 = prove laws6 "matchls.cross(id,nil)  = wrap.fst"
> pf11 = prove laws6 "matchls.cross(id,cons) = matchlss.cross (matchs,id).assl"

Replacing matchlss by star matchls.cpl (see results3), we have obtained

    matchls (s, []) = [s]
    matchls (s, p:ps) = concat [matchls (t,ps) | t <- matchs (s,p)]

This concludes the calculation. What remains is to use the definition of match
(not used in the above calculations) to give a recursive definition of

   matchs (s,p) = concat [union (s,t) | t <- match p]

From   match (Var v,x) = [[(v,x)]]  and  union (s, [(v,x)]) = extend s (v,x),
we obtain

   match s (Var v,x) = extend s (v,x)

From  match (Con f xs, Var v) = [], we obtain

   match s (Con f xs, Var v) = []


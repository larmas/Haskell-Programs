
Here are the definitions we are interested in (match is abbreviated to mt,
and matchlist to mtl):

> defs 
>  = map parseLaw [
>    "def mtl:     mtl = concat.map unify.cplist.map mt",
>    "def unify:   unify.nil   = wrap.nil",
>    "def unify:   unify.cons  = star union.cpr.cross(id,unify)",
>    "def cplist:  cplist.nil  = wrap.nil",
>    "def cplist:  cplist.cons = map cons.cpp.cross(id,cplist)"]

The definitions of unify and cplist are equivalent to

     unify = foldr (star union.cpr, wrap.nil)
     cplist = foldr (map cons.cpp, wrap.nil)

To simplify expressions we will use the abbreviation

     star f = concat . map f

Some basic laws of star are:

> stars
>  = map parseLaw [
>    "star intro:        concat . map f = star f",
>    "star after map:    star f . map g = star (f . g)",
>    "star after star:   star (star f . g) = star f . star g",
>    "star after wrap:   star f . wrap = f",
>    "star after nil:    star f . nil = nil"]

Other basic laws are:

> ids
>  = map parseLaw [
>    "id left unit:   id.f = f",
>    "id right unit:  f.id = f"]

> functors
>  = map parseLaw [
>    "cross functor:  cross (f,g) . cross (h,k) = cross (f.h, g.k)",
>    "cross functor:  cross (id,id) = id",
>    "map functor:    map f . map g = map (f.g)",
>    "map functor:    map id = id",
>    "map after nil:  map f . nil = nil",
>    "map after cons: map f . cons = cons . cross (f, map f)"]


For the proof we will need a claim, which will be proved later on:

> claims
>  = map parseLaw [
>    "claim 1: star (cpr.cross (id,g)) . cpp = cpp . cross (id,star g)"]

> laws1 = defs ++ stars ++ claims ++ ids ++ functors

> pf1 = simplify laws1 "mtl.nil"
> pf2 = simplify laws1 "mtl.cons"


To prove the claim, we use the following facts:

> cps
>  = map parseLaw [
>    "def cpp:          cpp = star cpr . cpl",
>    "cpl natural:      cpl . cross (id,g) = map (cross (id,g)) . cpl",
>    "cpr natural:      cpr . cross (f,id) = map (cross (f,id)) . cpr",
>    "cpl after star:   cpl . cross (star f,id) = star (cpl.cross(f,id)).cpr",
>    "cpr after star:   cpr . cross (id,star g) = star (cpr.cross(id,g)).cpr"]

> laws2 = stars ++ cps ++ ids ++ functors

> pf3 = prove laws2 "star (cpr.cross (id,g)) . cpp = cpp . cross (id,star g)"

*************************************
Now for the second part of the proof!
*************************************

The definitions we are interested in, together with the derived 
equationsfor mtl, are:

> defs2
>  = map parseLaw [
>    "def mtl2:       mtl2 = star union.cpp.cross (id, mtl)",
>    "def m2:         mt2  = star union.cpp.cross (id, mt)",
>    "mtl after nil:  mtl.nil = wrap.nil",
>    "mtl after cons: mtl.cons = star union . cpp . cross (mt, mtl)"]

The next step is to introduce the useful abbreviation 

     cup = star union . cpp

cup is associative and has a unit, in the following sense:

> cups
>  = map parseLaw [
>    "cup intro:  star union . cpp = cup",
>    "cup associative: cup.cross (id,cup.f) = cup.cross(cup,id).assocl.cross(id,f)",
>    "right identity cup:  cup.cross (id, wrap.nil) = fst"]

The associative law for cup is, basically,

     cup.cross(id,cup) = cup.cross(cup,id).assocl

The form above is used to avoid using the cross functor rule in the other direction.

The combinator assocl satisfies  

     assocl (a, (b,c)) = ((a,b),c)

Hence

> assocls
>  = map parseLaw [
>    "assocl natural:  assocl.cross (f, cross (g,h)) = cross (cross (f,g),h).assocl"]


> laws3 = defs2 ++ functors ++ ids ++ cups ++ assocls

> pf4 = prove laws3 "mtl2.cross(id,nil)  = fst"
> pf5 = prove laws3 "mtl2.cross(id,cons) = mtl2.cross(mt2,id).assocl"

At the point level, we have shown

        mtl2 (ss,[]) = ss
        mtl2 (ss,p:ps) = mtl2 (mt2 (ss,p),ps)

Hence curry mtl2 = foldl (curry mt2).

**************************************
Now for the last part!
**************************************

Here are the definitions we are interested in, together with the derived equations
for mtl2

> defs4
>  = map parseLaw [
>    "def mtl3:     mtl3 = mtl2 . cross(wrap,id)",
>    "def mt3:      mt3  = mt2 . cross(wrap,id)",
>    "mtl2 on nil:  mtl2.cross(f,nil) = f.fst",
>    "mtl2 on cons: mtl2.cross(f,cons) = mtl2.cross(mt2,id).assocl.cross(f,id)"]

The equations for mtl2 have been generalised to avoid using cross functor laws in
reverse direction. Basically

     mtl2.cross(f,nil) = mtl2.cross(id,nil).cross(f,id) = fst.cross(f,id)=f.fst

Similarly for second equation. For the same reason, here is a generalised version of
the naturality of assocl:

> assocl2s
>  = map parseLaw [
>    "assocl natural: cross (f.cross(g,id),id).assocl = cross(f,id).assocl.cross(g,id)"]

> laws4 = defs4 ++ ids ++ functors ++ assocl2s

> pf6 = prove laws4 "mtl3.cross(id,nil)  = wrap.fst"
> pf7 = prove laws4 "mtl3.cross(id,cons) = mtl2 . cross (mt3,id).assocl"

Finally, we can express mtl2 in terms of mtl3:

 pf8 = prove       "mtl2=star mtl3 . cpl"
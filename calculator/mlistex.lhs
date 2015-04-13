To simplify expressions we will use the abbreviation

   star f = concat . map f

Some basic laws of star are:

> stars
>  = map parseLaw [
>    "star after map:      star f . map g = star (f . g)",
>    "star after star:     star (star f . g) = star f . star g",
>    "star after wrap:     star f . wrap = f",
>    "star after nil:      star f . nil = nil"]

Here are the definitions we are interested in:

> defs 
>  = map parseLaw [
>    "def mlist:     mlist   = star unify . cplist . map mt",
>    "def unify:     unify.nil   = wrap.nil",
>    "def unify:     unify.cons  = star union . cpr . cross (id, unify)",
>    "def cplist:    cplist.nil  = wrap.nil",
>    "def cplist:    cplist.cons = map cons . cpp . cross (id, cplist)"]

We will need a claim

> claims
>  = map parseLaw [
>    "claim 1: star (cpr.cross (id,g)) . cpp = cpp . cross (id,star g)"]

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

> laws1 = defs ++ stars ++ claims ++ ids ++ functors

> pf1 = simplify laws1 "mlist.nil"
> pf2 = simplify laws1 "mlist.cons"

The above is sufficient to prove  

> defs2
>  = map parseLaw [
>    "mlist after nil:  mlist.nil = wrap.nil",
>    "mlist after cons: mlist.cons = star union . cpp . cross (mt, mlist)"]


To prove the claim, we use

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

We first go for a different version:

> unions
>  = map parseLaw [
>    "def Union:   star union . cpp = Union",
>    "Union assoc: Union . cross (id,Union.f) = Union . cross (Union,id).assocl.cross(id,f)",
>    "assocl law:  assocl.cross (f, cross (g,h)) = cross (cross (f,g),h).assocl",
>    "Union iden:  Union . cross (id, wrap.nil) = fst"]

> defs3
>  = map parseLaw [
>    "def mlist2: mlist2 = Union . cross (id, mlist)",
>    "def m2:     Union . cross (id, mt) = mt2"]

> laws3 = defs2 ++ functors ++ ids ++ unions ++ defs3

> pf4 = prove laws3 "mlist2.cross(id,nil) = fst"
> pf5 = prove laws3 "mlist2.cross(id,cons) = mlist2.cross(mt2,id).assocl"

At the point level
        mlist2 (ss,[]) = ss
        mlist2 (ss,p:ps) = mlist2 (mt2 (ss,p),ps)

Hence the curried version of mlist2 satisfies  mlist2 = foldl mt2
But I now need to bring in the fast fold trick.

**************************************
Now for the last part!
**************************************

> defs4
>  = map parseLaw [
>    "def mlist2:  mlist2.cross(f,nil) = f.fst",
>    "def mlist2:  mlist2.cross(f,cons) = mlist2.cross(mt2,id).assocl.cross(f,id)",
>    "def mlist3:  mlist3 = mlist2 . cross (wrap,id)",
>    "def mt3:     mt3 = mt2 . cross (wrap,id)",
>    "mlist2 prop: star mlist3 . cpl = mlist2"]

> assocls
>  = map parseLaw [
>    "assocl prop:    cross (f.cross(g,id),id) . assocl = cross(f,id). assocl.cross(g,id)"]

> laws4 = defs4 ++ ids ++ functors ++ assocls

> pf6 = prove laws4 "mlist3.cross(id,nil) = wrap.fst"
> pf7 = prove laws4 "mlist3.cross(id,cons) = star mlist3 . cpl . cross (mt3,id).assocl"


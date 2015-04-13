> matchls 
>  = map parseLaw [
>    "def matchl:  matchl      = star unify.cplist.map match",
>    "def unify:   unify.nil   = wrap.nil",
>    "def unify:   unify.cons  = star union.cpr.cross(id,unify)",
>    "def cplist:  cplist.nil  = wrap.nil",
>    "def cplist:  cplist.cons = map cons.cpp.cross(id,cplist)"]

> matchxlss
>  = map parseLaw [
>    "def matchxls:   matchxls = star union.cpp.cross (id, matchl)",
>    "def matchxs:    matchxs  = star union.cpp.cross (id, match)"]

> matchxls
>  = map parseLaw [
>    "def matchxl:   matchxl   = matchxls.cross(wrap,id)",
>    "def matchx:    matchx    = matchxs.cross(wrap,id)"]

> laws1 = stars ++ cps ++ ids ++ functors 

> stars
>  = map parseLaw [
>    "star after map:    star f . map g = star (f . g)",
>    "star after concat: star f . concat = star (star f)",
>    "star after wrap:   star f . wrap = f",
>    "star after nil:    star f . nil = nil",
>    "star after star:   star (star f . g) = star f . star g"]

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

> ids
>  = map parseLaw [
>    "id left unit:       id.f = f",
>    "id right unit:      f.id = f"]

> functors
>  = map parseLaw [
>    "cross functor:  cross(f,g) . cross(h,k) = cross(f.h, g.k)",
>    "cross functor:  cross(id,id) = id",
>    "map functor:    map f . map g = map (f.g)",
>    "map after nil:  map f . nil = nil",
>    "map after cons: map f . cons = cons . cross(f,map f)"]

**************************************************************************

> claims
>  = map parseLaw [
>    "claim: star (cpr.cross(id,g)).cpp = cpp.cross(id,star g)"]

> pf1 = prove laws1 "star (cpr.cross(id,g)).cpp = cpp.cross(id,star g)"

> laws2 = matchls ++ laws1 ++ claims

> pf2 = prove laws2 "matchl.nil  = wrap.nil"
> pf3 = prove laws2 "matchl.cons = star union.cpp.cross (match,matchl)"

**************************************************************************

> newmatchls
>  = map parseLaw [
>    "matchl-1:  matchl.nil  = wrap.nil",
>    "matchl-2:  matchl.cons = star union.cpp.cross (match,matchl)"]

> cups
>  = map parseLaw [
>    "cup intro: star union.cpp = cup",
>    "cup assoc: cup.cross(id,cup.f) = cup.cross(cup,id).assl.cross(id,f)",
>    "iden cup:  cup.cross(id,wrap.nil) = fst",
>    "iden cup:  cup.cross(wrap.nil,id) = snd"]

> assls
>  = map parseLaw [
>    "assl natural:  assl.cross(f,cross(g,h)) = cross(cross(f,g),h).assl",
>    "assl help:     assl.cross(f,id) = cross(cross(f,id),id).assl"]

> laws3 = newmatchls ++ matchxlss ++ cups ++ assls ++ laws1

> pf4 = prove laws3 "matchxls.cross(id,nil)  = fst"
> pf5 = prove laws3 "matchxls.cross(id,cons) = matchxls.cross(matchxs,id).assl"

**************************************************************************

> newmatchxlss
>  = map parseLaw [
>    "matchxls-1: matchxls.cross(f,nil) = f.fst",
>    "matchxls-2: matchxls.cross(f,cons) = matchxls.cross(matchxs,id).assl.cross(f,id)"]

> laws4 = newmatchxlss ++ matchxls ++ assls ++ laws1

> pf6 = prove laws4 "matchxl.cross(id,nil)=wrap.fst"
> pf7 = prove laws4 "matchxl.cross(id,cons)=matchxls.cross(matchx,id).assl"

**************************************************************************

> originals
>  = map parseLaw [
>    "matchxl (original):   matchxl  = star union.cpr.cross(id,match)",
>    "matchxls (original):  matchxls = star union.cpp.cross(id,match)"]

> laws5 = originals ++ laws1

> pf8 = prove laws5 "matchxls = star matchxl.cpl"

**************************************************************************
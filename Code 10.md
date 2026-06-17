# Code 10: Irreducible 2-, 3-, and 5-modules for `A5 : S5`

## Purpose

Let

```text
G := Group((4,5)(9,10), (1,2,3,4,5), (6,7,8,9,10));
```

Then `Size(G)=7200` and GAP identifies `G` as `A5 : S5`.

This code checks every irreducible GF(2)-, GF(3)-, and GF(5)-module `V` for
`G`.  It verifies that no extension `V.G`, including split and non-split
extensions, can simultaneously satisfy:

1. `V.G` is rational;
2. `V.G` contains an element `x` such that `Size(Centralizer(V.G,x))=8` and
   the image of `x` in `G` has order exactly `4`.

The checks use the following reductions.

- For odd primes `p=3,5`, condition (2) forces the image `g` of `x` to act
  fixed-point-freely on `V`; otherwise `C_V(g)` already makes the centralizer
  too large.  If this necessary condition holds, rationality is first tested on
  the elements of `V`: for each `v in V`, all non-zero scalar multiples
  `k*v`, `Gcd(k,p)=1`, must lie in the same `G`-orbit.  The only GF(3) module
  passing these two necessary tests has `H^2(G,V)=0`, so its extension is split,
  and the split extension is not rational.
- For `p=2`, elements of `V` cause no rationality obstruction.  Condition (2)
  forces `Size(C_V(g)) <= 2` for some order-4 image `g`.  Modules failing this
  are discarded.  For the remaining modules with `H^2=0`, the split extension
  is checked directly and is not rational.  The only remaining module is the
  trivial 1-dimensional module, where `dim H^2(G,V)=3`; the code enumerates the
  eight central extension representatives and checks rationality and condition
  (2) directly.

## GAP Code

```gap
LoadPackage("cohomolo");;

IsRationalGroupFast := function(X)
    local c, rep, ord, k;

    for c in ConjugacyClasses(X) do
        rep := Representative(c);
        ord := Order(rep);

        for k in [2..ord-1] do
            if Gcd(k, ord) = 1 and not rep^k in c then
                return false;
            fi;
        od;
    od;

    return true;
end;;

FixedDimensionOnElement := function(rep, x, F)
    local mat, dim;

    mat := Image(rep, x);
    dim := Length(mat);
    return Length(NullspaceMat(mat - IdentityMat(dim, F)));
end;;

ScalarRationalOnModuleByOrbits := function(G, rep, p)
    local F, dim, mats, MG, V, orbits, orbit, v, k;

    F := GF(p);
    dim := Length(Image(rep, GeneratorsOfGroup(G)[1]));
    mats := List(GeneratorsOfGroup(G), g -> Image(rep, g));
    MG := Group(mats);
    V := FullRowSpace(F, dim);

    orbits := Orbits(MG, Elements(V), OnRight);

    for orbit in orbits do
        if Length(orbit) > 0 and not IsZero(orbit[1]) then
            v := orbit[1];

            for k in [2..p-1] do
                if Gcd(k, p) = 1 and not ((k * One(F)) * v) in orbit then
                    return false;
                fi;
            od;
        fi;
    od;

    return true;
end;;

HasCentralizer8WithImageOrder4 := function(Efp, isoPerm, Eperm, quotient)
    local c, rep, pre, img;

    for c in ConjugacyClasses(Eperm) do
        rep := Representative(c);
        pre := PreImagesRepresentative(isoPerm, rep);
        img := Image(quotient, pre);

        if Order(img) = 4 and Size(Centralizer(Eperm, rep)) = 8 then
            return true;
        fi;
    od;

    return false;
end;;

CheckOddPrimeModules := function(G, p, pres, mods)
    local F, reps, order4, i, rep, dim, fixedDims, fixedSizes,
          scalarRat, chr, h2, Ext, rational;

    F := GF(p);
    reps := IrreducibleRepresentations(G, F);
    order4 := List(Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) = 4), Representative);

    Print("============================================================\n");
    Print("GF(", p, ") irreducible modules\n");
    Print("number of modules: ", Length(reps), "\n");
    Print("order-4 classes in G: ", Length(order4), "\n\n");

    Print("ID | dim | fixed dims on order-4 classes | H2 | result\n");
    Print("--------------------------------------------------------\n");

    for i in [1..Length(reps)] do
        rep := reps[i];
        dim := Length(Image(rep, GeneratorsOfGroup(G)[1]));
        fixedDims := List(order4, x -> FixedDimensionOnElement(rep, x, F));
        fixedSizes := List(fixedDims, d -> p^d);

        chr := CHR(G, p, pres, mods[i].generators);
        h2 := SecondCohomologyDimension(chr);

        Print(String(i, 2), " | ",
              String(dim, 3), " | ",
              String(fixedDims, 20), " | ",
              String(h2, 2), " | ");

        if not 0 in fixedDims then
            Print("condition (2) impossible; fixed sizes=", fixedSizes, "\n");
        else
            scalarRat := ScalarRationalOnModuleByOrbits(G, rep, p);

            if not scalarRat then
                Print("not rational already on V\n");
            elif h2 = 0 then
                Ext := Image(IsomorphismPermGroup(SemidirectProduct(G, rep, F^dim)));
                rational := IsRationalGroupFast(Ext);

                Print("split only, extension rational=", rational, "\n");
            else
                Print("passes necessary tests but H2=", h2,
                      "; enumerate non-split extensions separately\n");
            fi;
        fi;
    od;

    Print("\n");
end;;

CheckTwoModules := function(G, pres, mods)
    local p, F, reps, order4, i, rep, dim, fixedDims, fixedSizes,
          chr, h2, Ext, rational;

    p := 2;
    F := GF(2);
    reps := IrreducibleRepresentations(G, F);
    order4 := List(Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) = 4), Representative);

    Print("============================================================\n");
    Print("GF(2) irreducible modules\n");
    Print("number of modules: ", Length(reps), "\n");
    Print("order-4 classes in G: ", Length(order4), "\n\n");

    Print("ID | dim | fixed dims on order-4 classes | fixed sizes | H2 | result\n");
    Print("---------------------------------------------------------------------\n");

    for i in [1..Length(reps)] do
        rep := reps[i];
        dim := Length(Image(rep, GeneratorsOfGroup(G)[1]));
        fixedDims := List(order4, x -> FixedDimensionOnElement(rep, x, F));
        fixedSizes := List(fixedDims, d -> 2^d);

        chr := CHR(G, 2, pres, mods[i].generators);
        h2 := SecondCohomologyDimension(chr);

        Print(String(i, 2), " | ",
              String(dim, 3), " | ",
              String(fixedDims, 20), " | ",
              String(fixedSizes, 12), " | ",
              String(h2, 2), " | ");

        if ForAll(fixedSizes, s -> s > 2) then
            Print("condition (2) impossible\n");
        elif h2 = 0 then
            Ext := Image(IsomorphismPermGroup(SemidirectProduct(G, rep, F^dim)));
            rational := IsRationalGroupFast(Ext);
            Print("split only, extension rational=", rational, "\n");
        elif dim = 1 then
            Print("central extensions checked below\n");
        else
            Print("condition (2) impossible for non-split candidates used here\n");
        fi;
    od;

    Print("\n");
end;;

CheckTrivialTwoModuleCentralExtensions := function(G, pres, moduleRec)
    local chr, vectors, vec, Efp, egens, qhom, iso, Eperm,
          rational, hit, ggens;

    chr := CHR(G, 2, pres, moduleRec.generators);
    ggens := GeneratorsOfGroup(G);

    vectors := Concatenation([[0, 0, 0]],
        Filtered(Tuples([0, 1], SecondCohomologyDimension(chr)),
            v -> v <> [0, 0, 0]));

    Print("============================================================\n");
    Print("GF(2) trivial module: central extension representatives\n");
    Print("dim H2 = ", SecondCohomologyDimension(chr), "\n\n");

    Print("cohomology vector | structure | rational | has target element\n");
    Print("------------------------------------------------------------\n");

    for vec in vectors do
        if vec = [0, 0, 0] then
            Efp := SplitExtensionCHR(chr);
        else
            Efp := NonsplitExtension(chr, vec);
        fi;

        egens := GeneratorsOfGroup(Efp);

        # In the presentation returned by cohomolo, the first three generators
        # lift the three chosen generators of G, and the last generator is V.
        qhom := GroupHomomorphismByImages(Efp, G, egens,
            [ggens[1], ggens[2], ggens[3], One(G)]);

        if qhom = fail then
            Error("Could not construct quotient map for vector ", vec);
        fi;

        iso := IsomorphismPermGroup(Efp);
        Eperm := Image(iso);
        rational := IsRationalGroupFast(Eperm);
        hit := HasCentralizer8WithImageOrder4(Efp, iso, Eperm, qhom);

        Print(String(vec, 16), " | ",
              StructureDescription(Eperm), " | ",
              rational, " | ", hit, "\n");
    od;

    Print("\n");
end;;

RunCode10 := function()
    local G, pres, mods2, mods3, mods5;

    G := Group((4,5)(9,10), (1,2,3,4,5), (6,7,8,9,10));

    Print("|G| = ", Size(G), "\n");
    Print("StructureDescription(G) = ", StructureDescription(G), "\n");
    Print("G is rational = ", IsRationalGroupFast(G), "\n");
    Print("centralizer sizes of order-4 classes in G = ",
          List(Filtered(ConjugacyClasses(G),
              c -> Order(Representative(c)) = 4),
              c -> Size(Centralizer(G, Representative(c)))), "\n\n");

    pres := Image(IsomorphismFpGroupByGenerators(G, GeneratorsOfGroup(G)));

    mods2 := IrreducibleModules(G, GF(2))[2];
    mods3 := IrreducibleModules(G, GF(3))[2];
    mods5 := IrreducibleModules(G, GF(5))[2];

    CheckOddPrimeModules(G, 3, pres, mods3);
    CheckOddPrimeModules(G, 5, pres, mods5);
    CheckTwoModules(G, pres, mods2);
    CheckTrivialTwoModuleCentralExtensions(G, pres, mods2[1]);
end;;

RunCode10();;
```
## Output

```text
|G| = 7200
StructureDescription(G) = A5 : S5
G is rational = true
centralizer sizes of order-4 classes in G = [ 24, 24, 8 ]

============================================================
GF(3) irreducible modules
number of modules: 14
order-4 classes in G: 3

ID | dim | fixed dims on order-4 classes | H2 | result
--------------------------------------------------------
 1 |   1 |          [ 1, 1, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 3, 3, 3 ]
 2 |   1 |          [ 0, 0, 0 ] |  0 | split only, extension rational=false
 3 |   4 |          [ 1, 3, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 3, 27, 3 ]
 4 |   4 |          [ 3, 1, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 27, 3, 3 ]
 5 |   4 |          [ 1, 1, 1 ] |  1 | condition (2) impossible; fixed sizes=[ 3, 3, 3 ]
 6 |   4 |          [ 1, 1, 1 ] |  1 | condition (2) impossible; fixed sizes=[ 3, 3, 3 ]
 7 |   6 |          [ 1, 3, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 3, 27, 3 ]
 8 |   6 |          [ 3, 1, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 27, 3, 3 ]
 9 |  16 |          [ 4, 4, 4 ] |  1 | condition (2) impossible; fixed sizes=[ 81, 81, 81 ]
10 |  16 |          [ 4, 4, 4 ] |  0 | condition (2) impossible; fixed sizes=[ 81, 81, 81 ]
11 |  18 |          [ 3, 3, 5 ] |  0 | condition (2) impossible; fixed sizes=[ 27, 27, 243 ]
12 |  18 |          [ 3, 3, 5 ] |  0 | condition (2) impossible; fixed sizes=[ 27, 27, 243 ]
13 |  24 |          [ 4, 6, 6 ] |  0 | condition (2) impossible; fixed sizes=[ 81, 729, 729 ]
14 |  24 |          [ 6, 4, 6 ] |  0 | condition (2) impossible; fixed sizes=[ 729, 81, 729 ]

============================================================
GF(5) irreducible modules
number of modules: 18
order-4 classes in G: 3

ID | dim | fixed dims on order-4 classes | H2 | result
--------------------------------------------------------
 1 |   1 |          [ 1, 1, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 5, 5, 5 ]
 2 |   1 |          [ 0, 0, 0 ] |  0 | not rational already on V
 3 |   3 |          [ 2, 0, 0 ] |  0 | not rational already on V
 4 |   3 |          [ 0, 2, 0 ] |  0 | not rational already on V
 5 |   3 |          [ 1, 1, 1 ] |  1 | condition (2) impossible; fixed sizes=[ 5, 5, 5 ]
 6 |   3 |          [ 1, 1, 1 ] |  1 | condition (2) impossible; fixed sizes=[ 5, 5, 5 ]
 7 |   5 |          [ 3, 1, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 125, 5, 5 ]
 8 |   5 |          [ 1, 3, 1 ] |  0 | condition (2) impossible; fixed sizes=[ 5, 125, 5 ]
 9 |   5 |          [ 2, 2, 2 ] |  0 | condition (2) impossible; fixed sizes=[ 25, 25, 25 ]
10 |   5 |          [ 2, 2, 2 ] |  0 | condition (2) impossible; fixed sizes=[ 25, 25, 25 ]
11 |   9 |          [ 1, 1, 3 ] |  1 | condition (2) impossible; fixed sizes=[ 5, 5, 125 ]
12 |   9 |          [ 2, 2, 2 ] |  0 | condition (2) impossible; fixed sizes=[ 25, 25, 25 ]
13 |  15 |          [ 2, 4, 4 ] |  0 | condition (2) impossible; fixed sizes=[ 25, 625, 625 ]
14 |  15 |          [ 4, 2, 4 ] |  0 | condition (2) impossible; fixed sizes=[ 625, 25, 625 ]
15 |  15 |          [ 3, 5, 3 ] |  0 | condition (2) impossible; fixed sizes=[ 125, 3125, 125 ]
16 |  15 |          [ 5, 3, 3 ] |  0 | condition (2) impossible; fixed sizes=[ 3125, 125, 125 ]
17 |  25 |          [ 7, 7, 7 ] |  0 | condition (2) impossible; fixed sizes=
[ 78125, 78125, 78125 ]
18 |  25 |          [ 8, 8, 6 ] |  0 | condition (2) impossible; fixed sizes=
[ 390625, 390625, 15625 ]

============================================================
GF(2) irreducible modules
number of modules: 10
order-4 classes in G: 3

ID | dim | fixed dims on order-4 classes | fixed sizes | H2 | result
---------------------------------------------------------------------
 1 |   1 |          [ 1, 1, 1 ] |  [ 2, 2, 2 ] |  3 | central extensions checked below
 2 |   4 |          [ 1, 3, 1 ] |  [ 2, 8, 2 ] |  0 | split only, extension rational=false
 3 |   4 |          [ 3, 1, 1 ] |  [ 8, 2, 2 ] |  0 | split only, extension rational=false
 4 |   4 |          [ 1, 2, 1 ] |  [ 2, 4, 2 ] |  0 | split only, extension rational=false
 5 |   4 |          [ 2, 1, 1 ] |  [ 4, 2, 2 ] |  0 | split only, extension rational=false
 6 |   8 |          [ 2, 2, 2 ] |  [ 4, 4, 4 ] |  1 | condition (2) impossible
 7 |   8 |          [ 2, 2, 2 ] |  [ 4, 4, 4 ] |  1 | condition (2) impossible
 8 |  16 |          [ 4, 4, 4 ] | [ 16, 16, 16 ] |  0 | condition (2) impossible
 9 |  16 |          [ 4, 4, 4 ] | [ 16, 16, 16 ] |  0 | condition (2) impossible
10 |  16 |          [ 4, 4, 4 ] | [ 16, 16, 16 ] |  0 | condition (2) impossible

============================================================
GF(2) trivial module: central extension representatives
dim H2 = 3

cohomology vector | structure | rational | has target element
------------------------------------------------------------
     [ 0, 0, 0 ] | C2 x (A5 : S5) | true | false
     [ 0, 0, 1 ] | SL(2,5) : S5 | false | false
     [ 0, 1, 0 ] | A5 : (A5 : C4) | false | false
     [ 0, 1, 1 ] | A5 : (C2 . S5 = SL(2,5) . C2) | false | false
     [ 1, 0, 0 ] | SL(2,5) : S5 | false | false
     [ 1, 0, 1 ] | SL(2,5) : S5 | false | false
     [ 1, 1, 0 ] | A5 : (C2 . S5 = SL(2,5) . C2) | false | false
     [ 1, 1, 1 ] | C2 . (A5 : S5) = (SL(2,5) : A5) . C2 | false | false
```


## Summary

The key output is:

```text
|G| = 7200
StructureDescription(G) = A5 : S5
G is rational = true
centralizer sizes of order-4 classes in G = [ 24, 24, 8 ]

GF(3):
Only module 2 has fixed dims [ 0, 0, 0 ].  It has H2=0 and its split
extension is not rational.  Every other module has non-trivial fixed points
for all order-4 classes, so condition (2) is impossible.

GF(5):
Modules 2, 3, and 4 have some order-4 class acting fixed-point-freely, but
each already fails rationality on V.  Every other module has non-trivial fixed
points for all order-4 classes, so condition (2) is impossible.

GF(2):
Modules 2, 3, 4, and 5 have H2=0 and the split extensions are not rational.
Modules 6 and 7 have non-zero H2, but every order-4 class has fixed-point
space size 4, so condition (2) is impossible.  Modules 8, 9, and 10 also have
fixed-point spaces too large.

For the trivial GF(2) module, dim H2=3.  The eight central extensions are:

[ 0, 0, 0 ] : C2 x (A5 : S5), rational=true, target element=false
[ 0, 0, 1 ] : SL(2,5) : S5, rational=false, target element=false
[ 0, 1, 0 ] : A5 : (A5 : C4), rational=false, target element=false
[ 0, 1, 1 ] : A5 : (C2 . S5 = SL(2,5) . C2), rational=false, target element=false
[ 1, 0, 0 ] : SL(2,5) : S5, rational=false, target element=false
[ 1, 0, 1 ] : SL(2,5) : S5, rational=false, target element=false
[ 1, 1, 0 ] : A5 : (C2 . S5 = SL(2,5) . C2), rational=false, target element=false
[ 1, 1, 1 ] : C2 . (A5 : S5) = (SL(2,5) : A5) . C2, rational=false, target element=false
```

Thus no irreducible 2-, 3-, or 5-module `V` gives an extension `V.G`, split or
non-split, satisfying both required conditions.

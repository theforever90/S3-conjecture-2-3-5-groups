# Code 11: Irreducible 2-, 3-, and 5-modules for `S6` and `Aut(A6)`

## Purpose

This code is used in Lemma 28, step (2.3).  It checks the following statement.

Let `G` be `S6` or `Aut(A6)`, and let `V` be an irreducible GF(2)-, GF(3)-, or
GF(5)-module for `G`.  No extension `V.G`, split or non-split, can satisfy both
conditions:

1. `V.G` is rational;
2. `V.G` contains an element whose centralizer has order `8`.

The output of `IrreducibleModules` and `IrreducibleRepresentations` may list
irreducible modules in a different order in different GAP sessions.  Therefore
the checks below do not use the displayed module number as part of the argument:
the relevant data are the dimension, fixed-point dimensions on the target
classes, `dim H^2(G,V)`, rationality, and the centralizer test.

## GAP Code

```gap
LoadPackage("cohomolo");;

IsRationalGroupFast := function(X)
    local c, rep, ord, k;

    for c in ConjugacyClasses(X) do
        rep := Representative(c);
        ord := Order(rep);

        for k in [2..ord-1] do
            if Gcd(k, ord) = 1 and not (rep^k in c) then
                return false;
            fi;
        od;
    od;

    return true;
end;;

HasCentralizerOfSize := function(X, n)
    local c;

    for c in ConjugacyClasses(X) do
        if Size(Centralizer(X, Representative(c))) = n then
            return true;
        fi;
    od;

    return false;
end;;

FixedDimensionFromMatrices := function(mats, gens, x, F)
    local hom, mat, dim;

    hom := GroupHomomorphismByImages(Group(gens), Group(mats), gens, mats);
    mat := Image(hom, x);
    dim := Length(mat);

    return Length(NullspaceMat(mat - IdentityMat(dim, F)));
end;;

ScalarRationalOnModule := function(mats, p)
    local F, MG, dim, V, orbits, orbit, v, k;

    F := GF(p);
    MG := Group(mats);
    dim := Length(mats[1]);
    V := FullRowSpace(F, dim);
    orbits := Orbits(MG, Elements(V), OnRight);

    for orbit in orbits do
        if Length(orbit) > 0 and not IsZero(orbit[1]) then
            v := orbit[1];

            for k in [2..p-1] do
                if Gcd(k, p) = 1 and not (((k * One(F)) * v) in orbit) then
                    return false;
                fi;
            od;
        fi;
    od;

    return true;
end;;

AllCohomologyVectors := function(p, d)
    return Tuples([0..p-1], d);
end;;

CheckExtensionRepresentatives := function(G, p, modrec)
    local chr, h2, vectors, vec, Efp, E, rational, cent8, countRatCent8;

    chr := CHR(G, p, 0, modrec.generators);
    h2 := SecondCohomologyDimension(chr);
    vectors := AllCohomologyVectors(p, h2);
    countRatCent8 := 0;

    Print("    extension representatives: ", Length(vectors), "\n");
    Print("    vector | rational | centralizer-8 test\n");
    Print("    --------------------------------------\n");

    for vec in vectors do
        if ForAll(vec, x -> x = 0) then
            Efp := SplitExtensionCHR(chr);
        else
            CalcPres(chr);
            Efp := NonsplitExtension(chr, vec);
        fi;

        E := Image(IsomorphismPermGroup(Efp));
        rational := IsRationalGroupFast(E);

        if rational then
            cent8 := HasCentralizerOfSize(E, 8);
            if cent8 then
                countRatCent8 := countRatCent8 + 1;
            fi;
            Print("    ", String(vec, 12), " | ", rational, " | ", cent8, "\n");
        else
            Print("    ", String(vec, 12), " | ", rational, " | skipped\n");
        fi;
    od;

    Print("    rational and centralizer-8 representatives: ", countRatCent8, "\n");
end;;

CheckPrime := function(G, name, p)
    local F, gens, mods, targetClasses, rows, i, modrec, dim, fixed, h2,
          scalarRat, row, sortedRows;

    F := GF(p);
    gens := GeneratorsOfGroup(G);
    mods := IrreducibleModules(G, F)[2];

    # In Lemma 28, step (2.3), the image of the element has 2-power order.
    # Thus only quotient classes of order 4 or 8 can contribute here.
    targetClasses := Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) in [4, 8] and
             Size(Centralizer(G, Representative(c))) <= 8);

    rows := [];

    for i in [1..Length(mods)] do
        modrec := mods[i];
        dim := modrec.dimension;
        fixed := List(targetClasses,
            c -> FixedDimensionFromMatrices(
                modrec.generators, gens, Representative(c), F));
        h2 := SecondCohomologyDimension(CHR(G, p, 0, modrec.generators));

        if p in [3, 5] then
            if ForAll(fixed, d -> d > 0) then
                row := [dim, fixed, h2, "condition (2) impossible"];
            else
                scalarRat := ScalarRationalOnModule(modrec.generators, p);
                if not scalarRat then
                    row := [dim, fixed, h2, "not rational already on V"];
                else
                    row := [dim, fixed, h2,
                        "needs direct extension check below"];
                fi;
            fi;
        else
            if ForAll(fixed, d -> d >= 2) then
                row := [dim, fixed, h2, "fixed space too large"];
            else
                row := [dim, fixed, h2,
                    "needs direct extension check below"];
            fi;
        fi;

        Add(rows, row);
    od;

    sortedRows := SortedList(rows);

    Print("============================================================\n");
    Print(name, " over GF(", p, ")\n");
    Print("number of irreducible modules: ", Length(mods), "\n");
    Print("target quotient classes: ",
          List(targetClasses, c -> [Order(Representative(c)),
              Size(Centralizer(G, Representative(c)))]), "\n\n");

    Print("dim | fixed dims on target classes | H2 | result\n");
    Print("------------------------------------------------\n");

    for row in sortedRows do
        Print(String(row[1], 3), " | ",
              String(row[2], 30), " | ",
              String(row[3], 2), " | ",
              row[4], "\n");
    od;

    Print("\n");
end;;

RunCode11Summary := function()
    local S6, AutA6;

    S6 := SymmetricGroup(6);
    AutA6 := Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6))));

    Print("S6 is rational = ", IsRationalGroupFast(S6), "\n");
    Print("Aut(A6) is rational = ", IsRationalGroupFast(AutA6), "\n\n");

    CheckPrime(S6, "S6", 2);
    CheckPrime(S6, "S6", 3);
    CheckPrime(S6, "S6", 5);

    CheckPrime(AutA6, "Aut(A6)", 2);
    CheckPrime(AutA6, "Aut(A6)", 3);
    CheckPrime(AutA6, "Aut(A6)", 5);
end;;

RunCode11Summary();;
```

For the rows marked `needs direct extension check below`, use the following
direct checks in the same GAP session.  They enumerate the relevant extension
representatives, including the zero vector, which is the split extension.

```gap
S6 := SymmetricGroup(6);;
AutA6 := Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6))));;

modsS6GF2 := IrreducibleModules(S6, GF(2))[2];;
modsS6GF3 := IrreducibleModules(S6, GF(3))[2];;
modsAutGF2 := IrreducibleModules(AutA6, GF(2))[2];;
modsAutGF3 := IrreducibleModules(AutA6, GF(3))[2];;

TargetClasses := function(G)
    return Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) in [4, 8] and
             Size(Centralizer(G, Representative(c))) <= 8);
end;;

NeedsDirectOddCheck := function(G, p, modrec)
    local F, gens, fixed;

    F := GF(p);
    gens := GeneratorsOfGroup(G);
    fixed := List(TargetClasses(G),
        c -> FixedDimensionFromMatrices(
            modrec.generators, gens, Representative(c), F));

    return 0 in fixed and ScalarRationalOnModule(modrec.generators, p);
end;;

Print("S6, GF(2), modules with dim H2 > 0\n");
for m in Filtered(modsS6GF2,
    x -> SecondCohomologyDimension(CHR(S6, 2, 0, x.generators)) > 0) do
    Print("  dim V = ", m.dimension, "\n");
    CheckExtensionRepresentatives(S6, 2, m);
od;

Print("S6, GF(3), modules needing direct extension checks\n");
for m in Filtered(modsS6GF3, x -> NeedsDirectOddCheck(S6, 3, x)) do
    Print("  dim V = ", m.dimension, "\n");
    CheckExtensionRepresentatives(S6, 3, m);
od;

Print("Aut(A6), GF(2), one-dimensional module with dim H2 > 0\n");
for m in Filtered(modsAutGF2,
    x -> x.dimension = 1 and
         SecondCohomologyDimension(CHR(AutA6, 2, 0, x.generators)) > 0) do
    Print("  dim V = ", m.dimension, "\n");
    CheckExtensionRepresentatives(AutA6, 2, m);
od;

Print("Aut(A6), GF(3), modules needing direct extension checks\n");
for m in Filtered(modsAutGF3, x -> NeedsDirectOddCheck(AutA6, 3, x)) do
    Print("  dim V = ", m.dimension, "\n");
    CheckExtensionRepresentatives(AutA6, 3, m);
od;
```

For `Aut(A6)` over GF(2), there is also an 8-dimensional irreducible module
with `dim H^2 = 1`.  The extension need not be constructed.  For every element
of order `4` or `8` in the quotient, the fixed-point space in `V` gives the
lower bound `|C_E(x)| > 8`.

```gap
AutA6 := Image(IsomorphismPermGroup(AutomorphismGroup(AlternatingGroup(6))));;
F := GF(2);;
mods := IrreducibleModules(AutA6, F)[2];;
mod8 := First(mods, m -> m.dimension = 8);;
gens := GeneratorsOfGroup(AutA6);;

Print("Aut(A6), GF(2), 8-dimensional module\n");
for c in Filtered(ConjugacyClasses(AutA6),
    c -> Order(Representative(c)) in [4, 8]) do
    Print("  order=", Order(Representative(c)),
          ", |C_G(g)|=", Size(Centralizer(AutA6, Representative(c))),
          ", dim C_V(g)=",
          FixedDimensionFromMatrices(mod8.generators, gens, Representative(c), F),
          "\n");
od;
```

## Output

The summary output is as follows.  The rows are sorted by their data, not by GAP
module number.

```text
S6 is rational = true
Aut(A6) is rational = true

============================================================
S6 over GF(2)
number of irreducible modules: 4
target quotient classes: [ [ 4, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                       [ 1, 1 ] |  2 | needs direct extension check below
  4 |                       [ 1, 1 ] |  1 | needs direct extension check below
  4 |                       [ 1, 1 ] |  1 | needs direct extension check below
 16 |                       [ 4, 4 ] |  0 | fixed space too large

============================================================
S6 over GF(3)
number of irreducible modules: 7
target quotient classes: [ [ 4, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                       [ 0, 1 ] |  1 | needs direct extension check below
  1 |                       [ 1, 1 ] |  0 | condition (2) impossible
  4 |                       [ 1, 0 ] |  0 | needs direct extension check below
  4 |                       [ 1, 0 ] |  0 | needs direct extension check below
  6 |                       [ 1, 2 ] |  1 | condition (2) impossible
  9 |                       [ 2, 3 ] |  0 | condition (2) impossible
  9 |                       [ 3, 3 ] |  0 | condition (2) impossible

============================================================
S6 over GF(5)
number of irreducible modules: 10
target quotient classes: [ [ 4, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                       [ 0, 1 ] |  0 | not rational already on V
  1 |                       [ 1, 1 ] |  0 | condition (2) impossible
  5 |                       [ 1, 1 ] |  0 | condition (2) impossible
  5 |                       [ 1, 1 ] |  0 | condition (2) impossible
  5 |                       [ 2, 1 ] |  0 | condition (2) impossible
  5 |                       [ 2, 1 ] |  0 | condition (2) impossible
  8 |                       [ 1, 2 ] |  0 | condition (2) impossible
  8 |                       [ 3, 2 ] |  1 | condition (2) impossible
 10 |                       [ 2, 2 ] |  0 | condition (2) impossible
 10 |                       [ 2, 2 ] |  0 | condition (2) impossible

============================================================
Aut(A6) over GF(2)
number of irreducible modules: 3
target quotient classes: [ [ 8, 8 ], [ 8, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                    [ 1, 1, 1 ] |  3 | needs direct extension check below
  8 |                    [ 1, 1, 2 ] |  1 | needs direct extension check below
 16 |                    [ 2, 2, 4 ] |  0 | fixed space too large

============================================================
Aut(A6) over GF(3)
number of irreducible modules: 11
target quotient classes: [ [ 8, 8 ], [ 8, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                    [ 0, 0, 0 ] |  0 | needs direct extension check below
  1 |                    [ 0, 1, 1 ] |  1 | needs direct extension check below
  1 |                    [ 1, 0, 0 ] |  0 | needs direct extension check below
  1 |                    [ 1, 1, 1 ] |  0 | condition (2) impossible
  6 |                    [ 0, 1, 1 ] |  0 | needs direct extension check below
  6 |                    [ 2, 1, 1 ] |  1 | condition (2) impossible
  8 |                    [ 0, 0, 2 ] |  0 | not rational already on V
  9 |                    [ 1, 1, 3 ] |  0 | condition (2) impossible
  9 |                    [ 1, 2, 2 ] |  0 | condition (2) impossible
  9 |                    [ 2, 1, 3 ] |  0 | condition (2) impossible
  9 |                    [ 2, 2, 2 ] |  0 | condition (2) impossible

============================================================
Aut(A6) over GF(5)
number of irreducible modules: 11
target quotient classes: [ [ 8, 8 ], [ 8, 8 ], [ 4, 8 ] ]

dim | fixed dims on target classes | H2 | result
------------------------------------------------
  1 |                    [ 0, 0, 0 ] |  0 | not rational already on V
  1 |                    [ 0, 1, 1 ] |  0 | not rational already on V
  1 |                    [ 1, 0, 0 ] |  0 | not rational already on V
  1 |                    [ 1, 1, 1 ] |  0 | condition (2) impossible
  8 |                    [ 1, 0, 2 ] |  0 | not rational already on V
  8 |                    [ 1, 0, 2 ] |  0 | not rational already on V
  8 |                    [ 1, 2, 2 ] |  0 | condition (2) impossible
  8 |                    [ 1, 2, 2 ] |  1 | condition (2) impossible
 10 |                    [ 1, 1, 3 ] |  0 | condition (2) impossible
 10 |                    [ 1, 1, 3 ] |  0 | condition (2) impossible
 20 |                    [ 2, 2, 4 ] |  0 | condition (2) impossible
```

The direct extension checks give the following output.

```text
S6, GF(2), modules with dim H2 > 0
  dim V = 1
    extension representatives: 4
    vector | rational | centralizer-8 test
    --------------------------------------
          [ 0, 0 ] | true  | false
          [ 0, 1 ] | false | skipped
          [ 1, 0 ] | false | skipped
          [ 1, 1 ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 4
    extension representatives: 2
    vector | rational | centralizer-8 test
    --------------------------------------
             [ 0 ] | false | skipped
             [ 1 ] | true | false
    rational and centralizer-8 representatives: 0
  dim V = 4
    extension representatives: 2
    vector | rational | centralizer-8 test
    --------------------------------------
             [ 0 ] | false | skipped
             [ 1 ] | true | false
    rational and centralizer-8 representatives: 0

S6, GF(3), modules needing direct extension checks
  dim V = 1
    extension representatives: 3
    vector | rational | centralizer-8 test
    --------------------------------------
             [ 0 ] | false | skipped
             [ 1 ] | false | skipped
             [ 2 ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 4
    extension representatives: 1
    vector | rational | centralizer-8 test
    --------------------------------------
              [  ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 4
    extension representatives: 1
    vector | rational | centralizer-8 test
    --------------------------------------
              [  ] | false | skipped
    rational and centralizer-8 representatives: 0

Aut(A6), GF(2), one-dimensional module with dim H2 > 0
  dim V = 1
    extension representatives: 8
    vector | rational | centralizer-8 test
    --------------------------------------
       [ 0, 0, 0 ] | true  | false
       [ 0, 0, 1 ] | false | skipped
       [ 0, 1, 0 ] | false | skipped
       [ 0, 1, 1 ] | false | skipped
       [ 1, 0, 0 ] | false | skipped
       [ 1, 0, 1 ] | false | skipped
       [ 1, 1, 0 ] | false | skipped
       [ 1, 1, 1 ] | false | skipped
    rational and centralizer-8 representatives: 0

Aut(A6), GF(3), modules needing direct extension checks
  dim V = 1
    extension representatives: 1
    vector | rational | centralizer-8 test
    --------------------------------------
              [  ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 1
    extension representatives: 3
    vector | rational | centralizer-8 test
    --------------------------------------
             [ 0 ] | false | skipped
             [ 1 ] | false | skipped
             [ 2 ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 1
    extension representatives: 1
    vector | rational | centralizer-8 test
    --------------------------------------
              [  ] | false | skipped
    rational and centralizer-8 representatives: 0
  dim V = 6
    extension representatives: 1
    vector | rational | centralizer-8 test
    --------------------------------------
              [  ] | false | skipped
    rational and centralizer-8 representatives: 0
```

The 8-dimensional GF(2)-module for `Aut(A6)` gives:

```text
Aut(A6), GF(2), 8-dimensional module
  order=4, |C_G(g)|=16, dim C_V(g)=2
  order=8, |C_G(g)|=8,  dim C_V(g)=1
  order=4, |C_G(g)|=8,  dim C_V(g)=2
  order=4, |C_G(g)|=16, dim C_V(g)=2
  order=8, |C_G(g)|=8,  dim C_V(g)=1
```

Thus for this module every lift has centralizer larger than `8`.

## Conclusion

For `S6` and `Aut(A6)`, every irreducible GF(2)-, GF(3)-, and GF(5)-module is
eliminated by one of the following checks:

- the fixed-point space on every relevant quotient class is already too large;
- the rationality condition fails on the elementary abelian normal subgroup `V`;
- direct enumeration of extension representatives shows that no rational
  extension contains an element with centralizer order `8`.

Therefore no such extension `V.G` exists.

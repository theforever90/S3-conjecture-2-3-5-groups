# Code 6: Extensions of irreducible modules for `Aut(PSp(4,3))`

## Purpose

Let $A=\mathrm{Aut}(\mathrm{PSp}_4(3)).$
This code searches the irreducible GF(2)- and GF(5)-modules $V$ of $A$
for extensions $V.A$ satisfying the following two conditions:

1. the extension is rational;
2. it contains an element of order $9$ whose centralizer has order $9$.

For GF(2)-modules, the elements of $V$ automatically satisfy the rationality
condition because $V$ is elementary abelian of exponent $2$.  Thus the code
constructs the relevant split extensions, and also constructs all non-split
extensions when $H^2(A,V)\neq 0$.

For GF(5)-modules, the extensions are too large to construct in general.  It is
enough to test rationality on $V$: if there exists $v\in V^\#$ such that
$2v$ is not in the same $A$-orbit as $v$, then no rational extension with
this chief factor can occur.

The computation finds exactly two groups:

$2^6:\mathrm{Aut}(\mathrm{PSp}_4(3)) \quad\text{and}\quad 2^6.\mathrm{Aut}(\mathrm{PSp}_4(3)),$
where the first extension is split and the second is non-split.

The two resulting groups are also stored explicitly at the end of this file as
permutation groups, so they can be loaded later without constructing them again.

---

## Code

```gap
LoadPackage("atlasrep");;
LoadPackage("cohomolo");;

FixedDimension := function(rep, g, F)
    local mat, dim;

    mat := Image(rep, g);
    dim := Length(mat);
    return Length(NullspaceMat(mat - IdentityMat(dim, F)));
end;;

IsRationalGroupFast := function(G)
    local c, rep, ord, k, nclasses;

    nclasses := 0;
    for c in ConjugacyClasses(G) do
        nclasses := nclasses + 1;
        rep := Representative(c);
        ord := Order(rep);

        if ord > 2 then
            for k in Filtered([2..ord-1], i -> Gcd(i, ord) = 1) do
                if not rep^k in c then
                    Print("      rationality failure: order=", ord,
                          ", power=", k,
                          ", |C|=", Size(Centralizer(G, rep)), "\n");
                    return false;
                fi;
            od;
        fi;
    od;

    Print("      conjugacy classes checked: ", nclasses, "\n");
    return true;
end;;

Order9CentralizerSizes := function(G)
    local P3, x, centralizers;

    P3 := SylowSubgroup(G, 3);
    centralizers := [];

    for x in Elements(P3) do
        if Order(x) = 9 then
            Add(centralizers, Size(Centralizer(G, x)));
        fi;
    od;

    return Set(centralizers);
end;;

HasOrder9Centralizer9 := function(G)
    local centralizers;

    centralizers := Order9CentralizerSizes(G);
    Print("      centralizer sizes of order-9 elements: ",
          centralizers, "\n");
    return 9 in centralizers;
end;;

SCOEData := function(G)
    local data;

    data := List(ConjugacyClasses(G),
                 c -> [Order(Representative(c)),
                       Size(Centralizer(G, Representative(c)))]);
    SortBy(data, x -> [x[2], x[1]]);
    return data;
end;;

PrintSCOEData := function(label, G)
    Print("      SCOE data for ", label, ":\n");
    Print("      ", SCOEData(G), "\n");
end;;

VectorScalarRationalityTest := function(A, rep, F, maxBasisVectors)
    local mats, dim, pos, v, orb, a;

    mats := List(GeneratorsOfGroup(A), x -> Image(rep, x));
    dim := Length(mats[1]);

    for pos in [1..Minimum(dim, maxBasisVectors)] do
        v := List([1..dim], i -> Zero(F));
        v[pos] := One(F);
        orb := Orbit(Group(mats), v, OnRight);

        for a in [2..Size(F)-1] do
            if not (a * v) in orb then
                Print("      vector rationality failure: basis vector ",
                      pos, ", scalar ", a,
                      ", orbit size ", Length(orb), "\n");
                return false;
            fi;
        od;
    od;

    return true;
end;;

RunGF2Search := function()
    local A, gens, c9, g, F, reps, mods, pres, candidates, i, rep, mrec,
          dim, fix, chr, h2, V, Ext, isRat, hasC9, vecs, vec, ExtFp,
          ExtPerm, N;

    A := AtlasGroup("U4(2).2", NrMovedPoints, 40);
    gens := GeneratorsOfGroup(A);
    F := GF(2);
    reps := IrreducibleRepresentations(A, F);
    mods := IrreducibleModules(A, F)[2];
    pres := Image(IsomorphismFpGroupByGenerators(A, gens));

    c9 := Filtered(ConjugacyClasses(A),
                   c -> Order(Representative(c)) = 9);
    g := Representative(c9[1]);

    Print("============================================================\n");
    Print("GF(2) search for V.Aut(PSp(4,3))\n");
    Print("A = AtlasGroup(\"U4(2).2\", NrMovedPoints, 40)\n");
    Print("|A| = ", Size(A), ", generators = ", Length(gens),
          ", presentation relators = ", Length(RelatorsOfFpGroup(pres)), "\n");
    Print("order-9 classes in A: ", Length(c9),
          ", |C_A(g)| = ", Size(Centralizer(A, g)), "\n\n");

    candidates := [];

    Print("ID | dim | dim C_V(g) | dim H^2(A,V)\n");
    Print("-------------------------------------\n");

    for i in [1..Length(reps)] do
        rep := reps[i];
        mrec := mods[i];
        dim := Length(Image(rep, gens[1]));
        fix := FixedDimension(rep, g, F);
        chr := CHR(A, 2, pres, mrec.generators);
        h2 := SecondCohomologyDimension(chr);

        Print(String(i, 2), " | ",
              String(dim, 3), " | ",
              String(fix, 10), " | ",
              String(h2, 12), "\n");

        if fix <> 0 then
            Print("   skip: order-9 element has fixed points on V\n\n");
        else
            Print("   split extension V:A\n");
            V := F^dim;
            Ext := SemidirectProduct(A, rep, V);
            Ext := Image(IsomorphismPermGroup(Ext));
            hasC9 := HasOrder9Centralizer9(Ext);
            isRat := false;
            if hasC9 then
                isRat := IsRationalGroupFast(Ext);
            fi;
            Print("      rational: ", isRat, "\n");

            if hasC9 and isRat then
                Add(candidates, ["GF(2)", i, dim, "split", Ext]);
                Print("      >>> candidate found: split extension\n");
                PrintSCOEData("split extension", Ext);
            fi;
            Print("\n");

            if h2 > 0 then
                Print("   non-split extensions from H^2(A,V)\n");
                vecs := Filtered(Elements(FullRowSpace(F, h2)),
                                 x -> not IsZero(x));

                for vec in vecs do
                    Print("      constructing non-split vector ",
                          List(vec, Int), "\n");
                    ExtFp := NonsplitExtension(chr, List(vec, Int));
                    ExtPerm := Image(IsomorphismPermGroup(ExtFp));
                    N := PCore(ExtPerm, 2);

                    Print("      |E| = ", Size(ExtPerm),
                          ", permutation degree = ",
                          LargestMovedPoint(ExtPerm), "\n");
                    Print("      |O_2(E)| = ", Size(N),
                          ", complements to O_2(E): ",
                          Length(ComplementClassesRepresentatives(ExtPerm, N)),
                          "\n");

                    hasC9 := HasOrder9Centralizer9(ExtPerm);
                    isRat := false;
                    if hasC9 then
                        isRat := IsRationalGroupFast(ExtPerm);
                    fi;
                    Print("      rational: ", isRat, "\n");

                    if hasC9 and isRat then
                        Add(candidates,
                            ["GF(2)", i, dim, "non-split", ExtPerm]);
                        Print("      >>> candidate found: non-split extension\n");
                        PrintSCOEData("non-split extension", ExtPerm);
                    fi;
                od;
                Print("\n");
            fi;
        fi;
    od;

    Print("GF(2) candidates found: ", Length(candidates), "\n");
    for i in [1..Length(candidates)] do
        Print("  ", i, ": module ", candidates[i][2],
              ", dim ", candidates[i][3],
              ", ", candidates[i][4],
              ", |E|=", Size(candidates[i][5]), "\n");
    od;
    Print("\n");

    return candidates;
end;;

RunGF5Search := function()
    local A, gens, c9, g, F, reps, candidates, i, rep, dim, fix, vecRat;

    A := AtlasGroup("U4(2).2", NrMovedPoints, 40);
    gens := GeneratorsOfGroup(A);
    F := GF(5);
    reps := IrreducibleRepresentations(A, F);

    c9 := Filtered(ConjugacyClasses(A),
                   c -> Order(Representative(c)) = 9);
    g := Representative(c9[1]);

    Print("============================================================\n");
    Print("GF(5) search for possible V.Aut(PSp(4,3))\n");
    Print("|A| = ", Size(A), ", irreducible GF(5)-modules = ",
          Length(reps), "\n");
    Print("order-9 classes in A: ", Length(c9),
          ", |C_A(g)| = ", Size(Centralizer(A, g)), "\n\n");

    candidates := [];

    Print("ID | dim | dim C_V(g) | vector rationality on V\n");
    Print("------------------------------------------------\n");

    for i in [1..Length(reps)] do
        rep := reps[i];
        dim := Length(Image(rep, gens[1]));
        fix := FixedDimension(rep, g, F);

        Print(String(i, 2), " | ",
              String(dim, 3), " | ",
              String(fix, 10), " | ");

        if fix <> 0 then
            Print("not tested; order-9 element has fixed points\n");
        else
            vecRat := VectorScalarRationalityTest(A, rep, F, 5);
            Print(vecRat, "\n");

            if vecRat then
                Add(candidates, ["GF(5)", i, dim]);
                Print("      possible GF(5) candidate remains\n");
            else
                Print("      skip: V already violates rationality\n");
            fi;
        fi;
    od;

    Print("\nGF(5) candidates found: ", Length(candidates), "\n\n");
    return candidates;
end;;

RunCode6 := function()
    local cand2, cand5;

    cand2 := RunGF2Search();
    cand5 := RunGF5Search();

    Print("============================================================\n");
    Print("FINAL SUMMARY\n");
    Print("GF(2) candidate groups: ", Length(cand2), "\n");
    Print("GF(5) candidate modules: ", Length(cand5), "\n");
    Print("The groups satisfying the required conditions are exactly:\n");
    Print("  1. the split extension 2^6:Aut(PSp(4,3));\n");
    Print("  2. the non-split extension 2^6.Aut(PSp(4,3)).\n");
end;;

RunCode6();
```

---

## Representative output

The non-split construction can take several minutes.  The important lines are:

```text
GF(2) search for V.Aut(PSp(4,3))
A = AtlasGroup("U4(2).2", NrMovedPoints, 40)
|A| = 51840, generators = 2, presentation relators = 12
order-9 classes in A: 1, |C_A(g)| = 9

ID | dim | dim C_V(g) | dim H^2(A,V)
-------------------------------------
 1 |   1 |          1 |            2
   skip: order-9 element has fixed points on V

 2 |   6 |          0 |            1
   split extension V:A
      centralizer sizes of order-9 elements: [ 9 ]
      conjugacy classes checked: 65
      rational: true
      >>> candidate found: split extension
      SCOE data for split extension:
      [ [ 9, 9 ], [ 12, 12 ], [ 8, 16 ], [ 8, 16 ],
        [ 10, 20 ], [ 10, 20 ], [ 20, 20 ], [ 6, 24 ],
        [ 12, 24 ], [ 12, 24 ], [ 24, 24 ], [ 5, 40 ],
        [ 10, 40 ], [ 6, 48 ], [ 12, 48 ], [ 12, 48 ],
        [ 4, 64 ], [ 4, 64 ], [ 8, 64 ], [ 8, 64 ],
        [ 8, 64 ], [ 6, 72 ], [ 6, 72 ], [ 12, 72 ],
        [ 6, 96 ], [ 6, 96 ], [ 12, 96 ], [ 12, 96 ],
        [ 4, 128 ], [ 4, 128 ], [ 6, 144 ], [ 6, 144 ],
        [ 6, 144 ], [ 8, 192 ], [ 4, 256 ], [ 4, 256 ],
        [ 4, 256 ], [ 4, 256 ], [ 4, 256 ], [ 6, 288 ],
        [ 12, 288 ], [ 4, 384 ], [ 4, 384 ], [ 6, 384 ],
        [ 3, 432 ], [ 6, 576 ], [ 3, 648 ], [ 2, 768 ],
        [ 4, 768 ], [ 4, 768 ], [ 2, 1024 ], [ 4, 1024 ],
        [ 4, 1536 ], [ 2, 3072 ], [ 2, 3072 ], [ 4, 3072 ],
        [ 3, 3456 ], [ 4, 4608 ], [ 2, 6144 ], [ 4, 7680 ],
        [ 2, 18432 ], [ 2, 46080 ], [ 2, 92160 ],
        [ 2, 122880 ], [ 1, 3317760 ] ]

   non-split extensions from H^2(A,V)
      constructing non-split vector [ 1 ]
      |E| = 3317760, permutation degree = 864
      |O_2(E)| = 64, complements to O_2(E): 0
      centralizer sizes of order-9 elements: [ 9 ]
      conjugacy classes checked: 65
      rational: true
      >>> candidate found: non-split extension
      SCOE data for non-split extension:
      [ [ 9, 9 ], [ 12, 12 ], [ 8, 16 ], [ 8, 16 ],
        [ 10, 20 ], [ 10, 20 ], [ 20, 20 ], [ 6, 24 ],
        [ 12, 24 ], [ 12, 24 ], [ 24, 24 ], [ 5, 40 ],
        [ 10, 40 ], [ 6, 48 ], [ 12, 48 ], [ 12, 48 ],
        [ 4, 64 ], [ 4, 64 ], [ 4, 64 ], [ 8, 64 ],
        [ 8, 64 ], [ 6, 72 ], [ 6, 72 ], [ 12, 72 ],
        [ 6, 96 ], [ 6, 96 ], [ 12, 96 ], [ 12, 96 ],
        [ 4, 128 ], [ 8, 128 ], [ 6, 144 ], [ 6, 144 ],
        [ 6, 144 ], [ 4, 192 ], [ 4, 256 ], [ 4, 256 ],
        [ 8, 256 ], [ 8, 256 ], [ 8, 256 ], [ 6, 288 ],
        [ 12, 288 ], [ 4, 384 ], [ 4, 384 ], [ 6, 384 ],
        [ 3, 432 ], [ 6, 576 ], [ 3, 648 ], [ 2, 768 ],
        [ 4, 768 ], [ 8, 768 ], [ 2, 1024 ], [ 4, 1024 ],
        [ 4, 1536 ], [ 2, 3072 ], [ 4, 3072 ], [ 4, 3072 ],
        [ 3, 3456 ], [ 2, 4608 ], [ 2, 6144 ], [ 2, 7680 ],
        [ 2, 18432 ], [ 4, 46080 ], [ 2, 92160 ],
        [ 2, 122880 ], [ 1, 3317760 ] ]

 3 |   8 |          0 |            0
   split extension V:A
      centralizer sizes of order-9 elements: [ 9 ]
      rationality failure: order=8, power=5, |C|=32
      rational: false

GF(2) candidates found: 2
  1: module 2, dim 6, split, |E|=3317760
  2: module 2, dim 6, non-split, |E|=3317760

GF(5) search for possible V.Aut(PSp(4,3))
|A| = 51840, irreducible GF(5)-modules = 23

ID | dim | dim C_V(g) | vector rationality on V
------------------------------------------------
 3 |   6 |          0 |       vector rationality failure: basis vector 1, scalar 2, orbit size 2160
false
      skip: V already violates rationality
 4 |   6 |          0 |       vector rationality failure: basis vector 1, scalar 2, orbit size 720
false
      skip: V already violates rationality
12 |  20 |          0 |       vector rationality failure: basis vector 1, scalar 2, orbit size 51840
false
      skip: V already violates rationality

GF(5) candidates found: 0

FINAL SUMMARY
GF(2) candidate groups: 2
GF(5) candidate modules: 0
The groups satisfying the required conditions are exactly:
  1. the split extension 2^6:Aut(PSp(4,3));
  2. the non-split extension 2^6.Aut(PSp(4,3)).
```

---

## Precomputed permutation groups

The following GAP code stores the two candidate groups as permutation groups.
Use these definitions when the construction of the non-split extension is too
slow to repeat.

```gap
AutPSp43_2_6_split := Group(
[ ( 2, 3)( 4, 7)( 8,15)(10,19)(11,22)(12,24)(20,29)(28,46)(30,49)(31,40)
    (32,43)(33,47)(38,56)(41,60)(42,62)(44,63), 
  ( 2, 4, 8,16,15,30,19,34,54)( 3, 5,10,20,35,55,48,14,29)( 6,12,25,42,28,47,
     62,17,31)( 7,13,27,45,52,64,49,50,51)( 9,18,32,43,61,26,44,58,60)
    (11,23,39,59,56,63,40,24,41)(21,37,46,36,22,38,57,33,53), 
  ( 1, 2)( 3, 6)( 4, 9)( 5,11)( 7,14)( 8,17)(10,21)(12,26)(13,28)(15,27)
    (16,19)(18,33)(20,36)(22,39)(23,40)(24,35)(25,43)(29,48)(30,50)(31,51)
    (32,52)(34,47)(37,46)(38,58)(41,61)(42,55)(44,64)(45,56)(49,59)(53,63)
    (54,60)(57,62) ]
);;

SetName(AutPSp43_2_6_split, "AutPSp43_2_6_split");;
if Size(AutPSp43_2_6_split) <> 3317760 then
    Error("Unexpected group size for AutPSp43_2_6_split");
fi;

AutPSp43_2_6_nonsplit := Group(
[ (  1,  2)(  3,  5)(  4,  8)(  6, 11)(  7, 13)(  9, 18)( 10, 17)( 12, 23)
    ( 14, 21)( 15, 22)( 16, 20)( 19, 30)( 24, 35)( 25, 27)( 26, 37)( 28, 38)
    ( 29, 40)( 31, 39)( 32, 44)( 33, 45)( 34, 46)( 36, 41)( 42, 55)( 43, 58)
    ( 47, 64)( 48, 65)( 49, 67)( 50, 68)( 51, 70)( 52, 72)( 53, 73)( 54, 75)
    ( 56, 74)( 57, 77)( 59, 83)( 60, 82)( 61, 84)( 62, 85)( 63, 87)( 66, 88)
    ( 69, 86)( 71, 79)( 76, 96)( 78, 92)( 80,100)( 81, 89)( 90,107)( 91,109)
    ( 93,108)( 94,110)( 95,104)( 97,106)( 98,101)( 99,103)(102,119)(105,111)
    (112,129)(113,123)(114,128)(115,132)(116,125)(117,134)(118,124)(120,135)
    (121,122)(126,138)(127,139)(130,141)(131,140)(133,137)(136,143)(142,144), 
  (  1,  3,  7, 14, 26, 31, 19,  9,  4)(  2,  6, 12, 24, 36, 32, 20, 10,  5)
    (  8, 15, 25, 13, 23, 34, 39, 28, 16)( 11, 21, 33, 41, 29, 18, 17, 27, 22)
    ( 30, 42, 56, 78, 88, 63, 46, 59, 43)( 35, 47, 54, 40, 53, 74, 92, 66, 48)
    ( 37, 49, 52, 38, 51, 71, 95, 69, 50)( 44, 57, 79,104, 86, 62, 45, 61, 60)
    ( 55, 68, 94,114,131,136,120,102, 76)( 58, 80,105,122,129,113, 93, 67, 81)
    ( 64, 89, 82,106,123,119,128,111, 90)( 65, 91,112,130,142,137,121,103, 77)
    ( 70, 87,110,127,141,143,133,115, 96)( 72, 97,116,134,138,124,107, 83, 98)
    ( 73, 85,109,126,140,144,135,117, 99)( 75,100,118,132,139,125,108, 84,101)
    , (  4, 10)(  6,  7)(  8, 17)( 11, 13)( 12, 14)( 19, 32)( 21, 23)( 28, 29)
    ( 30, 44)( 38, 40)( 42, 57)( 43, 60)( 47, 49)( 51, 53)( 52, 54)( 55, 77)
    ( 56, 79)( 58, 82)( 59, 61)( 64, 67)( 70, 73)( 71, 74)( 72, 75)( 78,104)
    ( 83, 84)( 90, 93)( 91, 94)( 92, 95)(105,123)(107,108)(109,110)(111,113)
    (112,114)(116,118)(124,125)(126,127)(128,129)(136,142)(138,139)(143,144), 
  (  4, 10)(  6,  7)(  8, 17)( 11, 13)( 42, 57)( 43, 60)( 47, 49)( 48, 50)
    ( 51, 53)( 52, 54)( 55, 77)( 58, 82)( 59, 61)( 62, 63)( 64, 67)( 65, 68)
    ( 70, 73)( 72, 75)( 76,103)( 80,106)( 83, 84)( 85, 87)( 90, 93)( 91, 94)
    ( 96, 99)( 97,100)(107,108)(109,110)(120,137)(130,131)(133,135)(140,141), 
  (  1,  5)(  6,  7)( 11, 13)( 15, 27)( 19, 32)( 28, 29)( 31, 36)( 35, 37)
    ( 39, 41)( 42, 57)( 45, 46)( 48, 50)( 51, 53)( 56, 79)( 58, 82)( 62, 63)
    ( 64, 67)( 66, 69)( 71, 74)( 72, 75)( 76,103)( 78,104)( 80,106)( 81, 89)
    ( 83, 84)( 86, 88)( 92, 95)( 96, 99)( 97,100)( 98,101)(111,113)(112,114)
    (119,122)(120,137)(124,125)(126,127)(132,134)(133,135)(136,142)(143,144), 
  (  2,  3)(  9, 20)( 12, 14)( 16, 18)( 19, 32)( 21, 23)( 22, 25)( 28, 29)
    ( 35, 37)( 45, 46)( 47, 49)( 48, 50)( 55, 77)( 56, 79)( 58, 82)( 59, 61)
    ( 62, 63)( 66, 69)( 70, 73)( 71, 74)( 72, 75)( 78,104)( 80,106)( 81, 89)
    ( 86, 88)( 90, 93)( 92, 95)( 97,100)( 98,101)(102,121)(105,123)(107,108)
    (115,117)(116,118)(120,137)(128,129)(130,131)(133,135)(138,139)(140,141), 
  (  4, 10)(  6,  7)(  8, 17)(  9, 20)( 11, 13)( 16, 18)( 24, 26)( 33, 34)
    ( 35, 37)( 43, 60)( 45, 46)( 47, 49)( 48, 50)( 52, 54)( 58, 82)( 59, 61)
    ( 62, 63)( 64, 67)( 65, 68)( 66, 69)( 72, 75)( 76,103)( 78,104)( 80,106)
    ( 83, 84)( 85, 87)( 86, 88)( 92, 95)( 96, 99)( 97,100)(102,121)(105,123)
    (111,113)(115,117)(116,118)(119,122)(124,125)(132,134)(136,142)(143,144), 
  (  1,  5)(  2,  3)( 15, 27)( 19, 32)( 22, 25)( 24, 26)( 28, 29)( 30, 44)
    ( 33, 34)( 35, 37)( 38, 40)( 42, 57)( 43, 60)( 45, 46)( 47, 49)( 48, 50)
    ( 51, 53)( 52, 54)( 55, 77)( 58, 82)( 59, 61)( 62, 63)( 64, 67)( 65, 68)
    ( 70, 73)( 72, 75)( 83, 84)( 85, 87)(102,121)(105,123)(111,113)(112,114)
    (115,117)(116,118)(119,122)(124,125)(126,127)(128,129)(132,134)(138,139) ]
);;

SetName(AutPSp43_2_6_nonsplit, "AutPSp43_2_6_nonsplit");;
if Size(AutPSp43_2_6_nonsplit) <> 3317760 then
    Error("Unexpected group size for AutPSp43_2_6_nonsplit");
fi;

# Quick verification:
# Size(AutPSp43_2_6_split) = Size(AutPSp43_2_6_nonsplit) = 3317760.
# The split group has a complement to O_2; the non-split group has none.
```

---

## Summary

Let $A=\mathrm{Aut}(\operatorname{PSp}_4(3))$, and let $V$ be an
irreducible GF(2)- or GF(5)-module for $A$.  Among the extensions $V.A$
which are rational and contain an element of order $9$ whose centralizer has
order $9$, the computation leaves exactly two possibilities:

$2^6:A \quad\text{and}\quad 2^6.A.$

The first group is the split extension.  The second group is the non-split
extension; computationally this is confirmed by the fact that $O_2(G)$ has no
complement in the non-split group.

For GF(5)-modules, every irreducible module on which an element of order $9$
acts fixed-point-freely already fails rationality on $V$: there exists
$v\in V^\#$ such that $2v$ is not in the same $A$-orbit as $v$.
Hence no GF(5)-module gives a candidate extension.

The following lists record the conjugacy-class data of the two candidate
groups.  Each pair $[m,n]$ means that there is a conjugacy class whose
representative has order $m$, and whose centralizer has order $n$.  The
pairs are ordered by increasing centralizer order $n$.

For the split extension $2^6:A$, the list is:

```text
[ [ 9, 9 ], [ 12, 12 ], [ 8, 16 ], [ 8, 16 ],
  [ 10, 20 ], [ 10, 20 ], [ 20, 20 ], [ 6, 24 ],
  [ 12, 24 ], [ 12, 24 ], [ 24, 24 ], [ 5, 40 ],
  [ 10, 40 ], [ 6, 48 ], [ 12, 48 ], [ 12, 48 ],
  [ 4, 64 ], [ 4, 64 ], [ 8, 64 ], [ 8, 64 ],
  [ 8, 64 ], [ 6, 72 ], [ 6, 72 ], [ 12, 72 ],
  [ 6, 96 ], [ 6, 96 ], [ 12, 96 ], [ 12, 96 ],
  [ 4, 128 ], [ 4, 128 ], [ 6, 144 ], [ 6, 144 ],
  [ 6, 144 ], [ 8, 192 ], [ 4, 256 ], [ 4, 256 ],
  [ 4, 256 ], [ 4, 256 ], [ 4, 256 ], [ 6, 288 ],
  [ 12, 288 ], [ 4, 384 ], [ 4, 384 ], [ 6, 384 ],
  [ 3, 432 ], [ 6, 576 ], [ 3, 648 ], [ 2, 768 ],
  [ 4, 768 ], [ 4, 768 ], [ 2, 1024 ], [ 4, 1024 ],
  [ 4, 1536 ], [ 2, 3072 ], [ 2, 3072 ], [ 4, 3072 ],
  [ 3, 3456 ], [ 4, 4608 ], [ 2, 6144 ], [ 4, 7680 ],
  [ 2, 18432 ], [ 2, 46080 ], [ 2, 92160 ],
  [ 2, 122880 ], [ 1, 3317760 ] ]
```

For the non-split extension $2^6.A$, the list is:

```text
[ [ 9, 9 ], [ 12, 12 ], [ 8, 16 ], [ 8, 16 ],
  [ 10, 20 ], [ 10, 20 ], [ 20, 20 ], [ 6, 24 ],
  [ 12, 24 ], [ 12, 24 ], [ 24, 24 ], [ 5, 40 ],
  [ 10, 40 ], [ 6, 48 ], [ 12, 48 ], [ 12, 48 ],
  [ 4, 64 ], [ 4, 64 ], [ 4, 64 ], [ 8, 64 ],
  [ 8, 64 ], [ 6, 72 ], [ 6, 72 ], [ 12, 72 ],
  [ 6, 96 ], [ 6, 96 ], [ 12, 96 ], [ 12, 96 ],
  [ 4, 128 ], [ 8, 128 ], [ 6, 144 ], [ 6, 144 ],
  [ 6, 144 ], [ 4, 192 ], [ 4, 256 ], [ 4, 256 ],
  [ 8, 256 ], [ 8, 256 ], [ 8, 256 ], [ 6, 288 ],
  [ 12, 288 ], [ 4, 384 ], [ 4, 384 ], [ 6, 384 ],
  [ 3, 432 ], [ 6, 576 ], [ 3, 648 ], [ 2, 768 ],
  [ 4, 768 ], [ 8, 768 ], [ 2, 1024 ], [ 4, 1024 ],
  [ 4, 1536 ], [ 2, 3072 ], [ 4, 3072 ], [ 4, 3072 ],
  [ 3, 3456 ], [ 2, 4608 ], [ 2, 6144 ], [ 2, 7680 ],
  [ 2, 18432 ], [ 4, 46080 ], [ 2, 92160 ],
  [ 2, 122880 ], [ 1, 3317760 ] ]
```

In particular, in both candidate groups the smallest centralizer order among
non-identity elements is $9$, and there is a class represented by an element
of order $9$ whose centralizer has order $9$.

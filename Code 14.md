# Code 14: Excluding `[1920,240993]` and `[1920,240996]`

## Purpose

This code is used to rule out the case

```text
G/N is isomorphic to SmallGroup(1920,240993) or SmallGroup(1920,240996).
```

Let `B` be one of these two groups.  If `D < N` is chosen so that `N/D` is a
chief factor of `G`, then `N/D` is an irreducible GF(3)- or GF(5)-module for
`B`.  The code checks that no extension of `B` by such a module can
simultaneously satisfy:

1. the extension is rational;
2. the extension contains an element whose centralizer has order `8`.

The computation is organized in two stages.

- First, for every irreducible GF(3)- and GF(5)-module, apply necessary tests:
  an element of `B` with centralizer `8` must act fixed-point-freely on the
  module, and the rationality condition must already hold on the elementary
  abelian normal subgroup.
- Second, for the few modules surviving these necessary tests, compute `H^2`.
  In all surviving cases `H^2=0`, so the extension is split; constructing these
  split extensions shows that they are not rational.

The numbering of irreducible modules can vary between GAP sessions.  The
argument uses dimensions and test results rather than module IDs.

## GAP Code

```gap
LoadPackage("cohomolo");;

IsRationalGroupFast := function(G)
    local c, rep, ord, k;

    for c in ConjugacyClasses(G) do
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

Centralizer8Data := function(G)
    local out, c, rep;

    out := [];

    for c in ConjugacyClasses(G) do
        rep := Representative(c);

        if Size(Centralizer(G, rep)) = 8 then
            Add(out, [Order(rep), Size(c)]);
        fi;
    od;

    return out;
end;;

FixedDimension := function(mats, gens, g, F)
    local hom, M, d;

    hom := GroupHomomorphismByImages(Group(gens), Group(mats), gens, mats);
    M := Image(hom, g);
    d := Length(M);

    return Length(NullspaceMat(M - IdentityMat(d, F)));
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

SplitExtensionFromMatrices := function(G, mats, p)
    local F, gens, dim, dperm, newgens, j, P, B, M, i;

    F := GF(p);
    gens := GeneratorsOfGroup(G);
    dim := Length(mats[1]);
    dperm := LargestMovedPoint(G);
    newgens := [];

    for j in [1..Length(gens)] do
        P := PermutationMat(gens[j], dperm, F);
        B := mats[j];
        M := NullMat(dperm + dim + 1, dperm + dim + 1, F);
        M{[1..dperm]}{[1..dperm]} := P;
        M{[dperm+1..dperm+dim]}{[dperm+1..dperm+dim]} := B;
        M[dperm+dim+1][dperm+dim+1] := One(F);
        Add(newgens, M);
    od;

    for i in [1..dim] do
        M := IdentityMat(dperm + dim + 1, F);
        M[dperm+dim+1][dperm+i] := One(F);
        Add(newgens, M);
    od;

    return Group(newgens);
end;;

AnalyzePrime := function(id, p)
    local G, F, gens, targets, mods, candidates, i, m, fixedDims, fixedFree,
          scalarRat, h2, E, cent8, row;

    G := Image(IsomorphismPermGroup(SmallGroup(1920, id)));
    F := GF(p);
    gens := GeneratorsOfGroup(G);
    targets := List(Filtered(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = 8), Representative);
    mods := IrreducibleModules(G, F)[2];
    candidates := [];

    Print("============================================================\n");
    Print("Base SmallGroup(1920,", id, "), GF(", p, ")\n");
    Print("base rational=", IsRationalGroupFast(G),
          ", target classes=", Length(targets), "\n");
    Print("number of irreducible modules=", Length(mods), "\n");
    Print("dim | fixed dims | scalar-rational | H2 | final check\n");
    Print("------------------------------------------------------\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        fixedDims := List(targets, g -> FixedDimension(m.generators, gens, g, F));
        fixedFree := 0 in fixedDims;
        scalarRat := "skipped";
        h2 := "skipped";
        row := "condition (centralizer 8) impossible";

        if fixedFree then
            scalarRat := ScalarRationalOnModule(m.generators, p);

            if scalarRat then
                h2 := SecondCohomologyDimension(CHR(G, p, 0, m.generators));

                if h2 = 0 then
                    E := SplitExtensionFromMatrices(G, m.generators, p);
                    cent8 := Centralizer8Data(E);
                    row := Concatenation("split: size=", String(Size(E)),
                        ", rational=", String(IsRationalGroupFast(E)),
                        ", hasCent8=", String(Length(cent8) > 0));
                else
                    row := Concatenation("passes necessary tests but H2=",
                        String(h2), "; enumerate extensions separately");
                fi;

                Add(candidates, [m.dimension, fixedDims, scalarRat, h2, row]);
            else
                row := "not rational already on V";
            fi;
        fi;

        Print(String(m.dimension, 3), " | ", String(fixedDims, 12), " | ",
              String(scalarRat, 15), " | ", String(h2, 7), " | ", row, "\n");
    od;

    Print("surviving necessary-test candidates=", Length(candidates), "\n\n");
end;;

RunCode14 := function()
    local p, id;

    for p in [3, 5] do
        for id in [240993, 240996] do
            AnalyzePrime(id, p);
        od;
    od;
end;;

RunCode14();;
```

## Output

The necessary-condition screening and split-extension checks give the following
surviving cases.

```text
GF(3):
SmallGroup(1920,240993): one 1-dimensional module survives the necessary tests;
  H2=0 and its split extension has size 5760, rational=false, hasCent8=true.
SmallGroup(1920,240996): one 1-dimensional module survives the necessary tests;
  H2=0 and its split extension has size 5760, rational=false, hasCent8=true.

GF(5):
For each of SmallGroup(1920,240993) and SmallGroup(1920,240996), only the
1-dimensional and 3-dimensional modules survive the necessary tests.
For these surviving modules H2=0, so all extensions are split.
```

The final split-extension rationality checks are:

```text
GF(3):
SmallGroup(1920,240996), dim 1: split extension size=5760, rational=false.
SmallGroup(1920,240993), dim 1: split extension size=5760, rational=false.

GF(5):
SmallGroup(1920,240996), dim 1: split extension size=9600, rational=false.
SmallGroup(1920,240996), dim 3: split extension size=240000, rational=false.
SmallGroup(1920,240996), dim 3: split extension size=240000, rational=false.
SmallGroup(1920,240993), dim 1: split extension size=9600, rational=false.
SmallGroup(1920,240993), dim 3: split extension size=240000, rational=false.
SmallGroup(1920,240993), dim 3: split extension size=240000, rational=false.
```

## Conclusion

For both `SmallGroup(1920,240993)` and `SmallGroup(1920,240996)`, every
irreducible GF(3)- or GF(5)-module is eliminated as follows:

- either a quotient element with centralizer `8` does not act fixed-point-freely,
  so a lift cannot have centralizer order `8`;
- or the rationality condition already fails on the module;
- or the module survives the necessary tests but has `H2=0`, and the resulting
  split extension is not rational.

Thus no extension by an irreducible 3- or 5-module can both be rational and
contain an element with centralizer of order `8`.

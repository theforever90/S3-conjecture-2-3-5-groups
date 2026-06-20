# Code 18: Modules for `(H : C2) x S5`

## Purpose

Let

```text
M/V = (H : C) x D,
```

where `H` is an elementary abelian 3-group, `C = C2`, `D = S5`, and
`C_H(C)=1`.  If `V` is a minimal normal `p`-subgroup of `M` for
`p in {2,5}`, then `V` is an irreducible module for `(H : C) x S5`.

The code verifies the three computational claims used in the proof.

1. For every irreducible GF(5)-module `V2` of `S5`, there is a vector `v` such
   that no element of `S5` sends `v` to `2v` or `3v`.
2. No extension of `C2 x S5` by an irreducible GF(2)-module can be both
   rational and contain an element whose centralizer has order `8`.
3. No extension of `S3 x S5` by an irreducible GF(2)-module can be both
   rational and contain an element whose centralizer has order `8`.

The numbering of irreducible modules may vary between GAP sessions.  The proof
uses the dimensions, cohomology dimensions, rationality checks, and centralizer
data, not the displayed module numbers.

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

HasCentralizerOfSize := function(G, n)
    return ForAny(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = n);
end;;

GoodVectorInModule := function(M)
    local F, d, V, zero, two, three, mats, A, v, orb;

    F := MTX.Field(M);
    d := MTX.Dimension(M);
    V := FullRowSpace(F, d);
    zero := Zero(V);
    two := 2 * One(F);
    three := 3 * One(F);
    mats := MTX.Generators(M);
    A := Group(mats);

    for v in Enumerator(V) do
        if v <> zero then
            orb := Orbit(A, v, OnRight);

            if not ((two * v) in orb) and not ((three * v) in orb) then
                return v;
            fi;
        fi;
    od;

    return fail;
end;;

RunS5GF5VectorCheck := function()
    local G, F, p, nPReg, mods, dims, i, M, v;

    G := SymmetricGroup(5);
    F := GF(5);
    p := 5;

    nPReg := Length(Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) mod p <> 0));
    mods := IrreducibleModules(G, F, 10)[2];
    dims := List(mods, M -> MTX.Dimension(M));

    Print("S5 GF(5) VECTOR CHECK\n");
    Print("G = S5, p = 5\n");
    Print("number of 5-regular conjugacy classes = ", nPReg, "\n");
    Print("number of irreducible GF(5)-modules found = ", Length(mods), "\n");
    Print("dimensions found = ", dims, "\n\n");

    for i in [1..Length(mods)] do
        M := mods[i];
        v := GoodVectorInModule(M);

        if v = fail then
            Error("failed for module ", i);
        fi;

        Print("  module ", i,
              ": dim=", MTX.Dimension(M),
              ", good vector=", v, "\n");
    od;

    Print("\nAll irreducible GF(5)-modules of S5 passed.\n\n");
end;;

CheckCentralExtensionsByC2 := function()
    local target, targetId, n, id, G, N, Q, rows, ratRows,
          centRows, row;

    target := DirectProduct(CyclicGroup(2), SymmetricGroup(5));;
    targetId := IdGroup(target);
    n := NrSmallGroups(480);

    rows := [];

    for id in [1..n] do
        G := SmallGroup(480, id);

        if not IsSolvableGroup(G) then
            for N in NormalSubgroups(G) do
                if Size(N) = 2 then
                    Q := G / N;

                    if Size(Q) = 240 and IdGroup(Q) = targetId then
                        Add(rows, [
                            id,
                            StructureDescription(G),
                            StructureDescription(N),
                            IsRationalGroupFast(G),
                            HasCentralizerOfSize(G, 8),
                            IdGroup(G)
                        ]);
                        break;
                    fi;
                fi;
            od;
        fi;
    od;

    ratRows := Filtered(rows, r -> r[4]);
    centRows := Filtered(rows, r -> r[5]);

    Print("C2 x S5: ORDER 480 SEARCH\n");
    Print("target IdGroup(C2 x S5) = ", targetId, "\n");
    Print("candidate groups = ", Length(rows), "\n");
    Print("rational candidates = ", Length(ratRows), "\n");

    for row in ratRows do
        Print("  SmallGroup(480,", row[1], ") structure=", row[2],
              " hasCent8=", row[5], " IdGroup=", row[6], "\n");
    od;

    Print("candidates with centralizer 8 = ", Length(centRows), "\n");
    Print("candidate IDs = ", List(rows, r -> r[1]), "\n");
    Print("rational IDs = ", List(ratRows, r -> r[1]), "\n");
    Print("centralizer-8 IDs = ", List(centRows, r -> r[1]), "\n\n");
end;;

CheckGF2Extensions := function(G, name)
    local F, mods, i, m, h2, vectors, chr, vec, Efp, E, cent8data;

    F := GF(2);
    mods := IrreducibleModules(G, F)[2];

    Print(name, ": GF(2) MODULES\n");
    Print("G order = ", Size(G), "\n");
    Print("number of irreducible GF(2)-modules = ", Length(mods), "\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        h2 := SecondCohomologyDimension(CHR(G, 2, 0, m.generators));

        Print("  module ", i, ": dim=", m.dimension,
              ", |V|=", 2^m.dimension,
              ", dimH2=", h2, "\n");
    od;

    Print("\n", name, ": EXTENSIONS\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        chr := CHR(G, 2, 0, m.generators);
        h2 := SecondCohomologyDimension(chr);
        vectors := Tuples([0, 1], h2);

        CalcPres(chr);

        Print("  module ", i, " dim=", m.dimension,
              " dimH2=", h2,
              " extension representatives=", Length(vectors), "\n");

        if name = "C2 x S5" and m.dimension = 1 then
            Print("    [all rational candidates occur in the order 480 search above]\n");
        else
            for vec in vectors do
                if ForAll(vec, x -> x = 0) then
                    Efp := SplitExtensionCHR(chr);
                else
                    Efp := NonsplitExtension(chr, vec);
                fi;

                E := Image(IsomorphismPermGroup(Efp));
                cent8data := Centralizer8Data(E);

                Print("    vector=", vec,
                      " size=", Size(E),
                      " rational=", IsRationalGroupFast(E),
                      " hasCent8=", Length(cent8data) > 0,
                      " cent8Data=", cent8data, "\n");
            od;
        fi;
    od;

    Print("\n");
end;;

RunCode18 := function()
    local C2xS5, S3xS5;

    RunS5GF5VectorCheck();

    CheckCentralExtensionsByC2();

    C2xS5 := DirectProduct(CyclicGroup(2), SymmetricGroup(5));;
    CheckGF2Extensions(C2xS5, "C2 x S5");

    S3xS5 := DirectProduct(SymmetricGroup(3), SymmetricGroup(5));;
    CheckGF2Extensions(S3xS5, "S3 x S5");
end;;

RunCode18();;
```

## Output

```text
S5 GF(5) VECTOR CHECK
G = S5, p = 5
number of 5-regular conjugacy classes = 6
number of irreducible GF(5)-modules found = 6
dimensions found = [ 1, 1, 3, 3, 5, 5 ]

  module 1: dim=1, good vector=[ Z(5)^0 ]
  module 2: dim=1, good vector=[ Z(5)^0 ]
  module 3: dim=3, good vector=[ 0*Z(5), 0*Z(5), Z(5)^0 ]
  module 4: dim=3, good vector=[ 0*Z(5), 0*Z(5), Z(5)^0 ]
  module 5: dim=5, good vector=[ 0*Z(5), 0*Z(5), 0*Z(5), 0*Z(5), Z(5)^0 ]
  module 6: dim=5, good vector=[ 0*Z(5), 0*Z(5), 0*Z(5), 0*Z(5), Z(5)^0 ]

All irreducible GF(5)-modules of S5 passed.

C2 x S5: ORDER 480 SEARCH
target IdGroup(C2 x S5) = [ 240, 189 ]
candidate groups = 12
rational candidates = 1
  SmallGroup(480,1186) structure=C2 x C2 x S5 hasCent8=false IdGroup=
[ 480, 1186 ]
candidates with centralizer 8 = 6
candidate IDs = [ 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 1186 ]
rational IDs = [ 1186 ]
centralizer-8 IDs = [ 944, 945, 947, 948, 951, 953 ]

C2 x S5: GF(2) MODULES
G order = 240
number of irreducible GF(2)-modules = 3
  module 1: dim=1, |V|=2, dimH2=4
  module 2: dim=4, |V|=16, dimH2=0
  module 3: dim=4, |V|=16, dimH2=1

C2 x S5: EXTENSIONS
  module 1 dim=1 dimH2=4 extension representatives=16
    [all rational candidates occur in the order 480 search above]
  module 2 dim=4 dimH2=0 extension representatives=1
    vector=[  ] size=3840 rational=true hasCent8=false cent8Data=[  ]
  module 3 dim=4 dimH2=1 extension representatives=2
    vector=[ 0 ] size=3840 rational=true hasCent8=false cent8Data=[  ]
    vector=[ 1 ] size=3840 rational=true hasCent8=false cent8Data=[  ]

S3 x S5: GF(2) MODULES
G order = 720
number of irreducible GF(2)-modules = 6
  module 1: dim=1, |V|=2, dimH2=4
  module 2: dim=2, |V|=4, dimH2=0
  module 3: dim=4, |V|=16, dimH2=0
  module 4: dim=4, |V|=16, dimH2=1
  module 5: dim=8, |V|=256, dimH2=0
  module 6: dim=8, |V|=256, dimH2=0

S3 x S5: EXTENSIONS
  module 1 dim=1 dimH2=4 extension representatives=16
    vector=[ 0, 0, 0, 0 ] size=1440 rational=true hasCent8=false cent8Data=[  ]
    vector=[ 0, 0, 0, 1 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 0, 1, 0 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 0, 1, 1 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 1, 0, 0 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 1, 0, 1 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 1, 1, 0 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 0, 1, 1, 1 ] size=1440 rational=false hasCent8=false cent8Data=[  ]
    vector=[ 1, 0, 0, 0 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 4, 180 ] ]
    vector=[ 1, 0, 0, 1 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 4, 180 ] ]
    vector=[ 1, 0, 1, 0 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 8, 180 ] ]
    vector=[ 1, 0, 1, 1 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 8, 180 ] ]
    vector=[ 1, 1, 0, 0 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 4, 180 ] ]
    vector=[ 1, 1, 0, 1 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 4, 180 ] ]
    vector=[ 1, 1, 1, 0 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 8, 180 ] ]
    vector=[ 1, 1, 1, 1 ] size=1440 rational=false hasCent8=true cent8Data=[ [ 8, 180 ] ]
  module 2 dim=2 dimH2=0 extension representatives=1
    vector=[  ] size=2880 rational=true hasCent8=false cent8Data=[  ]
  module 3 dim=4 dimH2=0 extension representatives=1
    vector=[  ] size=11520 rational=true hasCent8=false cent8Data=[  ]
  module 4 dim=4 dimH2=1 extension representatives=2
    vector=[ 0 ] size=11520 rational=true hasCent8=false cent8Data=[  ]
    vector=[ 1 ] size=11520 rational=true hasCent8=false cent8Data=[  ]
  module 5 dim=8 dimH2=0 extension representatives=1
    vector=[  ] size=184320 rational=true hasCent8=false cent8Data=[  ]
  module 6 dim=8 dimH2=0 extension representatives=1
    vector=[  ] size=184320 rational=true hasCent8=false cent8Data=[  ]
```

## Conclusion

For the GF(5) case, every irreducible `S5`-module has a vector whose orbit does
not contain either `2v` or `3v`, as required in the proof.

For the GF(2) case, the `C2 x S5` and `S3 x S5` extension searches show that no
extension is simultaneously rational and contains an element with centralizer
order `8`.  This excludes the two GF(2) subcases.

# Code 12: The case `V1.Gbar = C2 x S5`

## Purpose

This code is used in Lemma 28, step (2.4), for the subcase

```text
V1.Gbar is isomorphic to C2 x S5.
```

Here `V2` is an irreducible GF(2)-module for `V1.Gbar`.  GAP shows that the
irreducible GF(2)-modules for `C2 x S5` have dimensions `1, 4, 4`; hence
`|V2|=2` or `|V2|=16`.

The code verifies the two claims used in the proof.

1. If `|V2|=2`, then among all groups of order `480` with a normal subgroup
   `C2` and quotient `C2 x S5`, the only rational group is
   `C2 x C2 x S5`.  This group has no element whose centralizer has order `8`.
2. If `|V2|=16`, then all split and non-split extensions arising from the two
   4-dimensional irreducible GF(2)-modules for `C2 x S5` have no element whose
   centralizer has order `8`.

The numbering of irreducible modules may vary between GAP sessions.  The proof
uses the module dimensions and the extension data, not the displayed module
number.

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

HasCentralizerOfSize := function(G, n)
    return ForAny(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = n);
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

    Print("ORDER 480 SEARCH\n");
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

CheckGF2ModulesC2xS5 := function()
    local G, F, mods, i, m, h2, vectors, vec, chr, Efp, E, cent8data;

    # A permutation representation of C2 x S5.
    G := Group((1,2), (3,4), (3,4,5,6,7));;
    F := GF(2);
    mods := IrreducibleModules(G, F)[2];

    Print("GF(2) MODULES FOR C2 x S5\n");
    Print("number of irreducible modules = ", Length(mods), "\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        h2 := SecondCohomologyDimension(CHR(G, 2, 0, m.generators));

        Print("  module ", i, ": dim=", m.dimension,
              ", |V|=", 2^m.dimension,
              ", dimH2=", h2, "\n");
    od;

    Print("\nEXTENSIONS FOR 4-DIMENSIONAL MODULES\n");

    for i in [1..Length(mods)] do
        m := mods[i];

        if m.dimension = 4 then
            chr := CHR(G, 2, 0, m.generators);
            h2 := SecondCohomologyDimension(chr);
            vectors := Tuples([0, 1], h2);

            CalcPres(chr);

            Print("  module ", i, " dim=4 dimH2=", h2,
                  " extension representatives=", Length(vectors), "\n");

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
end;;

CheckCentralExtensionsByC2();;
CheckGF2ModulesC2xS5();;
```

## Output

```text
ORDER 480 SEARCH
target IdGroup(C2 x S5) = [ 240, 189 ]
candidate groups = 12
rational candidates = 1
  SmallGroup(480,1186) structure=C2 x C2 x S5 hasCent8=false IdGroup=
[ 480, 1186 ]
candidates with centralizer 8 = 6
candidate IDs = [ 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 1186 ]
rational IDs = [ 1186 ]
centralizer-8 IDs = [ 944, 945, 947, 948, 951, 953 ]

GF(2) MODULES FOR C2 x S5
number of irreducible modules = 3
  module 1: dim=1, |V|=2, dimH2=4
  module 2: dim=4, |V|=16, dimH2=0
  module 3: dim=4, |V|=16, dimH2=1

EXTENSIONS FOR 4-DIMENSIONAL MODULES
  module 2 dim=4 dimH2=0 extension representatives=1
    vector=[  ] size=3840 rational=true hasCent8=false cent8Data=[  ]
  module 3 dim=4 dimH2=1 extension representatives=2
    vector=[ 0 ] size=3840 rational=true hasCent8=false cent8Data=[  ]
    vector=[ 1 ] size=3840 rational=true hasCent8=false cent8Data=[  ]
```

## Summary

For `|V2|=2`, the only rational candidate is

```text
SmallGroup(480,1186) = C2 x C2 x S5,
```

and it has no element with centralizer order `8`.

For `|V2|=16`, the two 4-dimensional irreducible GF(2)-modules for
`C2 x S5` give three extension representatives in total: one for the module
with `dim H^2=0`, and two for the module with `dim H^2=1`.  All three have
`hasCent8=false`.  Hence no group in this subcase satisfies the required
centralizer condition.

# Code 13: The case `V1.S5 = [1920,240993]` or `[1920,240996]`

## Purpose

After the case
`V1.Gbar = C2 x S5` has been eliminated.

In this remaining case,

```text
V1.S5 is isomorphic to SmallGroup(1920,240993) or SmallGroup(1920,240996).
```

The code verifies the following claims.

1. For each of these two groups, the irreducible GF(2)-modules have dimensions
   `1, 4, 4`.  Hence `|V2|=2` or `|V2|=16`.
2. If `|V2|=2`, then the only rational extension is the split direct product
   `C2 x (V1.S5)`, and it has no element whose centralizer has order `8`.
   All non-split central extensions are not rational.
3. If `|V2|=16`, then `V2.V1.A5` is perfect.  The possible groups `G/N` are
   found by searching the perfect groups of order `15360`, then taking the
   relevant overgroups inside their automorphism groups.  None of the resulting
   groups is both rational and contains an element with centralizer order `8`.

The module IDs printed by GAP are not used in the proof; only dimensions,
cohomology dimensions, rationality, and centralizer data matter.

## Theoretical Reduction

Let `X = G/N` and suppose `V1.S5` is one of
`SmallGroup(1920,240993)` or `SmallGroup(1920,240996)`.

For `|V2|=2`, `V2` is a trivial central GF(2)-module.  Thus `X` is a central
extension of `V1.S5` by `C2`.  These are constructed using `H^2(V1.S5,C2)`.

For `|V2|=16`, both `V1` and `V2` are non-trivial 4-dimensional GF(2)-modules.
The subgroup

```text
K = V2.V1.A5
```

is perfect: the action of `A5` generates the two non-trivial module layers
through commutators, and the quotient by the 2-part is `A5`.  Hence `K` must
occur in the perfect group library.  Since `K` is normal in `X` and `X/K` has
order `2`, the possible `X` are obtained from suitable overgroups of `K` in
`Aut(K)`.  The code implements this by:

- scanning all perfect groups of order `15360`;
- keeping those with a normal abelian subgroup `V1V2` of order `256` and
  quotient `A5`;
- requiring a normal elementary abelian subgroup `V2` of order `16` inside
  `V1V2`;
- using involutions in `Out(K)` and pulling them back to `Aut(K)`;
- retaining only the overgroups whose quotient by the subgroup induced by
  `V1V2` is `S5`.

Each resulting group is then checked for rationality and for centralizer order
`8`.

## GAP Code

```gap
LoadPackage("hap");;

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

CheckIrreducibleGF2Modules := function()
    local id, B, mods, dims;

    Print("GF(2) irreducible module dimensions\n");

    for id in [240993, 240996] do
        B := Image(IsomorphismPermGroup(SmallGroup(1920, id)));
        mods := IrreducibleModules(B, GF(2))[2];
        dims := List(mods, m -> m.dimension);

        Print("SmallGroup(1920,", id, "): dimensions=", dims, "\n");
    od;

    Print("\n");
end;;

CheckV2Order2 := function()
    local ids, id, Bpc, B, Split, N, A, R, C, CH, H2, elts, zpos,
          pos, i, cocycle, E, Eperm, results, cent8;

    ids := [240993, 240996];

    Print("V2 order 2: central extensions of SmallGroup(1920,id)\n");

    for id in ids do
        Bpc := SmallGroup(1920, id);
        B := Image(IsomorphismPermGroup(Bpc));

        Split := DirectProduct(CyclicGroup(2), Bpc);
        cent8 := Centralizer8Data(Split);

        Print("Base SmallGroup(1920,", id, ") structure=",
              StructureDescription(Bpc),
              " rational=", IsRationalGroupFast(B),
              " baseHasCent8=", Length(Centralizer8Data(B)) > 0, "\n");

        Print("  split C2 x B: size=", Size(Split),
              " rational=", IsRationalGroupFast(Split),
              " hasCent8=", Length(cent8) > 0,
              " cent8Data=", cent8, "\n");

        N := Group((1,2));;
        A := TrivialGModuleAsGOuterGroup(B, N);;

        R := ResolutionFiniteGroup(B, 3);;
        C := HomToGModule(R, A);;
        CH := CohomologyModule(C, 2);;
        H2 := ActedGroup(CH);;

        elts := Elements(H2);;
        zpos := PositionProperty(elts, x -> x = One(H2));;
        pos := Filtered([1..Length(elts)], i -> i <> zpos);;

        Print("  H2 invariants=", AbelianInvariants(H2),
              " H2 size=", Size(H2),
              " nonsplit=", Length(pos), "\n");

        results := [];

        for i in pos do
            cocycle := CH!.representativeCocycle(elts[i]);
            E := CcGroup(A, cocycle);
            Eperm := Image(IsomorphismPermGroup(E));

            Add(results, [
                IsRationalGroupFast(Eperm),
                Length(Centralizer8Data(Eperm)) > 0
            ]);
        od;

        Print("  nonsplit [rational, hasCent8] results=", results, "\n");
    od;

    Print("\n");
end;;

FindAllCandidatesV2V1S5 := function()
    local numPerf, found, i, K, ns, V1V2s, V1V2, V2s,
          Aut, Inn, iso, AutP, InnP, InnV1V2, InnV1V2P,
          hom, OutP, classes2, c, g, Gout, G, Q, cent8, rat;

    numPerf := NumberPerfectGroups(15360);
    found := [];

    Print("PERFECT GROUP SEARCH\n");
    Print("NumberPerfectGroups(15360) = ", numPerf, "\n");

    for i in [1..numPerf] do
        K := PerfectGroup(15360, i);
        ns := NormalSubgroups(K);
        V1V2s := Filtered(ns, N -> Size(N) = 256 and IsAbelian(N));

        for V1V2 in V1V2s do
            if StructureDescription(K / V1V2) = "A5" then
                V2s := Filtered(ns,
                    N -> Size(N) = 16 and IsElementaryAbelian(N)
                         and IsSubgroup(V1V2, N));

                if Length(V2s) > 0 then
                    Print("  matched K=PerfectGroup(15360,", i, ") ",
                          "V1V2=", StructureDescription(V1V2),
                          " V2-count=", Length(V2s), "\n");

                    Aut := AutomorphismGroup(K);
                    Inn := InnerAutomorphismsAutomorphismGroup(Aut);
                    iso := IsomorphismPermGroup(Aut);
                    AutP := Image(iso);
                    InnP := Image(iso, Inn);

                    InnV1V2 := Subgroup(Aut,
                        List(GeneratorsOfGroup(V1V2),
                            v -> InnerAutomorphism(K, v)));
                    InnV1V2P := Image(iso, InnV1V2);

                    hom := NaturalHomomorphismByNormalSubgroup(AutP, InnP);
                    OutP := ImagesSource(hom);

                    Print("    |Aut(K)|=", Size(AutP),
                          " |Out(K)|=", Size(OutP), "\n");

                    classes2 := Filtered(ConjugacyClasses(OutP),
                        cl -> Order(Representative(cl)) = 2);

                    Print("    order-2 classes in Out(K): ",
                          Length(classes2), "\n");

                    for c in classes2 do
                        g := Representative(c);
                        Gout := Subgroup(OutP, [g]);
                        G := PreImage(hom, Gout);
                        Q := G / InnV1V2P;

                        if StructureDescription(Q) = "S5" then
                            rat := IsRationalGroupFast(G);
                            cent8 := Centralizer8Data(G);

                            Add(found, rec(
                                perfectId := i,
                                rational := rat,
                                hasCent8 := Length(cent8) > 0,
                                cent8Data := cent8,
                                orderAutSubgroup := Size(G)
                            ));

                            Print("    candidate ", Length(found),
                                  ": |G|=", Size(G),
                                  " quotient=", StructureDescription(Q),
                                  " rational=", rat,
                                  " hasCent8=", Length(cent8) > 0,
                                  " cent8Data=", cent8, "\n");
                        fi;
                    od;
                fi;
            fi;
        od;
    od;

    Print("total candidates = ", Length(found), "\n");
    Print("rational and hasCent8 candidates = ",
          Length(Filtered(found, r -> r.rational and r.hasCent8)), "\n");

    return found;
end;;

CheckIrreducibleGF2Modules();;
CheckV2Order2();;
candidates := FindAllCandidatesV2V1S5();;
```

## Output

```text
GF(2) irreducible module dimensions
SmallGroup(1920,240993): dimensions=[ 1, 4, 4 ]
SmallGroup(1920,240996): dimensions=[ 1, 4, 4 ]

V2 order 2: central extensions of SmallGroup(1920,id)
Base SmallGroup(1920,240993) structure=(C2 x C2 x C2 x C2) : S5 rational=true baseHasCent8=true
  split C2 x B: size=3840 rational=true hasCent8=false cent8Data=[  ]
  H2 invariants=[ 2, 2, 2 ] H2 size=8 nonsplit=7
  nonsplit [rational, hasCent8] results=[ [ false, false ], [ false, false ],
  [ false, false ], [ false, false ], [ false, false ], [ false, false ],
  [ false, false ] ]
Base SmallGroup(1920,240996) structure=(C2 x C2 x C2 x C2) : S5 rational=true baseHasCent8=true
  split C2 x B: size=3840 rational=true hasCent8=false cent8Data=[  ]
  H2 invariants=[ 2, 2, 2 ] H2 size=8 nonsplit=7
  nonsplit [rational, hasCent8] results=[ [ false, false ], [ false, true ],
  [ false, false ], [ false, true ], [ false, false ], [ false, true ],
  [ false, true ] ]

PERFECT GROUP SEARCH
NumberPerfectGroups(15360) = 7
  matched K=PerfectGroup(15360,3) V1V2=C2 x C2 x C2 x C2 x C2 x C2 x C2 x C2 V2-count=5
    |Aut(K)|=88473600 |Out(K)|=5760
    order-2 classes in Out(K): 3
    candidate 1: |G|=30720 quotient=S5 rational=true hasCent8=false cent8Data=[  ]
  matched K=PerfectGroup(15360,5) V1V2=C2 x C2 x C2 x C2 x C2 x C2 x C2 x C2 V2-count=2
    |Aut(K)|=368640 |Out(K)|=24
    order-2 classes in Out(K): 2
    candidate 2: |G|=30720 quotient=S5 rational=true hasCent8=false cent8Data=[  ]
  matched K=PerfectGroup(15360,6) V1V2=C2 x C2 x C2 x C2 x C2 x C2 x C2 x C2 V2-count=3
    |Aut(K)|=184320 |Out(K)|=12
    order-2 classes in Out(K): 3
    candidate 3: |G|=30720 quotient=S5 rational=true hasCent8=false cent8Data=[  ]
    candidate 4: |G|=30720 quotient=S5 rational=false hasCent8=false cent8Data=[  ]
  matched K=PerfectGroup(15360,7) V1V2=C4 x C4 x C4 x C4 V2-count=1
    |Aut(K)|=61440 |Out(K)|=4
    order-2 classes in Out(K): 3
    candidate 5: |G|=30720 quotient=S5 rational=false hasCent8=false cent8Data=[  ]
    candidate 6: |G|=30720 quotient=S5 rational=false hasCent8=false cent8Data=[  ]
total candidates = 6
rational and hasCent8 candidates = 0
```

## Summary

For both `SmallGroup(1920,240993)` and `SmallGroup(1920,240996)`, the
irreducible GF(2)-modules have dimensions `1,4,4`, so `|V2|=2` or `16`.

If `|V2|=2`, the split extension `C2 x (V1.S5)` is rational but has no element
with centralizer order `8`; every non-split central extension is not rational.

If `|V2|=16`, the perfect group search gives six possible groups `G/N`.  Three
of them are rational, but none has an element with centralizer order `8`; the
remaining three are not rational.  Hence no group in this case satisfies both
required conditions.

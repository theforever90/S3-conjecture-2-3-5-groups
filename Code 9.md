# Code 9: Groups between $A_5\times A_6$ and $\mathrm{Aut}(A_5)\times\mathrm{Aut}(A_6)$

## Purpose

Let

$$
R=A_5\times A_6,\qquad
A=\mathrm{Aut}(A_5)\times \mathrm{Aut}(A_6).
$$

This code enumerates all groups $G$ satisfying

$$
R\leq G\leq A
$$

and finds those which are rational and contain an element $x$ such that

$$
|C_G(x)|=4 \quad\text{or}\quad |C_G(x)|=8.
$$

The computation finds no such group.  If the rationality condition is omitted,
there is exactly one group with a centralizer of order `4` or `8`; it has order
`43200`, index `4` in $A$, and contains one conjugacy class whose
representatives have order `4` and centralizer order `8`.  This group is not
rational.

## GAP Code

```gap
CentralizerHits := function(G, targetSizes)
    local hits, classes, c, rep, centSize;

    hits := [];
    classes := ConjugacyClasses(G);

    for c in classes do
        rep := Representative(c);
        centSize := Size(Centralizer(G, rep));

        if centSize in targetSizes then
            Add(hits, rec(
                representative := rep,
                element_order := Order(rep),
                centralizer_order := centSize,
                class_size := Size(c)
            ));
        fi;
    od;

    return hits;
end;;

IsRationalGroupFast := function(G)
    local c, rep, ord, k;

    for c in ConjugacyClasses(G) do
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

ConstructA5xA6Interval := function()
    local AutA5, A5, A6Abstract, AutA6Abstract, isoAutA6,
          AutA6, A6, A, emb1, emb2, R;

    AutA5 := SymmetricGroup(5);
    A5 := AlternatingGroup(5);

    A6Abstract := AlternatingGroup(6);
    AutA6Abstract := AutomorphismGroup(A6Abstract);
    isoAutA6 := IsomorphismPermGroup(AutA6Abstract);
    AutA6 := Image(isoAutA6);

    # The copy of A6 inside Aut(A6) is the derived subgroup.
    A6 := DerivedSubgroup(AutA6);

    A := DirectProduct(AutA5, AutA6);
    emb1 := Embedding(A, 1);
    emb2 := Embedding(A, 2);

    R := ClosureGroup(Image(emb1, A5), Image(emb2, A6));

    return rec(R := R, A := A);
end;;

FindRationalIntermediateGroupsWithSmallCentralizer := function()
    local interval, R, A, inter, candidates, records, nonRationalHits,
          targetSizes, i, G, hits, hit, isRational;

    interval := ConstructA5xA6Interval();
    R := interval.R;
    A := interval.A;

    Print("R size: ", Size(R), "\n");
    Print("A size: ", Size(A), "\n");
    Print("A/R index: ", Size(A) / Size(R), "\n");

    inter := IntermediateSubgroups(A, R);
    candidates := Concatenation([R], inter.subgroups, [A]);
    targetSizes := [4, 8];
    records := [];
    nonRationalHits := [];

    Print("candidate count: ", Length(candidates), "\n");

    for i in [1..Length(candidates)] do
        G := candidates[i];
        hits := CentralizerHits(G, targetSizes);

        if Length(hits) > 0 then
            isRational := IsRationalGroupFast(G);

            if isRational then
                Add(records, rec(
                    candidate_index := i,
                    group := G,
                    order := Size(G),
                    index_in_top := Index(A, G),
                    structure := StructureDescription(G),
                    generators := GeneratorsOfGroup(G),
                    hits := hits
                ));

                Print("rational hit group ", Length(records),
                      ": candidate index=", i,
                      ", order=", Size(G),
                      ", index in A=", Index(A, G),
                      ", structure=", StructureDescription(G), "\n");

                for hit in hits do
                    Print("  element order=", hit.element_order,
                          ", centralizer order=", hit.centralizer_order,
                          ", class size=", hit.class_size, "\n");
                od;
            else
                Add(nonRationalHits, rec(
                    candidate_index := i,
                    group := G,
                    order := Size(G),
                    index_in_top := Index(A, G),
                    structure := StructureDescription(G),
                    generators := GeneratorsOfGroup(G),
                    hits := hits
                ));

                Print("non-rational group with small centralizer",
                      ": candidate index=", i,
                      ", order=", Size(G),
                      ", index in A=", Index(A, G),
                      ", structure=", StructureDescription(G), "\n");

                for hit in hits do
                    Print("  element order=", hit.element_order,
                          ", centralizer order=", hit.centralizer_order,
                          ", class size=", hit.class_size, "\n");
                od;
            fi;
        fi;
    od;

    Print("rational hit group count: ", Length(records), "\n");
    Print("non-rational hit group count: ", Length(nonRationalHits), "\n");

    return rec(R := R, A := A, candidates := candidates,
               records := records, non_rational_hits := nonRationalHits);
end;;

result := FindRationalIntermediateGroupsWithSmallCentralizer();;
```

The rational groups satisfying the condition are saved in

```gap
result.records
```

In this computation, `result.records` is empty.  The groups which have a
centralizer of order `4` or `8` but fail rationality are saved in

```gap
result.non_rational_hits
```

## The Only Non-Rational Group with a Small Centralizer

If rationality is not imposed, the unique group found by the search has the
following permutation construction:

```gap
Code9NonRationalHitGroup := Group(
    ( 4, 5)( 6,34,79,57,22,75,13,85)( 7,63,67,73,25,37,11,56)
    ( 8,51,78,40,32,71,16,60)( 9,83,66,58,35,52,15,39)
    (10,31,55,27,62,80,23,46)(12,68,54,48,74,30,20,28)
    (14,69,41,36,29,81,26,33)(17,61,53,76,50,59,38,64)
    (18,70,77,72,21,49,43,44)(19,47,65,45,24,82,42,84),

    (1,2,3,4,5),

    ( 6,66)( 7,54)( 8,10)( 9,42)(11,41)(12,65)(13,53)(14,15)
    (16,26)(17,20)(18,21)(19,32)(22,29)(23,38)(24,62)(25,50)
    (27,69)(28,57)(30,46)(31,58)(33,44)(34,70)(35,74)(36,76)
    (37,75)(39,73)(40,61)(43,77)(45,84)(47,82)(48,51)(49,63)
    (52,60)(55,79)(56,80)(59,83)(64,72)(67,78)(68,81)(71,85)
);;
```

One element whose centralizer has order `8` is:

```gap
Code9HitElement :=
    ( 1, 2, 3, 4)( 6,40, 7,27)( 8,68,55,52)( 9,44,54,82)
    (10,83,78,30)(11,36,79,59)(12,72,66,47)(13,76,67,81)
    (14,85,50,37)(15,51,74,80)(16,45,62,70)(17,56,29,75)
    (18,34,19,73)(20,31,35,71)(21,63,24,57)(22,58,25,48)
    (23,84,32,49)(26,28,38,39)(33,65,61,43)(41,60,53,46)
    (42,69,77,64);;
```

The following check verifies both the small centralizer and the failure of
rationality:

```gap
Size(Code9NonRationalHitGroup);
StructureDescription(Code9NonRationalHitGroup);
Order(Code9HitElement);
Size(Centralizer(Code9NonRationalHitGroup, Code9HitElement));
IsRationalGroupFast(Code9NonRationalHitGroup);
```

## Output

```text
R size: 21600
A size: 172800
A/R index: 8
candidate count: 16
non-rational group with small centralizer: candidate index=6, order=43200, index in A=4, structure=A5 : (A6 . C2)
  element order=4, centralizer order=8, class size=5400
rational hit group count: 0
non-rational hit group count: 1
```

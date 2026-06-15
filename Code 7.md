# Code 7: Rational Extensions $V.S_6$ Containing an Element with Centralizer $6$

## Purpose

Let $A=S_6$, and let $V$ be an irreducible $A$-module over
$\mathrm{GF}(p)$, where $p\in\{2,3,5\}$.
We test extensions

$$
1\to V\to E\to S_6\to 1
$$

including both split and non-split extensions, for the simultaneous conditions:

1. $E$ is rational;
2. $E$ contains an element $x$ of order $6$ such that $|C_E(x)|=6$.

The computation first filters modules using fixed-point conditions.  In $S_6$
there are two conjugacy classes of elements of order $6$ whose centralizers have
order $6$, represented by

```text
(1,2,3)(4,5)
(1,2,3,4,5,6)
```

If $p=2$, the $3$-part of such an element must act without non-zero fixed
points on $V$.  If $p=3$, the $2$-part must act without non-zero fixed points.
If $p=5$, the element itself must act without non-zero fixed points.  We also
use rationality on $V$ as a necessary condition: for every non-zero $v\in V$
and every scalar $a\in\mathrm{GF}(p)^\times$, the vectors $v$ and $av$ must
lie in the same $S_6$-orbit.

## Conclusion

Such extensions do exist for $S_6$.  They occur exactly among the two
4-dimensional irreducible GF(2)-modules.

| Field | GAP module ID | $\dim V$ | Extension type | Rational? | Has $|C_E(x)|=6$ for some $|x|=6$? |
|:---:|:---:|:---:|:---|:---:|:---:|
| GF(2) | 2 | 4 | split | yes | yes |
| GF(2) | 2 | 4 | non-split | yes | yes |
| GF(2) | 3 | 4 | split | yes | yes |
| GF(2) | 3 | 4 | non-split | yes | yes |

The GF(3) 1-dimensional non-trivial module passes the fixed-point filter and
the corresponding extensions do contain elements of order $6$ with centralizer
$6$, but the groups are not rational.  All GF(5)-modules are excluded by the
necessary rationality condition on $V$.

## GAP Code

```gap
LoadPackage("cohomolo");;

FixedDimension := function(rep, x, F)
    local mat, dim;

    mat := Image(rep, x);
    dim := Length(mat);
    return Length(NullspaceMat(mat - IdentityMat(dim, F)));
end;;

VectorRationalityFailure := function(A, rep, F)
    local gens, mats, M, dim, V, v, a, orb;

    gens := GeneratorsOfGroup(A);
    mats := List(gens, g -> Image(rep, g));
    M := Group(mats);
    dim := Length(mats[1]);
    V := Elements(FullRowSpace(F, dim));

    for v in V do
        if IsZero(v) then
            continue;
        fi;

        orb := Orbit(M, v, OnRight);
        for a in [2..Size(F)-1] do
            if not (a * v in orb) then
                return [v, a, Length(orb)];
            fi;
        od;
    od;

    return fail;
end;;

IsRationalGroupFast := function(G)
    local c, rep, ord, k;

    for c in ConjugacyClasses(G) do
        rep := Representative(c);
        ord := Order(rep);

        for k in [2..ord-1] do
            if Gcd(k, ord) = 1 and not rep^k in c then
                Print("      rationality failure: order=", ord,
                      ", power=", k,
                      ", |C|=", Size(Centralizer(G, rep)), "\n");
                return false;
            fi;
        od;
    od;

    return true;
end;;

Order6Centralizer6Classes := function(G)
    return Filtered(ConjugacyClasses(G),
        c -> Order(Representative(c)) = 6
             and Size(Centralizer(G, Representative(c))) = 6);
end;;

MakeSplitExtension := function(A, rep, F)
    local dim, V, Ext;

    dim := Length(Image(rep, GeneratorsOfGroup(A)[1]));
    V := F^dim;
    Ext := SemidirectProduct(A, rep, V);
    return Image(IsomorphismPermGroup(Ext));
end;;

PrintFixedPointScreen := function()
    local A, p, F, reps, mods, reps6, i, rep, mrec, dim, h2, chr,
          a, part, vecFail;

    A := SymmetricGroup(6);
    reps6 := List(Filtered(ConjugacyClasses(A),
                         c -> Order(Representative(c)) = 6
                              and Size(Centralizer(A, Representative(c))) = 6),
                  Representative);

    Print("Order-6 classes in S6 with centralizer 6:\n");
    for a in reps6 do
        Print("  ", a, ", |C|=", Size(Centralizer(A, a)), "\n");
    od;

    for p in [2,3,5] do
        F := GF(p);
        reps := IrreducibleRepresentations(A, F);
        mods := IrreducibleModules(A, F)[2];

        Print("\n================ p=", p, " fixed-point screen ================\n");

        for i in [1..Length(reps)] do
            rep := reps[i];
            mrec := mods[i];
            dim := Length(Image(rep, GeneratorsOfGroup(A)[1]));
            chr := CHR(A, p, 0, mrec.generators);
            h2 := SecondCohomologyDimension(chr);

            Print("module id=", i, " dim=", dim, " H2dim=", h2, "\n");

            if dim <= 10 then
                vecFail := VectorRationalityFailure(A, rep, F);
                if vecFail = fail then
                    Print("  V-rationality necessary condition: pass\n");
                else
                    Print("  V-rationality necessary condition: fail scalar=",
                          vecFail[2], " orbitSize=", vecFail[3], "\n");
                fi;
            fi;

            for a in reps6 do
                if p = 2 then
                    part := a^2;
                elif p = 3 then
                    part := a^3;
                else
                    part := a;
                fi;

                Print("  class rep=", a,
                      " fixedRelevant=", FixedDimension(rep, part, F),
                      " fixedFull=", FixedDimension(rep, a, F), "\n");
            od;
        od;
    od;
end;;

PrintGroupTest := function(label, G)
    local rat, c6;

    Print("\n", label, "\n");
    Print("  |G|=", Size(G), "\n");
    rat := IsRationalGroupFast(G);
    c6 := Order6Centralizer6Classes(G);
    Print("  rational=", rat, "\n");
    Print("  # classes of order-6 elements with centralizer 6 = ", Length(c6), "\n");
    if Length(c6) > 0 then
        Print("  representatives: ", List(c6, Representative), "\n");
    fi;
end;;

TestCandidateModule := function(p, id)
    local A, F, reps, mods, rep, mrec, split, chr, h2, vec, Efp, Ext;

    A := SymmetricGroup(6);
    F := GF(p);
    reps := IrreducibleRepresentations(A, F);
    mods := IrreducibleModules(A, F)[2];
    rep := reps[id];
    mrec := mods[id];

    split := MakeSplitExtension(A, rep, F);
    PrintGroupTest(Concatenation("p=", String(p), " module id=", String(id), " split"), split);

    chr := CHR(A, p, 0, mrec.generators);
    h2 := SecondCohomologyDimension(chr);
    if h2 > 0 then
        CalcPres(chr);
        for vec in Filtered(Elements(FullRowSpace(F, h2)), x -> not IsZero(x)) do
            Efp := NonsplitExtension(chr, List(vec, Int));
            Ext := Image(IsomorphismPermGroup(Efp));
            PrintGroupTest(Concatenation("p=", String(p), " module id=", String(id),
                            " non-split vector=", String(List(vec, Int))), Ext);
        od;
    fi;
end;;

# Step 1: fixed-point and V-rationality screen.
PrintFixedPointScreen();

# Step 2: construct the surviving candidates.
# GF(2), module IDs 2 and 3 are the two 4-dimensional modules.
TestCandidateModule(2, 2);
TestCandidateModule(2, 3);

# GF(3), module ID 2 survives the fixed-point screen, but rationality fails.
TestCandidateModule(3, 2);
```

## Output Summary

The fixed-point screen gives:

```text
p=2:
  module 2, dim 4:
    (1,2,3,4,5,6) has fixedRelevant=0
  module 3, dim 4:
    (1,2,3)(4,5) has fixedRelevant=0

p=3:
  only module 2, dim 1 has fixedRelevant=0 for both order-6 classes

p=5:
  some modules pass the fixed-point test, but all GF(5)-modules fail
  the V-rationality necessary condition.
```

The constructed candidates give:

```text
p=2 module id=2 split
  |G|=11520
  rational=true
  # classes of order-6 elements with centralizer 6 = 1

p=2 module id=2 non-split vector=[1]
  |G|=11520
  rational=true
  # classes of order-6 elements with centralizer 6 = 1

p=2 module id=3 split
  |G|=11520
  rational=true
  # classes of order-6 elements with centralizer 6 = 1

p=2 module id=3 non-split vector=[1]
  |G|=11520
  rational=true
  # classes of order-6 elements with centralizer 6 = 1

p=3 module id=2 split
  |G|=2160
  rational=false
  # classes of order-6 elements with centralizer 6 = 2

p=3 module id=2 non-split vector=[1] and [2]
  |G|=2160
  rational=false
  # classes of order-6 elements with centralizer 6 = 2
```

Therefore, for $S_6$, the required extensions are precisely the split and
non-split extensions of the two irreducible 4-dimensional GF(2)-modules.

## Reusable Permutation Groups

The following GAP code stores the four groups explicitly as permutation groups.
They are also collected in the list `S6Cent6RationalGroups`.

```gap
G2Split := Group([
  ( 2, 3, 5, 9,10,14)( 4, 7,11)( 6, 8,13,16,12,15),
  ( 2, 4)( 6,10)( 7, 9)(13,14),
  ( 1, 2)( 3, 6)( 4, 8)( 5,10)( 7,12)( 9,11)(13,16)(14,15)
]);;

G2Nonsplit := Group([
  ( 1, 5,15,27,19, 9)( 2, 7,17,14,22,10)( 3, 8,18,26,20,11)( 4, 6,16,28,21,12)
    (13,24,25,30,29,23),
  ( 1,26)( 2,19)( 3,17)( 4,29)( 5,16)( 6,23)(10,11)(13,14)(15,21)(18,27)(22,25),
  ( 2,19)( 3,26)( 5,14)( 8,20)(10,27)(12,30)(15,22)(24,28),
  ( 2,19)( 4,29)( 7, 9)( 8,20)(10,27)(11,18)(15,22)(21,25),
  ( 1,17)( 2,19)( 3,26)( 6,23)( 7, 9)(10,27)(11,18)(12,30),
  ( 1,17)( 2,19)( 3,26)( 4,29)( 5,14)( 7, 9)( 8,20)(13,16)
]);;

G3Split := Group([
  ( 2, 3, 5,10,14,16)( 4, 8)( 6,12, 9)( 7,13,11),
  ( 2, 4)( 3, 6)( 5,11)( 7,14)(12,16)(13,15),
  ( 1, 2)( 3, 7)( 4, 9)( 5, 6)( 8,13)(10,15)(11,16)(12,14)
]);;

G3Nonsplit := Group([
  ( 2, 4, 7,15,11, 5)( 6,10,18,29,25,14)( 8,19,12,26,37,22, 9,21,13,27,34,20)
    (16,30,43,39,24,33,17,32,46,38,23,31)(35,40,53,51,44,48)(36,41,54,52,45,49)
    (47,57,50,58)(55,59,56,60),
  ( 1, 2)( 3, 6)( 4, 8,10, 9)( 5,12,14,13)( 7,16,18,17)(11,23,25,24)(15,28)
    (19,21)(20,35,22,36)(26,40,27,41)(29,42)(30,44,32,45)(31,33)(34,47)
    (37,50)(38,51,39,52)(43,55)(46,56)(57,58)(59,60),
  ( 2, 6)( 4,10)( 8, 9)(11,25)(15,29)(23,24)(26,27)(30,32)(35,36)(47,50)
    (48,49)(51,52)(53,54)(55,56)(57,58)(59,60),
  ( 1, 3)( 2, 6)(15,29)(20,22)(26,27)(28,42)(30,32)(34,37)(35,36)(38,39)
    (40,41)(43,46)(44,45)(47,50)(51,52)(55,56),
  ( 2, 6)( 5,14)( 7,18)( 8, 9)(15,29)(19,21)(23,24)(26,27)(30,32)(31,33)
    (34,37)(40,41)(43,46)(44,45)(48,49)(53,54),
  ( 1, 3)( 2, 6)( 4,10)( 5,14)( 7,18)( 8, 9)(11,25)(12,13)(15,29)(16,17)
    (23,24)(28,42)(34,37)(43,46)(47,50)(55,56)
]);;

S6Cent6RationalGroups := [
  rec(name := "GF(2) module 2 split", group := G2Split),
  rec(name := "GF(2) module 2 non-split", group := G2Nonsplit),
  rec(name := "GF(2) module 3 split", group := G3Split),
  rec(name := "GF(2) module 3 non-split", group := G3Nonsplit)
];;

List(S6Cent6RationalGroups, r -> [r.name, Size(r.group), LargestMovedPoint(r.group)]);
```

# Code 8: Irreducible 3- and 5-modules for $\mathrm{Aut}(A_5\times A_5)$

## Purpose

Let

$$
G\cong \mathrm{Aut}(A_5\times A_5).
$$

This code checks all irreducible GF(3)- and GF(5)-modules $V$ of $G$.
We prove that there is no extension $V.G$, split or non-split, which
simultaneously satisfies:

1. $V.G$ is a rational group;
2. $G$ has an element $g$ of order $8$ with $|C_G(g)|=8$, and $g$ acts on
   $V$ without non-zero fixed points.

The computation proceeds as follows.

First we construct

$$
G=(S_5\times S_5)\rtimes C_2,
$$

where the outer involution swaps the two $A_5$ factors.  This is
$\mathrm{Aut}(A_5\times A_5)$.

For each irreducible module $V$ over GF(3) or GF(5), the code computes:

- `fixed dimensions`: dimensions of $C_V(g)$ for the conjugacy classes of
  elements $g$ of order $8$ with $|C_G(g)|=8$;
- `dim H^2(G,V)`, using the GAP package `cohomolo`;
- if $C_V(g)=0$, the split extension $V:G$ and whether it is rational.

If $C_V(g)=0$ and `dim H^2(G,V)=0`, then every extension is split.  Therefore
checking the split extension is enough for that module.

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

FixedDimensionsOnTargets := function(rep, targets, F)
    local out, x;

    out := [];
    for x in targets do
        Add(out, FixedDimensionOnElement(rep, x, F));
    od;

    return out;
end;;

ConstructAutA5xA5 := function()
    local s5_1, s5_2, tau;

    s5_1 := Group((1,2,3,4,5), (1,2));
    s5_2 := Group((6,7,8,9,10), (6,7));
    tau := (1,6)(2,7)(3,8)(4,9)(5,10);

    return ClosureGroup(ClosureGroup(s5_1, s5_2), Group(tau));
end;;

RunModuleSearch := function(p)
    local G, F, targets, pres, reps, mods, i, rep, dim, fixed,
          chr, h2, Ext, rational;

    G := ConstructAutA5xA5();
    F := GF(p);

    targets := Filtered(List(ConjugacyClasses(G), Representative),
        x -> Order(x) = 8 and Size(Centralizer(G, x)) = 8);

    pres := Image(IsomorphismFpGroupByGenerators(G, GeneratorsOfGroup(G)));
    reps := IrreducibleRepresentations(G, F);
    mods := IrreducibleModules(G, F)[2];

    Print("============================================================\n");
    Print("GF(", p, ") irreducible modules for Aut(A5 x A5)\n");
    Print("|G| = ", Size(G), "\n");
    Print("order-8 classes with centralizer 8: ", Length(targets), "\n");
    Print("number of irreducible modules: ", Length(reps), "\n\n");

    Print("ID | dim | fixed | H2 | result\n");
    Print("--------------------------------\n");

    for i in [1..Length(reps)] do
        rep := reps[i];
        dim := Length(Image(rep, GeneratorsOfGroup(G)[1]));
        fixed := FixedDimensionsOnTargets(rep, targets, F);

        chr := CHR(G, p, pres, mods[i].generators);
        h2 := SecondCohomologyDimension(chr);

        Print(String(i, 2), " | ",
              String(dim, 3), " | ",
              String(fixed, 7), " | ",
              String(h2, 2), " | ");

        if Position(fixed, 0) = fail then
            Print("skip: fixed points\n");
        else
            Ext := Image(IsomorphismPermGroup(SemidirectProduct(G, rep, F^dim)));
            rational := IsRationalGroupFast(Ext);

            Print("size=", Size(Ext), ", rat=", rational);

            if h2 = 0 then
                Print(", split only");
            else
                Print(", check nonsplit");
            fi;

            Print("\n");
        fi;
    od;

    Print("\n");
end;;

RunModuleSearch(3);;
RunModuleSearch(5);;
```

## Output

```text
============================================================
GF(3) irreducible modules for Aut(A5 x A5)
|G| = 28800
order-8 classes with centralizer 8: 1
number of irreducible modules: 20

ID | dim | fixed | H2 | result
--------------------------------
 1 |   1 |   [ 0 ] |  0 | size=86400, rat=false, split only
 2 |   1 |   [ 1 ] |  0 | skip: fixed points
 3 |   1 |   [ 1 ] |  0 | skip: fixed points
 4 |   1 |   [ 0 ] |  0 | size=86400, rat=false, split only
 5 |   2 |   [ 0 ] |  0 | size=259200, rat=false, split only
 6 |   8 |   [ 1 ] |  0 | skip: fixed points
 7 |   8 |   [ 1 ] |  0 | skip: fixed points
 8 |   8 |   [ 1 ] |  1 | skip: fixed points
 9 |   8 |   [ 1 ] |  0 | skip: fixed points
10 |  12 |   [ 1 ] |  0 | skip: fixed points
11 |  12 |   [ 1 ] |  0 | skip: fixed points
12 |  16 |   [ 2 ] |  0 | skip: fixed points
13 |  16 |   [ 2 ] |  0 | skip: fixed points
14 |  16 |   [ 2 ] |  1 | skip: fixed points
15 |  16 |   [ 2 ] |  0 | skip: fixed points
16 |  32 |   [ 4 ] |  0 | skip: fixed points
17 |  36 |   [ 5 ] |  0 | skip: fixed points
18 |  36 |   [ 5 ] |  0 | skip: fixed points
19 |  48 |   [ 6 ] |  0 | skip: fixed points
20 |  48 |   [ 6 ] |  0 | skip: fixed points

============================================================
GF(5) irreducible modules for Aut(A5 x A5)
|G| = 28800
order-8 classes with centralizer 8: 1
number of irreducible modules: 27

ID | dim | fixed | H2 | result
--------------------------------
 1 |   1 |   [ 1 ] |  0 | skip: fixed points
 2 |   1 |   [ 0 ] |  0 | size=144000, rat=false, split only
 3 |   1 |   [ 0 ] |  0 | size=144000, rat=false, split only
 4 |   1 |   [ 1 ] |  0 | skip: fixed points
 5 |   2 |   [ 0 ] |  0 | size=720000, rat=false, split only
 6 |   6 |   [ 0 ] |  0 | size=450000000, rat=false, split only
 7 |   6 |   [ 1 ] |  1 | skip: fixed points
 8 |   6 |   [ 1 ] |  0 | skip: fixed points
 9 |   6 |   [ 0 ] |  0 | size=450000000, rat=false, split only
10 |   9 |   [ 2 ] |  1 | skip: fixed points
11 |   9 |   [ 1 ] |  0 | skip: fixed points
12 |   9 |   [ 2 ] |  0 | skip: fixed points
13 |   9 |   [ 1 ] |  0 | skip: fixed points
14 |  10 |   [ 1 ] |  0 | skip: fixed points
15 |  10 |   [ 2 ] |  0 | skip: fixed points
16 |  10 |   [ 1 ] |  0 | skip: fixed points
17 |  10 |   [ 2 ] |  0 | skip: fixed points
18 |  18 |   [ 2 ] |  0 | skip: fixed points
19 |  25 |   [ 3 ] |  0 | skip: fixed points
20 |  25 |   [ 4 ] |  0 | skip: fixed points
21 |  25 |   [ 4 ] |  0 | skip: fixed points
22 |  25 |   [ 3 ] |  0 | skip: fixed points
23 |  30 |   [ 4 ] |  0 | skip: fixed points
24 |  30 |   [ 3 ] |  0 | skip: fixed points
25 |  30 |   [ 3 ] |  0 | skip: fixed points
26 |  30 |   [ 4 ] |  0 | skip: fixed points
27 |  50 |   [ 6 ] |  0 | skip: fixed points
```

## Conclusion

For GF(3), the only irreducible modules on which the relevant order-$8$
element acts fixed-point-freely are modules `1`, `4`, and `5`.  For all three,
`dim H^2(G,V)=0`, so all extensions are split, and the split extension is not
rational.

For GF(5), the only irreducible modules on which the relevant order-$8$
element acts fixed-point-freely are modules `2`, `3`, `5`, `6`, and `9`.  For
all five, `dim H^2(G,V)=0`, so all extensions are split, and the split
extension is not rational.

Therefore no split or non-split extension $V.G$ satisfies both required
conditions.

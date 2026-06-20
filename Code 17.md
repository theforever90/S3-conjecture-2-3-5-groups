# Code 17: The case `G/H = C2 x S5` with `H` a normal 3-subgroup

## Purpose

This code verifies two computational facts:

1. If `|H| = 3`, `G/H = C2 x S5`, `G` is rational, and `G` has an element with
   centralizer order `8`, then `G` is isomorphic to `S3 x S5`.
2. For irreducible GF(3)-modules `V` of `C2 x S5`, if a quotient element with
   centralizer order `8` acts fixed-point-freely on `V`, then `V` is
   one-dimensional.

## GAP Code

```gap
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

HasCentralizer8 := function(G)
    return ForAny(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = 8);
end;;

RunPartA := function()
    local target, total, candidates, rationalHits, cent8Hits, i, G,
          normals, N, Q, iso, rat, has8;

    target := DirectProduct(CyclicGroup(2), SymmetricGroup(5));
    total := NumberSmallGroups(720);
    candidates := [];
    rationalHits := [];
    cent8Hits := [];

    Print("PART A: groups with normal C3 quotient C2 x S5\n");
    Print("SmallGroups of order 720 = ", total, "\n");

    for i in [1..total] do
        G := SmallGroup(720, i);
        normals := Filtered(NormalSubgroups(G), N -> Size(N) = 3);

        for N in normals do
            Q := G / N;
            iso := IsomorphismGroups(Q, target);

            if iso <> fail then
                rat := IsRationalGroupFast(G);
                has8 := HasCentralizer8(G);

                Add(candidates, rec(
                    id := i,
                    structure := StructureDescription(G),
                    rational := rat,
                    hasCent8 := has8
                ));

                if rat then
                    Add(rationalHits, i);
                fi;

                if rat and has8 then
                    Add(cent8Hits, i);
                fi;

                break;
            fi;
        od;
    od;

    Print("groups with normal C3 quotient C2 x S5 = ",
          Length(candidates), "\n");

    for i in [1..Length(candidates)] do
        Print("  SmallGroup(720,", candidates[i].id,
              ") structure=", candidates[i].structure,
              " rational=", candidates[i].rational,
              " hasCent8=", candidates[i].hasCent8, "\n");
    od;

    Print("rational candidates = ", rationalHits, "\n");
    Print("rational candidates with centralizer 8 = ", cent8Hits, "\n\n");
end;;

FixedDimension := function(mats, gens, g, F)
    local hom, M, d;

    hom := GroupHomomorphismByImages(Group(gens), Group(mats), gens, mats);
    M := Image(hom, g);
    d := Length(M);

    return Length(NullspaceMat(M - IdentityMat(d, F)));
end;;

FlattenIrreducibleModules := function(raw)
    local mods, item, sub;

    mods := [];

    for item in raw do
        if IsRecord(item) then
            Add(mods, item);
        elif IsList(item) then
            for sub in item do
                if IsRecord(sub) then
                    Add(mods, sub);
                fi;
            od;
        fi;
    od;

    return mods;
end;;

RunPartB := function()
    local G, F, gens, targets, mods, i, m, fixedDims, fixedFree;

    F := GF(3);

    # A permutation representation of C2 x S5.
    G := Group((1,2), (3,4), (3,4,5,6,7));;
    gens := GeneratorsOfGroup(G);

    targets := List(Filtered(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = 8), Representative);
    mods := FlattenIrreducibleModules(IrreducibleModules(G, F));

    Print("PART B: irreducible GF(3)-modules for C2 x S5\n");
    Print("G = C2 x S5, |G| = ", Size(G), "\n");
    Print("target classes with centralizer 8 = ", Length(targets), "\n");
    Print("irreducible GF(3)-modules = ", Length(mods), "\n\n");
    Print("ID | dim | fixed dims on target classes | fixed-free?\n");
    Print("------------------------------------------------------\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        fixedDims := List(targets,
            g -> FixedDimension(m.generators, gens, g, F));
        fixedFree := 0 in fixedDims;

        Print(String(i, 2), " | ", String(m.dimension, 3), " | ",
              String(fixedDims, 28), " | ", fixedFree, "\n");
    od;
end;;

RunPartA();;
RunPartB();;
```

## Output

```text
PART A: groups with normal C3 quotient C2 x S5
SmallGroups of order 720 = 840
groups with normal C3 quotient C2 x S5 = 3
  SmallGroup(720,767) structure=S5 x S3 rational=true hasCent8=true
  SmallGroup(720,769) structure=C6 x S5 rational=false hasCent8=false
  SmallGroup(720,770) structure=C2 x (A5 : S3) rational=false hasCent8=true
rational candidates = [ 767 ]
rational candidates with centralizer 8 = [ 767 ]

PART B: irreducible GF(3)-modules for C2 x S5
G = C2 x S5, |G| = 240
target classes with centralizer 8 = 2
irreducible GF(3)-modules = 10

ID | dim | fixed dims on target classes | fixed-free?
------------------------------------------------------
 1 |   1 |                     [ 1, 1 ] | false
 2 |   1 |                     [ 1, 0 ] | true
 3 |   1 |                     [ 0, 0 ] | true
 4 |   1 |                     [ 0, 1 ] | true
 5 |   4 |                     [ 1, 1 ] | false
 6 |   4 |                     [ 1, 1 ] | false
 7 |   4 |                     [ 1, 1 ] | false
 8 |   4 |                     [ 1, 1 ] | false
 9 |   6 |                     [ 1, 1 ] | false
10 |   6 |                     [ 1, 1 ] | false
```

## Conclusion

For `|H| = 3`, the only rational candidate with an element of centralizer order
`8` is `SmallGroup(720,767)`, which has structure `S5 x S3`.  Hence in the
base case, `G` is isomorphic to `S3 x S5`.

For the module calculation, all irreducible GF(3)-modules of dimension greater
than `1` have non-zero fixed-point spaces on both target classes.  Therefore, if
the relevant quotient element acts fixed-point-freely on `V`, then `V` must be
one-dimensional.

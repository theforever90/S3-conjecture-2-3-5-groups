# Code 15: Excluding irreducible GF(5)-modules for `C2 x S5`

## Purpose

Here

```text
G/N is isomorphic to C2 x S5.
```

Let `D <= N` be such that `N/D` is a chief factor of `G`.  If `N/D` is a
5-group, then it is an irreducible GF(5)-module for `G/N`.  This code verifies
that no such extension can simultaneously satisfy:

1. it is rational;
2. it contains an element whose centralizer has order `8`.

The check uses two necessary conditions.

- If an element above a quotient element with centralizer order `8` has
  centralizer order `8`, then that quotient element must act fixed-point-freely
  on the module.  Otherwise the non-trivial fixed-point space in the normal
  5-subgroup already makes the centralizer too large.
- If the extension is rational, then the rationality condition already holds on
  the normal elementary abelian module: every non-zero vector must be conjugate
  to all its non-zero scalar multiples.

Every irreducible GF(5)-module fails at least one of these two necessary tests.

## GAP Code

```gap
IsRationalOnModule := function(mats, p)
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

FixedDimension := function(mats, gens, g, F)
    local hom, M, d;

    hom := GroupHomomorphismByImages(Group(gens), Group(mats), gens, mats);
    M := Image(hom, g);
    d := Length(M);

    return Length(NullspaceMat(M - IdentityMat(d, F)));
end;;

RunCode15 := function()
    local G, F, p, gens, targets, mods, i, m, fixedDims, fixedFree,
          scalarRat, result;

    p := 5;
    F := GF(p);

    # A permutation representation of C2 x S5.
    G := Group((1,2), (3,4), (3,4,5,6,7));;
    gens := GeneratorsOfGroup(G);

    targets := List(Filtered(ConjugacyClasses(G),
        c -> Size(Centralizer(G, Representative(c))) = 8), Representative);
    mods := IrreducibleModules(G, F)[2];

    Print("G = C2 x S5, |G| = ", Size(G), "\n");
    Print("target classes with centralizer 8 = ", Length(targets), "\n");
    Print("irreducible GF(5)-modules = ", Length(mods), "\n\n");
    Print("dim | fixed dims on target classes | scalar-rational | result\n");
    Print("---------------------------------------------------------------\n");

    for i in [1..Length(mods)] do
        m := mods[i];
        fixedDims := List(targets,
            g -> FixedDimension(m.generators, gens, g, F));
        fixedFree := 0 in fixedDims;
        scalarRat := false;

        if fixedFree then
            scalarRat := IsRationalOnModule(m.generators, p);

            if scalarRat then
                result := "survives necessary tests";
            else
                result := "not rational already on V";
            fi;
        else
            result := "centralizer-8 lift impossible";
        fi;

        Print(String(m.dimension, 3), " | ",
              String(fixedDims, 28), " | ",
              String(scalarRat, 15), " | ",
              result, "\n");
    od;
end;;

RunCode15();;
```

## Output

```text
G = C2 x S5, |G| = 240
target classes with centralizer 8 = 2
irreducible GF(5)-modules = 12

dim | fixed dims on target classes | scalar-rational | result
---------------------------------------------------------------
  1 |                     [ 1, 1 ] |           false | centralizer-8 lift impossible
  1 |                     [ 1, 0 ] |           false | not rational already on V
  1 |                     [ 0, 0 ] |           false | not rational already on V
  1 |                     [ 0, 1 ] |           false | not rational already on V
  3 |                     [ 0, 0 ] |           false | not rational already on V
  3 |                     [ 0, 1 ] |           false | not rational already on V
  3 |                     [ 1, 1 ] |           false | centralizer-8 lift impossible
  3 |                     [ 1, 0 ] |           false | not rational already on V
  5 |                     [ 1, 1 ] |           false | centralizer-8 lift impossible
  5 |                     [ 1, 2 ] |           false | centralizer-8 lift impossible
  5 |                     [ 2, 2 ] |           false | centralizer-8 lift impossible
  5 |                     [ 2, 1 ] |           false | centralizer-8 lift impossible
```

## Conclusion

There are 12 irreducible GF(5)-modules for `C2 x S5`.  Each is eliminated by
one of the two necessary tests:

- either no target class acts fixed-point-freely, so an element with centralizer
  order `8` cannot occur in the extension;
- or the module already fails the rationality condition on the normal
  elementary abelian 5-subgroup.

Thus no extension by an irreducible 5-module can be both rational and contain an
element whose centralizer has order `8`.

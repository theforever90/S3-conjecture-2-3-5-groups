# Code 16: Lifts of double transpositions in the case `|gbar|=2`

## Purpose

This code is used in Lemma 28, case (3), where `|gbar|=2`.

After the preceding reductions, if `H` is chosen so that `K/H` is a chief factor
of `G`, then `G/H` is one of the rational extensions of `S5` by an irreducible
GF(2)-module:

```text
C2 x S5, SmallGroup(1920,240993), SmallGroup(1920,240996).
```

The element `gbar` lies in the double-transposition class of `S5`, i.e. the
class with centralizer order `8` in `S5`.  This code checks all elements in the
three possible groups whose image in the quotient `S5` lies in that class.  In
each possible group, the centralizer order is always larger than `8`.

## GAP Code

```gap
CentralizerDataForDoubleTranspositionLifts := function(X)
    local normals, N, Q, iso, S5, c, qrep, hits, cl, x, img, csize,
          minc, data, nat;

    hits := [];

    for N in NormalSubgroups(X) do
        if Size(N) = Size(X) / 120 then
            Q := X / N;
            iso := IsomorphismGroups(Q, SymmetricGroup(5));

            if iso <> fail then
                S5 := Image(iso);
                nat := NaturalHomomorphismByNormalSubgroup(X, N);

                for c in ConjugacyClasses(S5) do
                    if Order(Representative(c)) = 2
                       and Size(Centralizer(S5, Representative(c))) = 8 then
                        qrep := PreImagesRepresentative(iso, Representative(c));
                        minc := fail;
                        data := [];

                        for cl in ConjugacyClasses(X) do
                            x := Representative(cl);
                            img := Image(nat, x);

                            if img in ConjugacyClass(Q, qrep) then
                                csize := Size(Centralizer(X, x));

                                if minc = fail or csize < minc then
                                    minc := csize;
                                fi;

                                Add(data, [Order(x), csize]);
                            fi;
                        od;

                        Add(hits, rec(
                            kernelSize := Size(N),
                            quotientId := IdGroup(Q),
                            minCentralizer := minc,
                            data := Set(data)
                        ));
                    fi;
                od;
            fi;
        fi;
    od;

    return hits;
end;;

RunCode16 := function()
    local groups, entry, name, X, data, r;

    groups := [
        ["C2 x S5", DirectProduct(CyclicGroup(2), SymmetricGroup(5))],
        ["SmallGroup(1920,240993)", SmallGroup(1920,240993)],
        ["SmallGroup(1920,240996)", SmallGroup(1920,240996)]
    ];

    for entry in groups do
        name := entry[1];
        X := entry[2];

        Print("============================================================\n");
        Print(name, ", |X|=", Size(X),
              ", structure=", StructureDescription(X), "\n");

        data := CentralizerDataForDoubleTranspositionLifts(X);
        Print("S5 quotients found: ", Length(data), "\n");

        for r in data do
            Print("  kernel size=", r.kernelSize,
                  ", quotient Id=", r.quotientId,
                  ", min centralizer=", r.minCentralizer, "\n");
            Print("  [element order, centralizer size] data=", r.data, "\n");
        od;
    od;
end;;

RunCode16();;
```

## Output

```text
============================================================
C2 x S5, |X|=240, structure=C2 x S5
S5 quotients found: 1
  kernel size=2, quotient Id=[ 120, 34 ], min centralizer=16
  [element order, centralizer size] data=[ [ 2, 16 ] ]
============================================================
SmallGroup(1920,240993), |X|=1920, structure=(C2 x C2 x C2 x C2) : S5
S5 quotients found: 1
  kernel size=16, quotient Id=[ 120, 34 ], min centralizer=16
  [element order, centralizer size] data=[ [ 2, 32 ], [ 4, 16 ], [ 4, 32 ] ]
============================================================
SmallGroup(1920,240996), |X|=1920, structure=(C2 x C2 x C2 x C2) : S5
S5 quotients found: 1
  kernel size=16, quotient Id=[ 120, 34 ], min centralizer=16
  [element order, centralizer size] data=[ [ 2, 32 ], [ 4, 16 ], [ 4, 32 ] ]
```

## Conclusion

In each of the three possible groups `G/H`, every lift of the double-transposition
class of the quotient `S5` has centralizer order at least `16`.  Therefore no
such group can contain an element mapping to this class with centralizer order
`8`.

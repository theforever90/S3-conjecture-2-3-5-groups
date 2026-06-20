# Code 4: Extensions $V.S_5$ for Irreducible $2$-Modules

## Purpose

Let $G=V.S_5$, where $V$ is an irreducible $\mathbb F_2S_5$-module.
The irreducible modules have dimensions $1$, $4$, and $4$.
The candidate groups are obtained from the SmallGroup enumeration in Code 2.
In the $1$-dimensional case this includes the non-split extensions.

For each candidate, this code checks:

1. the dimension of $V$;
2. whether the extension splits over $V$;
3. the centralizer sizes of the conjugacy classes;
4. whether every element outside $V$ with centralizer of order less than $8$
   is conjugate into a complement isomorphic to $S_5$.

## Code

```gap
S5 := SymmetricGroup(5);;

IsIrreducibleNormalModule := function(G, V)
    local ns, N;

    ns := NormalSubgroups(G);
    for N in ns do
        if Size(N) > 1 and Size(N) < Size(V) and IsSubgroup(V, N) then
            return false;
        fi;
    od;
    return true;
end;;

FindComplementsToV := function(G, V)
    local comps, c, H;

    comps := [];
    for c in ConjugacyClassesSubgroups(G) do
        H := Representative(c);
        if Size(H) = 120
           and Size(Intersection(H, V)) = 1
           and Size(ClosureGroup(H, V)) = Size(G) then
            Add(comps, H);
        fi;
    od;
    return comps;
end;;

IsConjugateIntoSomeComplement := function(G, x, comps)
    local H, c;

    for H in comps do
        for c in ConjugacyClasses(H) do
            if IsConjugate(G, x, Representative(c)) then
                return true;
            fi;
        od;
    od;
    return false;
end;;

CentralizerData := function(G)
    local data, c, x;

    data := [];
    for c in ConjugacyClasses(G) do
        x := Representative(c);
        Add(data, [Order(x), Size(Centralizer(G, x))]);
    od;
    return Set(data);
end;;

AnalyzeOneGroup := function(order, id)
    local G, Vs, V, comps, c, x, small, irred;

    G := SmallGroup(order, id);
    Vs := Filtered(NormalSubgroups(G),
        N -> Size(N) in [2, 16]
             and IsElementaryAbelian(N)
             and IdGroup(G / N) = IdGroup(S5));

    for V in Vs do
        irred := IsIrreducibleNormalModule(G, V);
        Print("[", order, ",", id, "]",
              "  dim(V)=", LogInt(Size(V), 2),
              "  irreducible=", irred,
              "  structure: ", StructureDescription(G), "\n");

        if irred then
            comps := FindComplementsToV(G, V);
            small := [];

            for c in ConjugacyClasses(G) do
                x := Representative(c);
                if not x in V and Size(Centralizer(G, x)) < 8 then
                    Add(small,
                        [Order(x),
                         Size(Centralizer(G, x)),
                         IsConjugateIntoSomeComplement(G, x, comps)]);
                fi;
            od;

            Print("[", order, ",", id, "]",
                  "  split=", Length(comps) > 0,
                  "  #complement classes=", Length(comps), "\n");
            Print("  centralizer data (element order, |C_G(x)|):\n  ",
                  CentralizerData(G), "\n");
            Print("  classes outside V with |C_G(x)| < 8:\n  ",
                  Set(small), "\n\n");
        fi;
    od;
end;;

Print("=== Irreducible extensions V.S5 over GF(2) ===\n\n");

# Candidate groups from Code 2.
ids240 := [89, 90, 91, 189];;

ids1920 := [
    240482, 240507, 240589, 240592, 240610, 240626, 240750, 240752,
    240791, 240792, 240796, 240970, 240971, 240975, 240993, 240996
];;

for id in ids240 do
    AnalyzeOneGroup(240, id);
od;

for id in ids1920 do
    AnalyzeOneGroup(1920, id);
od;
```

## Output

```
=== Irreducible extensions V.S5 over GF(2) ===

[240,89]  dim(V)=1  irreducible=true  structure: C2 . S5 = SL(2,5) . C2
[240,89]  split=false  #complement classes=0
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 240 ], [ 2, 240 ], [ 3, 12 ], [ 4, 8 ], [ 4, 12 ],
    [ 5, 10 ], [ 6, 12 ], [ 8, 8 ], [ 10, 10 ], [ 12, 12 ] ]
  classes outside V with |C_G(x)| < 8:
  [  ]

[240,90]  dim(V)=1  irreducible=true  structure: SL(2,5) : C2
[240,90]  split=false  #complement classes=0
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 240 ], [ 2, 12 ], [ 2, 240 ], [ 3, 12 ], [ 4, 8 ],
    [ 5, 10 ], [ 6, 12 ], [ 8, 8 ], [ 10, 10 ] ]
  classes outside V with |C_G(x)| < 8:
  [  ]

[240,91]  dim(V)=1  irreducible=true  structure: A5 : C4
[240,91]  split=false  #complement classes=0
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 240 ], [ 2, 16 ], [ 2, 240 ], [ 3, 12 ], [ 4, 8 ],
    [ 4, 24 ], [ 5, 10 ], [ 6, 12 ], [ 10, 10 ], [ 12, 12 ] ]
  classes outside V with |C_G(x)| < 8:
  [  ]

[240,189]  dim(V)=1  irreducible=true  structure: C2 x S5
[240,189]  split=true  #complement classes=2
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 240 ], [ 2, 16 ], [ 2, 24 ], [ 2, 240 ],
    [ 3, 12 ], [ 4, 8 ], [ 5, 10 ], [ 6, 12 ], [ 10, 10 ] ]
  classes outside V with |C_G(x)| < 8:
  [  ]

[1920,240482]  dim(V)=4  irreducible=false  structure: C2 x (A5 : ((C4 x C2) : C2))
[1920,240507]  dim(V)=4  irreducible=false  structure: A5 : ((C2 x C2 x C2 x C2) : C2)
[1920,240589]  dim(V)=4  irreducible=false  structure: C2 x C2 x C2 x (A5 : C4)
[1920,240592]  dim(V)=4  irreducible=false  structure: C2 x C2 x (A5 : D8)
[1920,240610]  dim(V)=4  irreducible=false  structure: C2 x C2 x C2 x C2 x S5
[1920,240626]  dim(V)=4  irreducible=false  structure: (C2 x C2) : (SL(2,5) : C4)
[1920,240750]  dim(V)=4  irreducible=false  structure: C2 x C2 x (SL(2,5) : C4)
[1920,240752]  dim(V)=4  irreducible=false  structure: C2 x ((C2 x SL(2,5)) : C4)
[1920,240791]  dim(V)=4  irreducible=false  structure: C2 x (SL(2,5) : D8)
[1920,240792]  dim(V)=4  irreducible=false  structure: C2 x ((C2 x C2) : (C2 . S5 = SL(2,5) . C2))
[1920,240796]  dim(V)=4  irreducible=false  structure: (C2 x C2) : ((C2 x SL(2,5)) : C2)
[1920,240970]  dim(V)=4  irreducible=false  structure: C2 x C2 x C2 x (SL(2,5) : C2)
[1920,240971]  dim(V)=4  irreducible=false  structure: C2 x C2 x C2 x (C2 . S5 = SL(2,5) . C2)
[1920,240975]  dim(V)=4  irreducible=false  structure: C2 x C2 x ((SL(2,5) : C2) : C2)

[1920,240993]  dim(V)=4  irreducible=true  structure: (C2 x C2 x C2 x C2) : S5
[1920,240993]  split=true  #complement classes=2
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 1920 ], [ 2, 32 ], [ 2, 48 ], [ 2, 128 ],
    [ 3, 6 ], [ 4, 8 ], [ 4, 16 ], [ 4, 32 ], [ 5, 5 ],
    [ 6, 6 ], [ 8, 8 ] ]
  classes outside V with |C_G(x)| < 8:
  [ [ 3, 6, true ], [ 5, 5, true ], [ 6, 6, true ] ]

[1920,240996]  dim(V)=4  irreducible=true  structure: (C2 x C2 x C2 x C2) : S5
[1920,240996]  split=true  #complement classes=1
  centralizer data (element order, |C_G(x)|):
  [ [ 1, 1920 ], [ 2, 32 ], [ 2, 96 ], [ 2, 192 ],
    [ 2, 384 ], [ 3, 24 ], [ 4, 8 ], [ 4, 16 ], [ 4, 32 ],
    [ 4, 96 ], [ 5, 5 ], [ 6, 12 ], [ 6, 24 ], [ 8, 8 ],
    [ 12, 12 ] ]
  classes outside V with |C_G(x)| < 8:
  [ [ 5, 5, true ] ]
```

## Conclusion

The irreducible cases are exactly the four $1$-dimensional extensions
$[240,89]$, $[240,90]$, $[240,91]$, $[240,189]$ and the two $4$-dimensional
extensions $[1920,240993]$, $[1920,240996]$.  The $1$-dimensional cases include
the three non-split extensions $[240,89]$, $[240,90]$, and $[240,91]$; none has
an element outside $V$ whose centralizer has order less than $8$.  The two
$4$-dimensional irreducible extensions both split over $V$, and every element
outside $V$ with centralizer of order less than $8$ is conjugate into a
complement isomorphic to $S_5$.

# Code 2: Rational Groups of the Form $V.\mathrm{S}_5$ over $\mathrm{GF}(2)$

## Purpose

Find all rational groups of the form $G = V.\mathrm{S}_5$, where $V$ is an irreducible $\mathrm{S}_5$-module over $\mathrm{GF}(2)$.

The irreducible $2$-modules of $\mathrm{S}_5$ are either $1$-dimensional ($|V|=2$, $|G|=240$) or $4$-dimensional ($|V|=16$, $|G|=1920$). All such groups lie in the SmallGroup library.

## Code

```gap
# ---- Rational group test ----
IsRationalGroup := function(G)
    local classes, rep, order, k;
    classes := ConjugacyClasses(G);
    for rep in List(classes, Representative) do
        order := Order(rep);
        for k in [1..order] do
            if Gcd(k, order) = 1 then
                if not IsConjugate(G, rep, rep^k) then
                    return false;
                fi;
            fi;
        od;
    od;
    return true;
end;

S5 := SymmetricGroup(5);

# ============================================================
# Order 240: V = C2 (1-dimensional module)
# ============================================================
Print("=== Searching SmallGroup(240) for V.S5 with V=C2 ===\n");
for id in [1..NrSmallGroups(240)] do
    G := SmallGroup(240, id);
    if IsSolvable(G) then continue; fi;
    # Look for normal subgroup V of order 2 with G/V ≅ S5
    ns := Filtered(NormalSubgroups(G), N -> Size(N) = 2 and IsElementaryAbelian(N));
    for V in ns do
        if IdGroup(G / V) = IdGroup(S5) then
            Print("  SG(240,", id, "): struct=", StructureDescription(G),
                  "  rat=", IsRationalGroup(G), "\n");
            break;
        fi;
    od;
od;

# ============================================================
# Order 1920: V = C2^4 (4-dimensional module)
# ============================================================
Print("\n=== Searching SmallGroup(1920) for V.S5 with V=C2^4 ===\n");
for id in [1..NrSmallGroups(1920)] do
    G := SmallGroup(1920, id);
    if IsSolvable(G) then continue; fi;
    # Look for normal subgroup V of order 16 with G/V ≅ S5
    ns := Filtered(NormalSubgroups(G),
                   N -> Size(N) = 16 and IsElementaryAbelian(N));
    for V in ns do
        if IdGroup(G / V) = IdGroup(S5) then
            Print("  SG(1920,", id, "): struct=", StructureDescription(G),
                  "  rat=", IsRationalGroup(G), "\n");
            break;
        fi;
    od;
od;
```

## Output

```
=== Searching SmallGroup(240) for V.S5 with V=C2 ===
  SG(240,89): struct=C2 . S5 = SL(2,5) . C2  rat=false
  SG(240,90): struct=SL(2,5) : C2  rat=false
  SG(240,91): struct=A5 : C4  rat=false
  SG(240,189): struct=C2 x S5  rat=true

=== Searching SmallGroup(1920) for V.S5 with V=C2^4 ===
  SG(1920,240482): struct=C2 x (A5 : ((C4 x C2) : C2))  rat=false
  SG(1920,240507): struct=A5 : ((C2 x C2 x C2 x C2) : C2)  rat=false
  SG(1920,240589): struct=C2 x C2 x C2 x (A5 : C4)  rat=false
  SG(1920,240592): struct=C2 x C2 x (A5 : D8)  rat=false
  SG(1920,240610): struct=C2 x C2 x C2 x C2 x S5  rat=true
  SG(1920,240626): struct=(C2 x C2) : (SL(2,5) : C4)  rat=false
  SG(1920,240750): struct=C2 x C2 x (SL(2,5) : C4)  rat=false
  SG(1920,240752): struct=C2 x ((C2 x SL(2,5)) : C4)  rat=false
  SG(1920,240791): struct=C2 x (SL(2,5) : D8)  rat=false
  SG(1920,240792): struct=C2 x ((C2 x C2) : (C2 . S5 = SL(2,5) . C2))  rat=false
  SG(1920,240796): struct=(C2 x C2) : ((C2 . S5 = SL(2,5) . C2) : C2)  rat=false
  SG(1920,240970): struct=C2 x C2 x C2 x (SL(2,5) : C2)  rat=false
  SG(1920,240971): struct=C2 x C2 x C2 x (C2 . S5 = SL(2,5) . C2)  rat=false
  SG(1920,240975): struct=C2 x C2 x ((SL(2,5) : C2) : C2)  rat=false
  SG(1920,240993): struct=(C2 x C2 x C2 x C2) : S5  rat=true
  SG(1920,240996): struct=(C2 x C2 x C2 x C2) : S5  rat=true
```

## Conclusion

| Order | $|V|$ | Rational Groups | Rational? | Notes |
|:---:|:---:|:---|:---:|:---|
| 240 | 2 | SG(240,89), SG(240,90), SG(240,91) | ✗ | Non-split extensions |
| 240 | 2 | SG(240,189) = $C_2 \times S_5$ | ✓ | Direct product (trivial module) |
| 1920 | 16 | SG(1920,240610) = $C_2^4 \times S_5$ | ✓ | Direct product (trivial module) |
| **1920** | **16** | **SG(1920,240993), SG(1920,240996)** | **✓** | **Irreducible 4-dimensional module** |

Among all groups of the form $V.\mathrm{S}_5$ with $V$ an elementary abelian $2$-group and $G/V \cong S_5$, the rational ones are:

- $[240,189] \cong C_2 \times S_5$ (trivial action),
- $[1920,240610] \cong C_2^4 \times S_5$ (trivial action),
- $[1920,240993]$ and $[1920,240996]$ (irreducible action).

When $V$ is required to be an **irreducible** $\mathrm{S}_5$-module over $\mathrm{GF}(2)$, the only rational groups are $C_2\times S_5$, $[1920,240993]$ and $[1920,240996]$.

# Code 3: Rational Groups Between $A_5 \times A_5$ and $\mathrm{Aut}(A_5 \times A_5)$

## Purpose

Let $R = A_5 \times A_5$. This code enumerates **all groups** $G$ satisfying $R \leq G \leq \mathrm{Aut}(R)$ and filters those that are **rational groups**. For each rational group found, we compute:

1. **Conjugacy class sizes** — both the full sorted list and the set of distinct sizes
2. **Centralizer sizes** $|C_G(g)|$ with corresponding element orders
3. **Structure description**

---

## Code

```gap
# ==============================================================================
# Utility Functions
# ==============================================================================

# A group G is rational if every element is conjugate to all its
# powers that are coprime to its order.
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

# Conjugacy class sizes (full list, sorted)
CCS := function(G)
    local sizes;
    sizes := List(ConjugacyClasses(G), Size);
    Sort(sizes);
    return sizes;
end;

# Conjugate type vector (distinct sizes only)
CTV := function(G)
    return Set(List(ConjugacyClasses(G), Size));
end;

# Centralizer sizes with element orders, sorted by |C|
SCOE := function(G)
    local data;
    data := List(ConjugacyClasses(G),
        c -> [Order(Representative(c)), Int(Size(G)/Size(c))]);
    Sort(data, function(a,b) return a[2] < b[2]; end);
    return data;
end;

# ==============================================================================
# Construct M = A5 x A5 and A = Aut(A5 x A5)
# ==============================================================================

# Permutation representation on 10 points:
#   {1..5}  -> first A5 (or S5)
#   {6..10} -> second A5 (or S5)

a5_1 := Group((1,2,3,4,5), (1,2,3));
a5_2 := Group((6,7,8,9,10), (6,7,8));
M := ClosureGroup(a5_1, a5_2);              # M = A5 x A5, |M| = 3600

s5_1 := Group((1,2,3,4,5), (1,2));
s5_2 := Group((6,7,8,9,10), (6,7));

# Coordinate-swapping involution
tau := (1,6)(2,7)(3,8)(4,9)(5,10);

# A = (S5 x S5) ⋊ <tau> ≅ Aut(A5 x A5), |A| = 28800
A := ClosureGroup(ClosureGroup(s5_1, s5_2), Group(tau));

Print("M = A5 x A5,  |M| = ", Size(M), "\n");
Print("A = Aut(A5xA5), |A| = ", Size(A), "\n");
Print("Index [A:M] = ", Size(A)/Size(M), "\n\n");

# ==============================================================================
# Find All Intermediate Subgroups and Filter Rational Groups
# ==============================================================================

Print("Computing intermediate subgroups...\n");
inter := IntermediateSubgroups(A, M);
all_candidates := Concatenation([M], inter.subgroups, [A]);
Print("Total candidate groups (including M and A): ",
      Length(all_candidates), "\n\n");

Print("Filtering rational groups...\n");
rational_groups := [];
for G in all_candidates do
    if IsRationalGroup(G) then
        Add(rational_groups, rec(group := G, order := Size(G)));
        Print("  Found rational group of order ", Size(G), "\n");
    fi;
od;
Sort(rational_groups, function(a,b) return a.order < b.order; end);
Print("\nTotal rational groups found: ", Length(rational_groups), "\n");

# ==============================================================================
# Detailed Analysis of Each Rational Group
# ==============================================================================

for i in [1..Length(rational_groups)] do
    G := rational_groups[i].group;
    ord := Size(G);
    idx := Index(A, G);

    Print("\n========================================\n");
    Print("Rational Group #", i, "\n");
    Print("========================================\n");
    Print("Order:               ", ord, "\n");
    Print("Index in Aut(A5xA5): ", idx, "\n");
    Print("Structure:           ", StructureDescription(G), "\n");

    ccs := CCS(G);
    Print("Number of conjugacy classes: ", Length(ccs), "\n");
    Print("Conjugacy class sizes (sorted):\n  ", ccs, "\n");

    ctv := CTV(G);
    Print("Distinct sizes (", Length(ctv), " values):\n  ", ctv, "\n");

    scoe := SCOE(G);
    Print("(Element order, |C|) sorted by |C|:\n");
    for pair in scoe do
        Print("  (", String(pair[1],2), ", ", String(pair[2],6), ")");
        if pair[2] in [4, 6, 8, 9, 10, 15] then
            Print("  <-- key size");
        fi;
        Print("\n");
    od;
    Print("========================================\n");
od;
```

---

## Output

### Search Summary

```
M = A5 x A5,  |M| = 3600
A = Aut(A5xA5), |A| = 28800
Index [A:M] = 8

Computing intermediate subgroups...
Total candidate groups (including M and A): 10

Filtering rational groups...
  Found rational group of order 7200
  Found rational group of order 14400
  Found rational group of order 14400
  Found rational group of order 28800

Total rational groups found: 4
```

> $M = A_5 \times A_5$ (order 3600) itself is **not** rational. Among the 10 candidate groups, exactly 4 are rational.

### Rational Group #1 — $A_5 \rtimes S_5$ (order 7200)

```
Order:               7200
Index in Aut(A5xA5): 4
Structure:           A5 : S5
Number of conjugacy classes: 26
Conjugacy class sizes (sorted):
  [ 1, 15, 15, 20, 20, 24, 24, 100, 200, 200, 225, 288, 288, 300, 300, 300, 
  300, 360, 360, 400, 400, 480, 480, 600, 600, 900 ]
Distinct sizes (14 values):
  [ 1, 15, 20, 24, 100, 200, 225, 288, 300, 360, 400, 480, 600, 900 ]
(Element order, |C|) sorted by |C|:
  ( 4,      8)  <-- key size
  (12,     12)
  (12,     12)
  (15,     15)  <-- key size
  (15,     15)  <-- key size
  ( 3,     18)
  ( 6,     18)
  (10,     20)
  (10,     20)
  ( 4,     24)
  ( 6,     24)
  ( 6,     24)
  ( 4,     24)
  ( 5,     25)
  ( 5,     25)
  ( 2,     32)
  ( 6,     36)
  ( 6,     36)
  ( 2,     72)
  ( 5,    300)
  ( 5,    300)
  ( 3,    360)
  ( 3,    360)
  ( 2,    480)
  ( 2,    480)
  ( 1,   7200)
```

> Contains $|C| = 8$ (from order-4 elements) and $|C| = 15$ (from order-15 elements). No $|C| = 4, 6, 9, 10$.

### Rational Group #2 — $S_5 \times S_5$ (order 14400)

```
Order:               14400
Index in Aut(A5xA5): 2
Structure:           S5 x S5
Number of conjugacy classes: 49
Conjugacy class sizes (sorted):
  [ 1, 10, 10, 15, 15, 20, 20, 20, 20, 24, 24, 30, 30, 100, 150, 150, 200, 
  200, 200, 200, 225, 240, 240, 300, 300, 300, 300, 300, 300, 360, 360, 400, 
  400, 400, 400, 450, 450, 480, 480, 480, 480, 576, 600, 600, 600, 600, 720, 
  720, 900 ]
Distinct sizes (20 values):
  [ 1, 10, 15, 20, 24, 30, 100, 150, 200, 225, 240, 300, 360, 400, 450, 480, 
  576, 600, 720, 900 ]
(Element order, |C|) sorted by |C|:
  ( 4,     16)
  (20,     20)
  (20,     20)
  (12,     24)
  (12,     24)
  (12,     24)
  (12,     24)
  ( 5,     25)
  (30,     30)
  (15,     30)
  (30,     30)
  (15,     30)
  ( 4,     32)
  ( 4,     32)
  ( 3,     36)
  ( 6,     36)
  ( 6,     36)
  ( 6,     36)
  (10,     40)
  (10,     40)
  ( 6,     48)
  ( 6,     48)
  ( 6,     48)
  ( 4,     48)
  ( 6,     48)
  ( 4,     48)
  (10,     60)
  (10,     60)
  ( 2,     64)
  ( 6,     72)
  ( 6,     72)
  ( 6,     72)
  ( 6,     72)
  ( 2,     96)
  ( 2,     96)
  ( 2,    144)
  ( 4,    480)
  ( 4,    480)
  ( 5,    600)
  ( 5,    600)
  ( 3,    720)
  ( 6,    720)
  ( 6,    720)
  ( 3,    720)
  ( 2,    960)
  ( 2,    960)
  ( 2,   1440)
  ( 2,   1440)
  ( 1,  14400)
```

> $S_5 \times S_5$ has **none** of the key centralizer sizes $\{4, 6, 8, 9, 10, 15\}$. Its minimal nontrivial centralizer size is 16.

### Rational Group #3 — $(A_5 \times A_5) \rtimes (C_2 \times C_2)$ (order 14400)

```
Order:               14400
Index in Aut(A5xA5): 2
Structure:           (A5 x A5) : (C2 x C2)
Number of conjugacy classes: 25
Conjugacy class sizes (sorted):
  [ 1, 30, 40, 48, 60, 60, 100, 225, 288, 288, 400, 400, 400, 600, 600, 720, 
  900, 900, 900, 960, 1200, 1200, 1200, 1440, 1440 ]
Distinct sizes (15 values):
  [ 1, 30, 40, 48, 60, 100, 225, 288, 400, 600, 720, 900, 960, 1200, 1440 ]
(Element order, |C|) sorted by |C|:
  (10,     10)  <-- key size
  (10,     10)  <-- key size
  ( 6,     12)
  ( 6,     12)
  (12,     12)
  (15,     15)  <-- key size
  ( 4,     16)
  ( 4,     16)
  ( 4,     16)
  (10,     20)
  ( 4,     24)
  ( 6,     24)
  ( 3,     36)
  ( 6,     36)
  ( 6,     36)
  ( 5,     50)
  ( 5,     50)
  ( 2,     64)
  ( 2,    144)
  ( 2,    240)
  ( 2,    240)
  ( 5,    300)
  ( 3,    360)
  ( 2,    480)
  ( 1,  14400)
```

> **Critical for Lemma 28:** This is the unique rational group in the lattice that simultaneously contains $|C| = 10$ and $|C| = 15$ (from elements of order 10 and 15 respectively).

### Rational Group #4 — $\mathrm{Aut}(A_5 \times A_5) \cong (A_5 \times A_5) \rtimes D_8$ (order 28800)

```
Order:               28800
Index in Aut(A5xA5): 1
Structure:           (A5 x A5) : D8
Number of conjugacy classes: 35
Conjugacy class sizes (sorted):
  [ 1, 20, 30, 40, 40, 48, 60, 100, 120, 225, 300, 400, 400, 400, 400, 480, 
  576, 600, 600, 600, 720, 800, 900, 900, 960, 960, 1200, 1200, 1200, 1440, 
  1800, 2400, 2400, 2880, 3600 ]
Distinct sizes (24 values):
  [ 1, 20, 30, 40, 48, 60, 100, 120, 225, 300, 400, 480, 576, 600, 720, 800, 
  900, 960, 1200, 1440, 1800, 2400, 2880, 3600 ]
(Element order, |C|) sorted by |C|:
  ( 8,      8)  <-- key size
  (10,     10)  <-- key size
  (12,     12)
  ( 6,     12)
  ( 4,     16)
  (20,     20)
  ( 4,     24)
  (12,     24)
  (12,     24)
  (30,     30)
  (15,     30)
  ( 4,     32)
  ( 4,     32)
  ( 6,     36)
  (10,     40)
  ( 6,     48)
  ( 4,     48)
  ( 6,     48)
  ( 5,     50)
  (10,     60)
  ( 6,     72)
  ( 6,     72)
  ( 6,     72)
  ( 3,     72)
  ( 2,     96)
  ( 2,    128)
  ( 2,    240)
  ( 2,    288)
  ( 4,    480)
  ( 5,    600)
  ( 6,    720)
  ( 3,    720)
  ( 2,    960)
  ( 2,   1440)
  ( 1,  28800)
```

> **Critical for Lemma 27:** This group contains a **self-centralizing element of order 8** ($|C|=8$), as well as $|C|=10$. The existence of such an 8-element triggers the extensive module-extension analysis in Lemma 27.

---

## Summary

### Rational Groups Overview

| \# | Order | Index | Structure | \|C\|=8 | \|C\|=9 | \|C\|=10 | \|C\|=15 |
|---|-------|-------|-----------|:---:|:---:|:----:|:----:|
| 1 | 7,200 | 4 | A₅ ⋊ S₅ | ✓ | ✗ | ✗ | ✓ |
| 2 | 14,400 | 2 | S₅ × S₅ | ✗ | ✗ | ✗ | ✗ |
| 3 | 14,400 | 2 | (A₅×A₅) ⋊ (C₂×C₂) | ✗ | ✗ | ✓ | ✓ |
| 4 | 28,800 | 1 | (A₅×A₅) ⋊ D₈ | ✓ | ✗ | ✓ | ✗ |

# Code 1: Centralizers of Order-2 and Order-4 Elements of $\mathrm{Aut}(R)$ Acting on $R$

## Purpose

This code verifies, for the three simple groups $R = A_5$, $A_6$, $\mathrm{PSp}(4,3)$, the size and structure of the centralizers (i.e., fixed points) in $R$ of all **order-2 elements** (involutions) and **order-4 elements** of $\mathrm{Aut}(R)$.

Concretely, for an automorphism $\alpha \in \mathrm{Aut}(R)$, we compute:

$$C_R(\alpha) = \{ x \in R \mid \alpha(x) = x \}$$

i.e., the subgroup of elements of $R$ fixed by $\alpha$. We are interested in the values of $|C_R(\alpha)|$ and the group structure of $C_R(\alpha)$.

This computation is fundamental to the study of the $S_3$ conjecture: it tells us the size of the fixed-point set of elements of the automorphism group acting on the simple group $R$, thereby constraining the construction of possible rational group extensions.

## Code

```gap
# ============================================================
# Unified function: compute centralizers (fixed points) in G
# of elements of specified orders in Aut(G)
# Parameters:
#   G_name         - name of the group (for display)
#   G              - the group itself
#   orders_to_check - list of orders to inspect, e.g., [2, 4]
# ============================================================
AnalyzeAutomorphismFixedPoints := function(G_name, G, orders_to_check)
    local AutG, InnerAuts, classes, class_data, data, cl, g, C_in_G, size, struct,
          count, type_str, ord, g_sq, sort_key;

    Print("\n========================================\n");
    Print("Analyzing: ", G_name, "\n");
    Print("|G| = ", Order(G), "\n");

    # Compute the automorphism group
    AutG := AutomorphismGroup(G);
    InnerAuts := InnerAutomorphismsAutomorphismGroup(AutG);
    Print("|Aut(G)| = ", Order(AutG), "\n");
    Print("Out(G) order = ", Order(AutG) / Order(InnerAuts), "\n");

    for ord in orders_to_check do
        Print("\n------------------------------------------------------------\n");
        Print(">>> Elements of Order ", ord, " in Aut(", G_name, ")\n");
        Print("------------------------------------------------------------\n");

        # Get conjugacy classes of all elements of order 'ord' in Aut(G)
        classes := ConjugacyClasses(AutG);
        classes := Filtered(classes, c -> Order(Representative(c)) = ord);

        Print("Found ", Length(classes), " conjugacy class(es).\n\n");

        if Length(classes) = 0 then
            Print("No elements of order ", ord, " found.\n");
            continue;
        fi;

        # Precompute all data and sort by (|C_G(g)|, inner/outer, structure)
        # to ensure deterministic output (GAP may return classes in varying order)
        class_data := [];
        for cl in classes do
            g := Representative(cl);
            C_in_G := Subgroup(G, Filtered(G, x -> Image(g, x) = x));
            size := Size(C_in_G);
            struct := StructureDescription(C_in_G);

            if g in InnerAuts then
                type_str := "Inner";
                sort_key := 0;
            elif ord = 2 then
                type_str := "Outer";
                sort_key := 1;
            else
                g_sq := g^2;
                if g_sq in InnerAuts then
                    type_str := "Outer (g^2 inner)";
                    sort_key := 1;
                else
                    type_str := "Outer (g^2 outer)";
                    sort_key := 2;
                fi;
            fi;

            Add(class_data, [size, sort_key, struct, type_str]);
        od;

        # Sort by size, then inner/outer, then structure description
        SortBy(class_data, x -> [x[1], x[2], x[3]]);

        Print("Class | Type               | |C_G(g)|  | Structure of C_G(g)\n");
        Print("-----------------------------------------------------------------------\n");

        count := 1;
        for data in class_data do
            Print(String(count, 5), " | ",
                  String(data[4], 18), " | ",
                  String(data[1], 9), " | ",
                  data[3], "\n");
            count := count + 1;
        od;
    od;
    Print("========================================\n");
end;

# ============================================================
# Compute order-2 and order-4 elements for A5, A6, PSp(4,3)
# ============================================================

Print("\n");
Print("######################################################################\n");
Print("#  Code 1: Centralizers of order-2 and order-4 elements              #\n");
Print("#  of Aut(R) acting on R, for R = A_5, A_6, PSp(4,3)                #\n");
Print("######################################################################\n");

# --- R = A_5 ---
A5 := AlternatingGroup(5);
AnalyzeAutomorphismFixedPoints("A_5", A5, [2, 4]);

# --- R = A_6 ---
A6 := AlternatingGroup(6);
AnalyzeAutomorphismFixedPoints("A_6", A6, [2, 4]);

# --- R = PSp(4,3) ---
PSp43 := PSp(4, 3);
AnalyzeAutomorphismFixedPoints("PSp(4,3)", PSp43, [2, 4]);
```

## Output

> **Note:** The conjugacy classes are sorted by $|C_R(g)|$ for determinism. The `StructureDescription` strings for large subgroups may differ between GAP runs (different but isomorphic descriptions); the sizes $|C_R(g)|$ are the invariant quantities.

```
######################################################################
#  Code 1: Centralizers of order-2 and order-4 elements              #
#  of Aut(R) acting on R, for R = A_5, A_6, PSp(4,3)                #
######################################################################

========================================
Analyzing: A_5
|G| = 60
|Aut(G)| = 120
Out(G) order = 2

------------------------------------------------------------
>>> Elements of Order 2 in Aut(A_5)
------------------------------------------------------------
Found 2 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |              Inner |         4 | C2 x C2
    2 |              Outer |         6 | S3

------------------------------------------------------------
>>> Elements of Order 4 in Aut(A_5)
------------------------------------------------------------
Found 1 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |  Outer (g^2 inner) |         2 | C2
========================================

========================================
Analyzing: A_6
|G| = 360
|Aut(G)| = 1440
Out(G) order = 4

------------------------------------------------------------
>>> Elements of Order 2 in Aut(A_6)
------------------------------------------------------------
Found 3 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |              Inner |         8 | D8
    2 |              Outer |        10 | D10
    3 |              Outer |        24 | S4

------------------------------------------------------------
>>> Elements of Order 4 in Aut(A_6)
------------------------------------------------------------
Found 3 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |  Outer (g^2 inner) |         2 | C2
    2 |              Inner |         4 | C4
    3 |  Outer (g^2 inner) |         4 | C4
========================================

========================================
Analyzing: PSp(4,3)
|G| = 25920
|Aut(G)| = 51840
Out(G) order = 2

------------------------------------------------------------
>>> Elements of Order 2 in Aut(PSp(4,3))
------------------------------------------------------------
Found 4 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |              Outer |        48 | C2 x S4
    2 |              Inner |        96 | (C2 x C2 x A4) : C2
    3 |              Inner |       576 | (((C2 x C2 x C2) : (C2 x C2)) : (C3 x C3)) : C2
    4 |              Outer |       720 | S6

------------------------------------------------------------
>>> Elements of Order 4 in Aut(PSp(4,3))
------------------------------------------------------------
Found 4 conjugacy class(es).

Class | Type               | |C_G(g)|  | Structure of C_G(g)
-----------------------------------------------------------------------
    1 |              Inner |         8 | C4 x C2
    2 |  Outer (g^2 inner) |        16 | (C4 x C2) : C2
    3 |              Inner |        48 | ((C4 x C2) : C2) : C3
    4 |  Outer (g^2 inner) |        48 | A4 : C4
========================================
```

## Summary of Results

**$R = A_5$** ($|\mathrm{Aut}(A_5)| = 120$, $\mathrm{Out}(A_5) \cong C_2$)

| order | type | $C_R(g)$ |
|-------|------|----------|
| 2 | inner | $C_2 \times C_2$ (size 4) |
| 2 | outer | $S_3$ (size 6) |
| 4 | outer ($g^2$ inner) | $C_2$ (size 2) |

**$R = A_6$** ($|\mathrm{Aut}(A_6)| = 1440$, $\mathrm{Out}(A_6) \cong C_2 \times C_2$)

| order | type | $C_R(g)$ |
|-------|------|----------|
| 2 | inner | $D_8$ (size 8) |
| 2 | outer | $D_{10}$ (size 10) |
| 2 | outer | $S_4$ (size 24) |
| 4 | outer ($g^2$ inner) | $C_2$ (size 2) |
| 4 | inner | $C_4$ (size 4) |
| 4 | outer ($g^2$ inner) | $C_4$ (size 4) |

**$R = \mathrm{PSp}(4,3)$** ($|\mathrm{Aut}(\mathrm{PSp}(4,3))| = 51840$, $\mathrm{Out}(\mathrm{PSp}(4,3)) \cong C_2$)

| order | type | $C_R(g)$ |
|-------|------|----------|
| 2 | outer | $C_2 \times S_4$ (size 48) |
| 2 | inner | $(C_2^2 \times A_4) \rtimes C_2$ (size 96) |
| 2 | inner | $((C_2^3 \rtimes C_2^2) \rtimes C_3^2) \rtimes C_2$ (size 576) |
| 2 | outer | $S_6$ (size 720) |
| 4 | inner | $C_4 \times C_2$ (size 8) |
| 4 | outer ($g^2$ inner) | $(C_4 \times C_2) \rtimes C_2$ (size 16) |
| 4 | inner | $((C_4 \times C_2) \rtimes C_2) \rtimes C_3$ (size 48) |
| 4 | outer ($g^2$ inner) | $A_4 \rtimes C_4$ (size 48) |

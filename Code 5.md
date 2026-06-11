# Code 5: Exclusion of Rational Groups with Order-9 Elements Having $|C| = 9$, for $R = A_5 \times A_5 \times A_5$

## Purpose

Let $R = A_5 \times A_5 \times A_5$. This code verifies that among all groups $G$ satisfying $R \leq G \leq \mathrm{Aut}(R)$, **there is no rational group that contains an element of order $9$ whose centralizer has size exactly $9$**.

This is a computational lemma used in the proof of the $S_3$ conjecture: in the case analysis where $|g| = 9$, the existence of a rational quotient group with $|C(g)| = 9$ would lead to a contradiction. The verification rules out this possibility for $R = A_5 \times A_5 \times A_5$.

The computation uses three key optimizations to avoid the $\sim\!10^7$-order bottleneck:

1. **Permutation group conversion** — $\mathrm{Aut}(R)$ is computed abstractly and mapped to a permutation group via `IsomorphismPermGroup`, so that all subgroup and conjugacy class operations run in the permutation group machinery.
2. **Sylow-based order-9 search** — Instead of iterating over all conjugacy classes, we search for order-$9$ elements directly inside a Sylow $3$-subgroup (which is small). This makes Condition A (existence of an order-$9$ element with $|C| = 9$) an almost instant check.
3. **Rationality only when needed** — The expensive rationality test (Condition B) is performed only if Condition A already holds. The rationality test itself uses the fast membership test `rep^k in c` rather than the slower `IsConjugate`.

---

## Code

```gap
VerifyNoSuchGroup := function()
    local A5, R, AutR, iso, P_AutR, P_R, intermediate,
          G, P3, elems, x, has_condA, is_rational, classes, c, rep, ord, k;

    Print("1. Constructing permutation group representations of R and Aut(R)...\n");
    A5 := AlternatingGroup(5);
    R := DirectProduct(A5, A5, A5);
    AutR := AutomorphismGroup(R);

    # Core optimization 1: map abstract automorphism group to a permutation group
    iso := IsomorphismPermGroup(AutR);
    P_AutR := Image(iso, AutR);
    # Since A5 has trivial center (Z(R) = 1), R is naturally isomorphic to
    # the inner automorphism group of R, which is a subgroup of Aut(R)
    P_R := Image(iso, InnerAutomorphismsAutomorphismGroup(AutR));

    Print("2. Extracting intermediate subgroups between R and Aut(R)...\n");
    # Collect conjugacy class representatives, then add both endpoints
    intermediate := IntermediateSubgroups(P_AutR, P_R).subgroups;
    Add(intermediate, P_R);
    Add(intermediate, P_AutR);
    Print("   Found ", Length(intermediate),
          " conjugacy class representatives to check.\n\n");

    Print("3. Testing the two conditions:\n");
    Print("   Condition A: there exists an element of order 9 with |C| = 9.\n");
    Print("   Condition B: the group is rational.\n\n");

    for G in intermediate do
        has_condA := false;

        # Core optimization 2: use Sylow 3-subgroup to find order-9 elements
        P3 := SylowSubgroup(G, 3);
        elems := Elements(P3);
        for x in elems do
            if Order(x) = 9 then
                if Size(Centralizer(G, x)) = 9 then
                    has_condA := true;
                    break;
                fi;
            fi;
        od;

        # Only run the expensive rationality check if Condition A holds
        if has_condA then
            is_rational := true;
            classes := ConjugacyClasses(G);
            for c in classes do
                rep := Representative(c);
                ord := Order(rep);

                if ord > 2 then
                    for k in Filtered([1..ord], i -> Gcd(i, ord) = 1) do
                        # Core optimization 3: membership test is faster
                        # than IsConjugate
                        if not rep^k in c then
                            is_rational := false;
                            break;
                        fi;
                    od;
                fi;

                if not is_rational then
                    break;
                fi;
            od;

            # If both conditions hold, we have found a counterexample
            if is_rational then
                Print(">>> VERIFICATION FAILED: found a group satisfying both conditions!\n");
                Print("    Group order: ", Size(G), "\n");
                return false;
            fi;
        fi;
    od;

    Print(">>> VERIFICATION PASSED: between R and Aut(R), there is no\n");
    Print("    rational group containing an element of order 9 with |C| = 9.\n");
    return true;
end;

Print("\n");
Print("######################################################################\n");
Print("#  Code 5: Exclusion of Rational Groups with Order-9 Elements       #\n");
Print("#  having |C| = 9, for R = A5 x A5 x A5                            #\n");
Print("######################################################################\n\n");

VerifyNoSuchGroup();
```

---

## Output

```
######################################################################
#  Code 5: Exclusion of Rational Groups with Order-9 Elements       #
#  having |C| = 9, for R = A5 x A5 x A5                            #
######################################################################

1. Constructing permutation group representations of R and Aut(R)...
2. Extracting intermediate subgroups between R and Aut(R)...
   Found 98 conjugacy class representatives to check.

3. Testing the two conditions:
   Condition A: there exists an element of order 9 with |C| = 9.
   Condition B: the group is rational.

>>> VERIFICATION PASSED: between R and Aut(R), there is no
    rational group containing an element of order 9 with |C| = 9.
```

---

## Summary

**Conclusion:** For $R = A_5 \times A_5 \times A_5$, among all $98$ groups between $R$ and $\mathrm{Aut}(R)$, **no rational group contains an element of order $9$ whose centralizer has size exactly $9$**. 

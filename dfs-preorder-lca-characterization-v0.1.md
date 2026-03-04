# Preorder DFS: Declarative Characterization via LCA

Working Document v0.1 — March 2026

---

## 1. Definitions

### 1.1 Finite Ordered Tree

A **finite ordered tree** T = (N, parent, r, sib) consists of:

- A finite set of nodes N
- A root r ∈ N
- A parent function parent : N \ {r} → N
- A sibling ordering sib : N × N → Bool, where for each node v,
  sib restricted to the children of v is a strict total order

**Derived notions:**

- children(v) = {u ∈ N : parent(u) = v}
- x ≤_A y (ancestor): x = y, or x = parent(y'), where y' ≤_A y
  Equivalently: x is on the unique path from y to r.
- x <_A y (proper ancestor): x ≤_A y and x ≠ y

Standard properties (assumed/easily proved for finite trees):
- A1. ≤_A is a partial order.
- A2. r ≤_A x for all x.
- A3. For all x, the set {y : y ≤_A x} is totally ordered by ≤_A.
  (The path from x to r is a chain.)

### 1.2 LCA and child_toward

**lca(x, y):** The unique deepest common ancestor of x and y.

Formally: lca(x, y) is the unique a such that:
  (i)  a ≤_A x and a ≤_A y
  (ii) For all a', if a' ≤_A x and a' ≤_A y, then a' ≤_A a

Existence and uniqueness follow from A2 (r is a common ancestor)
and A3 (ancestors of x form a chain, ancestors of y form a chain;
the intersection of two chains is a chain, and a finite chain has
a maximum).

**child_toward(a, x):** Defined when a <_A x. The unique c such that:
  (i)  parent(c) = a
  (ii) c ≤_A x

Existence: Since a <_A x, there is a path from a to x. The first
step on that path is a child of a that is an ancestor of x.

Uniqueness: If c₁ ≠ c₂ are both children of a with c₁ ≤_A x and
c₂ ≤_A x, then c₁ and c₂ are both ancestors of x, contradicting
A3 (ancestors of x are totally ordered) unless one is an ancestor
of the other, but siblings can't be ancestors of each other (that
would create a cycle).

**Key property (CT-compose):**
If a <_A b ≤_A x, then child_toward(a, x) = child_toward(a, b).

Proof: child_toward(a, x) is the child c of a with c ≤_A x.
Since a <_A b ≤_A x, b is a descendant of a and an ancestor of x.
child_toward(a, b) is the child c' of a with c' ≤_A b.
Since c' ≤_A b ≤_A x, c' is also an ancestor of x.
By uniqueness of child_toward(a, x): c = c'. ∎

### 1.3 DFS Preorder

**Definition.** The DFS preorder traversal of a rooted ordered tree
is the list defined recursively:

```
dfs(v) = [v] ++ concat [dfs(c) for c in children(v) ordered by sib]
```

The full traversal is dfs(r).

**Notation:** We write pos(x) for the 0-indexed position of node x
in dfs(r). This is well-defined since (as we will prove) each node
appears exactly once.

### 1.4 The Two Orderings

**DFS order (≤_D):** x <_D y iff pos(x) < pos(y).

**LCA order (≤_L):** For distinct x, y:

```
x <_L y  ⟺
  let a = lca(x, y) in
    (a = x)
    ∨ (a ≠ x ∧ a ≠ y ∧ sib(child_toward(a, x), child_toward(a, y)))
```

Cases:
- a = x: x <_L y  (ancestor comes first)
- a = y: ¬(x <_L y)  (descendant comes after)
- a ≠ x, a ≠ y: x <_L y iff child_toward(a, x) precedes
  child_toward(a, y) in the sibling ordering at a

---

## 2. DFS Properties

### 2.1 Completeness and Uniqueness

**Theorem 2.1.** Every node appears exactly once in dfs(r).

*Proof.* By structural induction on the tree.

**Base:** If T consists of only the root r, then dfs(r) = [r]. ✓

**Inductive step:** Let r have children c₁, ..., cₖ. By induction,
dfs(cᵢ) contains exactly the nodes in the subtree rooted at cᵢ,
each exactly once. The subtrees are disjoint (a node has exactly
one parent). So:

dfs(r) = [r] ++ dfs(c₁) ++ ... ++ dfs(cₖ)

contains r (once) plus every node in each subtree (once each).
Since every non-root node is in exactly one subtree, every node
appears exactly once. ∎

**Corollary 2.2.** pos : N → {0, ..., |N|-1} is a bijection.

**Corollary 2.3.** <_D is a strict total order on N.

### 2.2 Subtree Contiguity

**Theorem 2.4 (Subtree Contiguity).** For any node v, the positions
of nodes in subtree(v) = {u : v ≤_A u} form a contiguous interval
in the DFS ordering, starting at pos(v).

*Proof.* By structural induction.

**Base:** subtree(v) = {v} when v is a leaf. Interval [pos(v), pos(v)]. ✓

**Inductive step:** Let v have children c₁, ..., cₖ (in sib order).
By induction, subtree(cᵢ) occupies a contiguous interval starting
at pos(cᵢ). By the DFS definition:

dfs(v) = [v] ++ dfs(c₁) ++ ... ++ dfs(cₖ)

So the positions are:
  pos(v), then subtree(c₁), then subtree(c₂), ..., then subtree(cₖ)

Each subtree(cᵢ) is contiguous (by IH) and they are laid out
consecutively. So subtree(v) occupies [pos(v), pos(v) + |subtree(v)| - 1]. ∎

**Corollary 2.5 (Ancestor Precedes Descendant).**
If x <_A y, then pos(x) < pos(y), i.e., x <_D y.

*Proof.* y ∈ subtree(x) and y ≠ x. By Theorem 2.4, the interval
for subtree(x) starts at pos(x). Since x itself is at pos(x) and
y is a different element in the interval, pos(y) > pos(x). ∎

### 2.3 Sibling Subtree Ordering

**Theorem 2.6 (Sibling Subtree Ordering).** Let c₁, c₂ be children
of the same node v with sib(c₁, c₂) (c₁ precedes c₂ in sibling
order). Then for all u₁ ∈ subtree(c₁) and u₂ ∈ subtree(c₂):

pos(u₁) < pos(u₂)

*Proof.* By the DFS definition:
  dfs(v) = [v] ++ dfs(c₁) ++ ... ++ dfs(c₂) ++ ...

Since sib(c₁, c₂), dfs(c₁) appears entirely before dfs(c₂).
By Theorem 2.1, u₁ appears in dfs(c₁) and u₂ in dfs(c₂).
So pos(u₁) < pos(u₂). ∎

---

## 3. The Characterization Theorem

### 3.1 Statement

**Theorem 3.1.** For all distinct x, y ∈ N:

```
x <_D y  ⟺  x <_L y
```

### 3.2 Proof: <_D implies <_L

Assume x <_D y (i.e., pos(x) < pos(y)). We show x <_L y.

Let a = lca(x, y).

**Case a = x.** Then x <_L y by the first disjunct of the definition. ✓

**Case a = y.** Then y <_A x. By Corollary 2.5, pos(y) < pos(x).
But we assumed pos(x) < pos(y). Contradiction. ✗ (This case cannot occur.)

**Case a ≠ x and a ≠ y.** Let cx = child_toward(a, x), cy = child_toward(a, y).
cx ≠ cy (otherwise lca(x, y) would be deeper than a).

x ∈ subtree(cx) and y ∈ subtree(cy). Since pos(x) < pos(y), by
Theorem 2.6 (contrapositive applied to both orderings), we must
have sib(cx, cy). (If sib(cy, cx) held, Theorem 2.6 would give
pos(y') < pos(x') for all y' in subtree(cy) and x' in subtree(cx),
contradicting pos(x) < pos(y).)

So sib(cx, cy), which gives x <_L y by the second disjunct. ✓ ∎

### 3.3 Proof: <_L implies <_D

Assume x <_L y. We show x <_D y (i.e., pos(x) < pos(y)).

Let a = lca(x, y).

**Case a = x (ancestor case).** x <_A y (proper, since x ≠ y).
By Corollary 2.5: pos(x) < pos(y). ✓

**Case a ≠ x, a ≠ y (sibling case).** The LCA definition gives
sib(cx, cy) where cx = child_toward(a, x), cy = child_toward(a, y).

x ∈ subtree(cx), y ∈ subtree(cy), and sib(cx, cy).
By Theorem 2.6: pos(x) < pos(y). ✓ ∎

### 3.4 Summary

The characterization theorem follows directly from three DFS
properties:

1. **Corollary 2.5** (ancestors precede descendants): handles the
   ancestor case (a = x or a = y).

2. **Theorem 2.6** (sibling subtree ordering): handles the sibling
   case (a ≠ x, a ≠ y).

3. **Theorem 2.1** (each node appears once): ensures the DFS order
   is well-defined and total.

Each of these is a clean structural induction on the tree.

---

## 4. Consequences

### 4.1 Total Order

**Corollary 4.1.** <_L is a strict total order.

*Proof.* <_L = <_D (Theorem 3.1), and <_D is a strict total order
(Corollary 2.3). ∎

This is the "free" proof of P1 that avoids the direct case analysis
on LCA configurations. Irreflexivity, totality, and transitivity
are all inherited from the DFS sequence.

### 4.2 Stability

**Corollary 4.2 (Stability).** Adding a new leaf to the tree does
not change the relative <_L ordering of existing nodes.

*Proof.* Adding leaf ℓ as a child of some node v: the DFS changes
by inserting ℓ into the traversal at a specific position (among v's
children, according to sib). All existing nodes retain their
relative positions in the traversal (the DFS of every other subtree
is unchanged). So <_D, and hence <_L, is unchanged for existing
pairs. ∎

### 4.3 Extends Ancestor Order

**Corollary 4.3.** If x <_A y, then x <_L y.

*Proof.* Immediate from Corollary 2.5 and Theorem 3.1. ∎

---

## 5. Discussion

### 5.1 Proof Structure

The overall structure is:

```
             DFS properties (structural induction)
                    |
                    v
    <_D is a total order + subtree contiguity + sibling ordering
                    |
                    v
         Characterization: <_D = <_L
                    |
                    v
       <_L is a total order (inherited from <_D)
```

The key insight is that proving properties of <_L (the declarative,
LCA-based definition) is much easier by going through <_D (the
algorithmic definition) than by direct case analysis on the formula.
The DFS properties are clean structural inductions; the
characterization theorem is a short case split with two cases.

The direct proof of transitivity for <_L (see rga-order-total-order-
proof-v0.1) required ~10 cases. The indirect proof via <_D requires
zero case analysis for transitivity — it's inherited.

### 5.2 Generality

Nothing in this development is specific to RGA or distributed
systems. The result holds for any finite rooted tree with any
sibling ordering. RGA specializes by choosing sib to be reverse <_T
(newest timestamp first).

### 5.3 For Mechanization

The proof has a clean dependency structure:

**Layer 0: Tree definitions.**
  - Finite rooted tree with ordered children
  - Ancestor relation, LCA, child_toward
  - Their basic properties (A1-A3, LCA existence/uniqueness,
    CT-compose)

**Layer 1: DFS definition and properties.**
  - dfs(v) as a recursive function on the tree
  - Theorem 2.1 (each node once) — structural induction
  - Theorem 2.4 (subtree contiguity) — structural induction
  - Theorem 2.6 (sibling subtree ordering) — from DFS definition

**Layer 2: Characterization.**
  - Theorem 3.1 (<_D = <_L) — case split using Layer 1

**Layer 3: Consequences.**
  - Corollary 4.1 (total order) — immediate
  - Corollary 4.2 (stability) — DFS argument
  - Corollary 4.3 (extends ancestor order) — immediate

Layers 0 and 1 are the main implementation effort. Layer 0 may
partially exist in proof assistant libraries (Lean's Mathlib has
tree types; Isabelle's HOL has extensive order theory). Layer 1
is straightforward recursive function definition + structural
induction.

### 5.4 Candidate Proof Assistants

**Lean 4:** Natural fit. Trees as inductive types, DFS as recursive
definition, structural induction built in. Mathlib has order theory.
List operations and their properties are well-supported.

**Isabelle/HOL:** Also natural. Isar proof language for readable
proofs. Strong automation (simp, auto) could discharge many steps.
Existing libraries for trees may help.

For either: the main effort is Layer 0 (tree infrastructure).
The proofs themselves (Layers 1-3) should be compact.

### 5.5 Relationship to the OT Proof

The OT correctness proof needs to reason about *pairs* of elements:
"element a is at position i" and "after rebasing past b, a is at
position i+1." This pairwise reasoning maps directly to the <_L
formula (which is defined pointwise on pairs) rather than to the
DFS traversal (which is a global computation).

So the workflow is:
1. Define <_L (the formula the OT proof actually uses).
2. Prove <_L = <_D (this document).
3. Use <_L properties freely in the OT proof, knowing they're
   sound because <_L inherits everything from <_D.

The OT proof never needs to reference DFS directly. It works with
the LCA formula, confident that it describes a total order.

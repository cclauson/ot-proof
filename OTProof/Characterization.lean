/-
# Layer 2: The Characterization Theorem

Theorem 3.1: dfsLt x y t ↔ lcaLt x y t

Following §3 of dfs-preorder-lca-characterization-v0.1.md.
-/
import OTProof.DFS

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## The two orderings -/

/-- DFS ordering: `x` appears before `y` in the DFS traversal of `t`. -/
def dfsLt (x y : α) (t : OrdTree α) : Prop :=
  PrecedesIn x y t.dfs

/-- LCA ordering (§1.4): the declarative ordering based on LCA and child_toward.
    For distinct x, y:
    - If lca(x,y) = x, then x <_L y  (ancestor comes first)
    - If lca(x,y) = y, then ¬(x <_L y)
    - Otherwise, x <_L y iff child_toward(lca, x) precedes child_toward(lca, y)
      in sibling order -/
def lcaLt (x y : α) (t : OrdTree α) : Prop :=
  ∃ a, IsLCA a x y t ∧
    (a = x ∨
     (a ≠ x ∧ a ≠ y ∧
      ∃ cx cy, IsChildToward cx a x t ∧ IsChildToward cy a y t ∧
        SibLt cx cy t))

/-! ## Main theorem -/

/-- **Theorem 3.1 (→)**: LCA order implies DFS order.

    Proof sketch: Assume x <_L y. Let a = lca(x,y).
    - Case a = x: x is proper ancestor of y. By Cor 2.5, pos(x) < pos(y).
    - Case a ≠ x, a ≠ y: sib(cx, cy) where cx = child_toward(a,x),
      cy = child_toward(a,y). By Theorem 2.6, pos(x) < pos(y). -/
theorem dfsLt_of_lcaLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y)
    (h : lcaLt x y t) : dfsLt x y t := by
  sorry

/-- **Theorem 3.1 (←)**: DFS order implies LCA order.

    Proof sketch: Let a = lca(x,y).
    - Case a = x: x <_L y by the first disjunct.
    - Case a = y: y is ancestor of x, so y precedes x in DFS (Cor 2.5),
      contradicting x <_D y.
    - Case a ≠ x, a ≠ y: Let cx = child_toward(a,x), cy = child_toward(a,y).
      Since pos(x) < pos(y), by Theorem 2.6 (contrapositive), sib(cx, cy).
      So x <_L y by the second disjunct. -/
theorem lcaLt_of_dfsLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y)
    (h : dfsLt x y t) : lcaLt x y t := by
  sorry

/-- **Theorem 3.1**: The DFS ordering and LCA ordering coincide. -/
theorem dfsLt_iff_lcaLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y) :
    dfsLt x y t ↔ lcaLt x y t :=
  ⟨lcaLt_of_dfsLt hd hx hy hne, dfsLt_of_lcaLt hd hx hy hne⟩

end OrdTree

end OTProof

/-
# Layer 1: DFS Definition and Properties

DFS preorder traversal and its key properties:
- Theorem 2.1: Each node appears exactly once
- Theorem 2.4: Subtree contiguity
- Corollary 2.5: Ancestor precedes descendant
- Theorem 2.6: Sibling subtree ordering

Following §2 of dfs-preorder-lca-characterization-v0.1.md.
-/
import OTProof.OrdTree

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## DFS definition -/

/-- DFS preorder traversal is the same as `toList`. -/
abbrev dfs : OrdTree α → List α := toList

/-! ## Helper: precedence in a list -/

/-- `PrecedesIn x y l` means `x` appears before `y` in list `l`. -/
def PrecedesIn (x y : α) (l : List α) : Prop :=
  ∃ (pre mid suf : List α), l = pre ++ x :: mid ++ y :: suf

/-! ## Theorem 2.1: Completeness and Uniqueness -/

/-- **Theorem 2.1**: In a tree with distinct labels, each node appears exactly
    once in the DFS traversal — i.e., the DFS list has no duplicates. -/
theorem dfs_nodup {t : OrdTree α} (hd : t.Distinct) :
    t.dfs.Nodup :=
  hd

/-- Every member of the tree appears in the DFS list. -/
theorem mem_dfs_of_mem {x : α} {t : OrdTree α} (h : x ∈ t) :
    x ∈ t.dfs :=
  h

/-- Every element in the DFS list is a member of the tree. -/
theorem mem_of_mem_dfs {x : α} {t : OrdTree α} (h : x ∈ t.dfs) :
    x ∈ t :=
  h

/-! ## Subtree DFS -/

/-- The DFS of the subtree rooted at `v` (returns [] if v not found). -/
def subtreeDfs [DecidableEq α] (v : α) : OrdTree α → List α
  | node a cs =>
    if a = v then (node a cs).dfs
    else cs.flatMap fun c => subtreeDfs v c

/-- The DFS of a child subtree is a sublist of the parent's DFS. -/
theorem dfs_child_sublist {c : OrdTree α} {a : α} {cs : List (OrdTree α)}
    (hc : c ∈ cs) :
    c.dfs.Sublist (node a cs).dfs := by
  sorry

/-! ## Theorem 2.4: Subtree Contiguity -/

/-- **Theorem 2.4 (Subtree Contiguity)**: The DFS of a subtree rooted at `v`
    appears as a contiguous block in the DFS of the full tree. -/
theorem dfs_subtree_contiguous [DecidableEq α] {v : α} {t : OrdTree α}
    (hd : t.Distinct) (hv : v ∈ t) :
    ∃ (pre suf : List α),
      t.dfs = pre ++ (subtreeDfs v t) ++ suf := by
  sorry

/-! ## Corollary 2.5: Ancestor Precedes Descendant -/

/-- **Corollary 2.5**: If `x` is a proper ancestor of `y`, then `x` appears
    before `y` in the DFS traversal. -/
theorem ancestor_precedes_in_dfs [DecidableEq α] {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn x y t) :
    PrecedesIn x y t.dfs := by
  sorry

/-! ## Theorem 2.6: Sibling Subtree Ordering -/

/-- **Theorem 2.6**: If `c₁` precedes `c₂` in the children list of their
    parent, then every node in `subtree(c₁)` precedes every node in
    `subtree(c₂)` in the DFS. -/
theorem sibling_subtree_ordering [DecidableEq α]
    {u₁ u₂ c₁ c₂ : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hsib : SibLt c₁ c₂ t)
    (hu₁ : IsAncestorIn c₁ u₁ t ∨ c₁ = u₁)
    (hu₂ : IsAncestorIn c₂ u₂ t ∨ c₂ = u₂) :
    PrecedesIn u₁ u₂ t.dfs := by
  sorry

end OrdTree

end OTProof

/-
# Layer 3: Consequences

- Corollary 4.1: lcaLt is a strict total order (for distinct elements)
- Corollary 4.3: Ancestor implies lcaLt

Following §4 of dfs-preorder-lca-characterization-v0.1.md.
-/
import OTProof.OrderedTree.Characterization

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## PrecedesIn transitivity (needed for lcaLt transitivity) -/

/-- PrecedesIn is transitive in a Nodup list. -/
theorem precedesIn_trans {x y z : α} {l : List α}
    (hnd : l.Nodup) (_hyz : y ≠ z)
    (hxy : PrecedesIn x y l) (hyz_p : PrecedesIn y z l) :
    PrecedesIn x z l := by
  obtain ⟨pre₁, mid₁, suf₁, rfl⟩ := hxy
  have hy_not₁ : y ∉ pre₁ ++ x :: mid₁ := fun h =>
    List.disjoint_of_nodup_append hnd h (List.mem_cons_self ..)
  obtain ⟨pre₂, mid₂, suf₂, h₂⟩ := hyz_p
  rcases List.append_eq_append_iff.mp h₂ with ⟨a', ha₁, ha₂⟩ | ⟨c', hc₁, hc₂⟩
  · -- z ∈ y :: suf₁
    exact precedesIn_of_mem_append
      (List.mem_append_right _ (List.mem_cons_self ..))
      (ha₂ ▸ List.mem_append_right _ (List.mem_cons_self ..))
  · -- y ∈ pre₁ ++ x :: mid₁, contradiction
    exact absurd (hc₁ ▸ List.mem_append_left _
      (List.mem_append_right _ (List.mem_cons_self ..))) hy_not₁

/-! ## Corollary 4.1: lcaLt is a strict total order -/

/-- dfsLt is irreflexive (PrecedesIn x x is impossible in a Nodup list). -/
theorem dfsLt_irrefl {t : OrdTree α} (hd : t.Distinct) (x : α) :
    ¬dfsLt x x t := by
  intro h
  exact h.ne_of_nodup (dfs_nodup hd) rfl

/-- lcaLt is irreflexive: immediate from the `x ≠ y` condition in lcaLt. -/
theorem lcaLt_irrefl (x : α) (t : OrdTree α) :
    ¬lcaLt x x t := fun ⟨hne, _⟩ => hne rfl

/-- **Corollary 4.1 (transitivity)**: lcaLt is transitive.
    Inherited from dfsLt via Theorem 3.1. -/
theorem lcaLt_trans {x y z : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hz : z ∈ t)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h₁ : lcaLt x y t) (h₂ : lcaLt y z t) :
    lcaLt x z t :=
  lcaLt_of_dfsLt hd hx hz hxz
    (precedesIn_trans (dfs_nodup hd) hyz
      (dfsLt_of_lcaLt hd hx hy hxy h₁)
      (dfsLt_of_lcaLt hd hy hz hyz h₂))

/-- **Corollary 4.1 (totality)**: For distinct members, either x <_L y or y <_L x.
    Inherited from dfsLt via Theorem 3.1. -/
theorem lcaLt_total {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y) :
    lcaLt x y t ∨ lcaLt y x t := by
  rcases precedesIn_total (dfs_nodup hd) hx hy hne with h | h
  · exact Or.inl (lcaLt_of_dfsLt hd hx hy hne h)
  · exact Or.inr (lcaLt_of_dfsLt hd hy hx hne.symm h)

/-! ## Corollary 4.3: Ancestor implies lcaLt -/

/-- **Corollary 4.3**: If x is a proper ancestor of y, then x <_L y.
    Immediate from Corollary 2.5 and Theorem 3.1. -/
theorem lcaLt_of_ancestor {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn x y t) :
    lcaLt x y t :=
  lcaLt_of_dfsLt hd (isAncestorIn_mem_left h.1) (isAncestorIn_mem_right h.1) h.2
    (ancestor_precedes_in_dfs hd h)

end OrdTree

end OTProof

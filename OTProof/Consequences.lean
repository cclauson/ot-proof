/-
# Layer 3: Consequences

- Corollary 4.1: lcaLt is a strict total order
- Corollary 4.3: Ancestor implies lcaLt

Following §4 of dfs-preorder-lca-characterization-v0.1.md.
-/
import OTProof.Characterization

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## Corollary 4.1: lcaLt is a strict total order -/

/-- lcaLt is irreflexive. -/
theorem lcaLt_irrefl {t : OrdTree α} (hd : t.Distinct) (x : α) (hx : x ∈ t) :
    ¬lcaLt x x t := by
  sorry

/-- **Corollary 4.1 (transitivity)**: lcaLt is transitive.
    Inherited from dfsLt via Theorem 3.1. -/
theorem lcaLt_trans {x y z : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hz : z ∈ t)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h₁ : lcaLt x y t) (h₂ : lcaLt y z t) :
    lcaLt x z t := by
  sorry

/-- **Corollary 4.1 (totality)**: For distinct members, either x <_L y or y <_L x.
    Inherited from dfsLt via Theorem 3.1. -/
theorem lcaLt_total {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y) :
    lcaLt x y t ∨ lcaLt y x t := by
  sorry

/-! ## Corollary 4.3: Ancestor implies lcaLt -/

/-- **Corollary 4.3**: If x is a proper ancestor of y, then x <_L y.
    Immediate from Corollary 2.5 and Theorem 3.1. -/
theorem lcaLt_of_ancestor {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn x y t) :
    lcaLt x y t := by
  sorry

end OrdTree

end OTProof

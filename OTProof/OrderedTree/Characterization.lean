/-
# Layer 2: The Characterization Theorem

Theorem 3.1: dfsLt x y t ↔ lcaLt x y t

Following §3 of dfs-preorder-lca-characterization-v0.1.md.
-/
import OTProof.OrderedTree.DFS

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## The two orderings -/

/-- DFS ordering: `x` appears before `y` in the DFS traversal of `t`. -/
def dfsLt (x y : α) (t : OrdTree α) : Prop :=
  PrecedesIn x y t.dfs

/-- LCA ordering (§1.4): the declarative ordering based on LCA and child_toward.
    Includes `x ≠ y` so that the relation is irreflexive. -/
def lcaLt (x y : α) (t : OrdTree α) : Prop :=
  x ≠ y ∧ ∃ a, IsLCA a x y t ∧
    (a = x ∨
     (a ≠ x ∧ a ≠ y ∧
      ∃ cx cy, IsChildToward cx a x t ∧ IsChildToward cy a y t ∧
        SibLt cx cy t))

/-! ## PrecedesIn helpers for the characterization -/

/-- In a Nodup list, PrecedesIn x y implies x ≠ y.
    Note: `pre ++ x :: mid ++ y :: suf` parses as `(pre ++ (x :: mid)) ++ (y :: suf)`. -/
theorem PrecedesIn.ne_of_nodup {x y : α} {l : List α}
    (hp : PrecedesIn x y l) (hnd : l.Nodup) : x ≠ y := by
  obtain ⟨pre, mid, suf, rfl⟩ := hp
  intro heq; subst heq
  -- hnd : ((pre ++ x :: mid) ++ (x :: suf)).Nodup
  have hx_in : x ∈ pre ++ x :: mid :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hx_in₂ : x ∈ x :: suf := List.mem_cons_self ..
  exact List.disjoint_of_nodup_append hnd hx_in hx_in₂

/-- In a Nodup list, PrecedesIn x y and PrecedesIn y x cannot both hold. -/
theorem precedesIn_antisymm {x y : α} {l : List α}
    (hnd : l.Nodup) (hxy : PrecedesIn x y l) (hyx : PrecedesIn y x l) : False := by
  obtain ⟨pre₁, mid₁, suf₁, rfl⟩ := hxy
  -- hnd : ((pre₁ ++ x :: mid₁) ++ (y :: suf₁)).Nodup
  have hdisj := List.disjoint_of_nodup_append hnd
  have hx_in₁ : x ∈ pre₁ ++ x :: mid₁ :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hne : x ≠ y := fun h => hdisj hx_in₁ (h ▸ List.mem_cons_self ..)
  have hx_not_suf : x ∉ suf₁ := fun h => hdisj hx_in₁ (List.mem_cons_of_mem _ h)
  -- From Nodup of RHS form (needed for case 2)
  obtain ⟨pre₂, mid₂, suf₂, h₂⟩ := hyx
  -- h₂ : (pre₁ ++ x :: mid₁) ++ y :: suf₁ = (pre₂ ++ y :: mid₂) ++ x :: suf₂
  rcases List.append_eq_append_iff.mp h₂ with ⟨a', ha₁, ha₂⟩ | ⟨c', hc₁, hc₂⟩
  · -- y :: suf₁ = a' ++ x :: suf₂
    cases a' with
    | nil =>
      simp only [List.nil_append] at ha₂
      have : y = x := by injection ha₂
      exact hne this.symm
    | cons b a'' =>
      simp only [List.cons_append] at ha₂
      have hsuf : suf₁ = a'' ++ x :: suf₂ := by injection ha₂
      exact hx_not_suf (hsuf ▸ List.mem_append_right _ (List.mem_cons_self ..))
  · -- x :: suf₂ = c' ++ y :: suf₁
    have hnd₂ : ((pre₂ ++ y :: mid₂) ++ (x :: suf₂)).Nodup := h₂ ▸ hnd
    have hdisj₂ := List.disjoint_of_nodup_append hnd₂
    have hy_in₂ : y ∈ pre₂ ++ y :: mid₂ :=
      List.mem_append_right _ (List.mem_cons_self ..)
    have hy_not_suf₂ : y ∉ suf₂ := fun h =>
      hdisj₂ hy_in₂ (List.mem_cons_of_mem _ h)
    cases c' with
    | nil =>
      simp only [List.nil_append] at hc₂
      have : x = y := by injection hc₂
      exact hne this
    | cons b c'' =>
      simp only [List.cons_append] at hc₂
      have hsuf : suf₂ = c'' ++ y :: suf₁ := by injection hc₂
      exact hy_not_suf₂ (hsuf ▸ List.mem_append_right _ (List.mem_cons_self ..))

/-! ## DFS totality -/

/-- In a Nodup list, for distinct members, one precedes the other. -/
theorem precedesIn_total {x y : α} {l : List α}
    (hnd : l.Nodup) (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    PrecedesIn x y l ∨ PrecedesIn y x l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a rest ih =>
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · exact Or.inl (precedesIn_cons_of_mem hy')
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inr (precedesIn_cons_of_mem hx')
      · rcases ih hnd' hx' hy' with h | h
        · exact Or.inl (h.cons a)
        · exact Or.inr (h.cons a)

/-! ## Main theorem -/

/-- **Theorem 3.1 (→)**: LCA order implies DFS order. -/
theorem dfsLt_of_lcaLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (_hy : y ∈ t) (hne : x ≠ y)
    (h : lcaLt x y t) : dfsLt x y t := by
  obtain ⟨_, a, hlca, hord⟩ := h
  rcases hord with rfl | ⟨hax, hay, cx, cy, hcx, hcy, hsib⟩
  · exact ancestor_precedes_in_dfs hd ⟨hlca.2.1, hne⟩
  · exact sibling_subtree_ordering hd hsib
      (isChildToward_ancestor_or_eq hcx)
      (isChildToward_ancestor_or_eq hcy)

/-- **Theorem 3.1 (←)**: DFS order implies LCA order. -/
theorem lcaLt_of_dfsLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y)
    (h : dfsLt x y t) : lcaLt x y t := by
  obtain ⟨a, hlca⟩ := lca_exists hd hx hy
  refine ⟨hne, a, hlca, ?_⟩
  by_cases hax : a = x
  · exact Or.inl hax
  · by_cases hay : a = y
    · -- a = y: y is ancestor of x → y precedes x in DFS, contradicts h
      subst hay
      exact absurd (precedesIn_antisymm (dfs_nodup hd) h
        (ancestor_precedes_in_dfs hd ⟨hlca.1, hax⟩)) False.elim
    · -- a ≠ x, a ≠ y: sibling case
      right; refine ⟨hax, hay, ?_⟩
      obtain ⟨cx, hcx⟩ := childToward_exists hd ⟨hlca.1, hax⟩
      obtain ⟨cy, hcy⟩ := childToward_exists hd ⟨hlca.2.1, hay⟩
      -- cx ≠ cy: if equal, cx is common ancestor deeper than a, contradicting LCA
      have hcne : cx ≠ cy := by
        intro heq; subst heq
        have hcx_x : IsAncestorIn cx x t := by
          rcases isChildToward_ancestor_or_eq hcx with h | rfl
          · exact h
          · exact isAncestorIn_refl hx
        have hcx_y : IsAncestorIn cx y t := by
          rcases isChildToward_ancestor_or_eq hcy with h | rfl
          · exact h
          · exact isAncestorIn_refl hy
        exact isChildToward_ne hd hcx
          (isAncestorIn_antisymm hd (isChildToward_anc_of_child hcx)
            (hlca.2.2 cx hcx_x hcx_y))
      -- By SibLt totality, either cx < cy or cy < cx
      rcases sibLt_total_of_childToward hd hcne hcx hcy with hsib | hsib
      · exact ⟨cx, cy, hcx, hcy, hsib⟩
      · -- cy < cx → y precedes x → contradicts h
        have : dfsLt y x t := sibling_subtree_ordering hd hsib
          (isChildToward_ancestor_or_eq hcy)
          (isChildToward_ancestor_or_eq hcx)
        exact absurd (precedesIn_antisymm (dfs_nodup hd) h this) False.elim

/-- **Theorem 3.1**: The DFS ordering and LCA ordering coincide. -/
theorem dfsLt_iff_lcaLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) (hne : x ≠ y) :
    dfsLt x y t ↔ lcaLt x y t :=
  ⟨lcaLt_of_dfsLt hd hx hy hne, dfsLt_of_lcaLt hd hx hy hne⟩

end OrdTree

end OTProof

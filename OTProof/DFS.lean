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

/-! ## PrecedesIn helpers -/

/-- If `y ∈ l`, then `PrecedesIn x y (x :: l)`. -/
theorem precedesIn_cons_of_mem {x y : α} {l : List α} (h : y ∈ l) :
    PrecedesIn x y (x :: l) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨[], s, t, rfl⟩

/-- Prepending a list preserves PrecedesIn. -/
theorem PrecedesIn.append_left {x y : α} {l : List α} (s : List α)
    (h : PrecedesIn x y l) : PrecedesIn x y (s ++ l) := by
  obtain ⟨pre, mid, suf, rfl⟩ := h
  exact ⟨s ++ pre, mid, suf, by simp [List.append_assoc]⟩

/-- Adding one element at front preserves PrecedesIn. -/
theorem PrecedesIn.cons {x y : α} {l : List α} (a : α)
    (h : PrecedesIn x y l) : PrecedesIn x y (a :: l) :=
  h.append_left [a]

/-- If `PrecedesIn x y l₁` and `l₁` is an infix of `l₂`, then `PrecedesIn x y l₂`. -/
theorem PrecedesIn.of_infix {x y : α} {l₁ l₂ : List α}
    (h : PrecedesIn x y l₁) (hi : l₁ <:+: l₂) : PrecedesIn x y l₂ := by
  obtain ⟨pre, mid, suf, rfl⟩ := h
  obtain ⟨s, t, rfl⟩ := hi
  refine ⟨s ++ pre, mid, suf ++ t, ?_⟩
  simp [List.append_assoc]

/-- If `x ∈ l₁` and `y ∈ l₂`, then `PrecedesIn x y (l₁ ++ l₂)`. -/
theorem precedesIn_of_mem_append {x y : α} {l₁ l₂ : List α}
    (hx : x ∈ l₁) (hy : y ∈ l₂) : PrecedesIn x y (l₁ ++ l₂) := by
  obtain ⟨s₁, t₁, rfl⟩ := List.append_of_mem hx
  obtain ⟨s₂, t₂, rfl⟩ := List.append_of_mem hy
  refine ⟨s₁, t₁ ++ s₂, t₂, ?_⟩
  simp [List.append_assoc]

/-! ## Subtree DFS -/

/-- The DFS of the subtree rooted at `v` (returns [] if v not found). -/
def subtreeDfs [DecidableEq α] (v : α) : OrdTree α → List α
  | node a cs =>
    if a = v then (node a cs).dfs
    else cs.flatMap fun c => subtreeDfs v c

/-! ## Infix helper for child DFS in flatMap -/

/-- A child's `toList` is an infix of `cs.flatMap toList`. -/
theorem toList_infix_flatMap_toList {c : OrdTree α}
    {cs : List (OrdTree α)} (hc : c ∈ cs) :
    c.toList <:+: cs.flatMap fun c => c.toList := by
  induction cs with
  | nil => exact absurd hc List.not_mem_nil
  | cons d rest ih =>
    rcases List.mem_cons.mp hc with rfl | h
    · -- c = d: c.toList is a prefix of (d :: rest).flatMap toList
      exact ⟨[], rest.flatMap fun c => c.toList, by simp⟩
    · -- c ∈ rest: by IH + rest.flatMap is a suffix of (d :: rest).flatMap
      exact (ih h).trans ⟨d.toList, [], by simp⟩

/-- The DFS of a child subtree is a sublist of the parent's DFS. -/
theorem dfs_child_sublist {c : OrdTree α} {a : α} {cs : List (OrdTree α)}
    (hc : c ∈ cs) :
    c.dfs.Sublist (node a cs).dfs := by
  simp only [dfs, toList_node]
  exact (toList_infix_flatMap_toList hc).sublist.cons a

/-! ## Ordered flatMap helper -/

/-- If `i < j`, then elements at position `i` precede elements at position `j`
    in the flatMap. -/
private theorem precedesIn_flatMap_of_get_lt
    {cs : List (OrdTree α)} {x y : α}
    {i j : Fin cs.length}
    (hij : i.val < j.val)
    (hx : x ∈ (cs.get i).toList) (hy : y ∈ (cs.get j).toList) :
    PrecedesIn x y (cs.flatMap fun c => c.toList) := by
  induction cs with
  | nil => exact absurd i.isLt (Nat.not_lt_zero _)
  | cons d rest ih =>
    match i, j with
    | ⟨0, _⟩, ⟨j' + 1, hj⟩ =>
      apply precedesIn_of_mem_append hx
      have hj' : j' < rest.length := Nat.lt_of_succ_lt_succ hj
      exact List.mem_flatMap.mpr ⟨rest.get ⟨j', hj'⟩, List.get_mem _ _, hy⟩
    | ⟨i' + 1, _⟩, ⟨j' + 1, _⟩ =>
      exact (ih (i := ⟨i', Nat.lt_of_succ_lt_succ ‹_›⟩)
        (j := ⟨j', Nat.lt_of_succ_lt_succ ‹_›⟩)
        (Nat.lt_of_succ_lt_succ hij) hx hy).append_left _
    | ⟨_ + 1, _⟩, ⟨0, _⟩ => exact absurd hij (Nat.not_lt_zero _)

/-! ## Ancestor restriction helper -/

/-- If `c` is in child `sub` and `IsAncestorIn c u (node a cs)`, then
    `IsAncestorIn c u sub` (in a distinct tree). -/
theorem isAncestorIn_restrict_to_child
    {c u a : α} {cs : List (OrdTree α)} {sub : OrdTree α}
    (hd : (node a cs).Distinct)
    (hsub : sub ∈ cs) (hc_in_sub : c ∈ sub)
    (hanc : IsAncestorIn c u (node a cs)) :
    IsAncestorIn c u sub := by
  have hc_ne_a : c ≠ a := fun h =>
    root_not_mem_child hd hsub (h ▸ hc_in_sub)
  obtain ⟨c', hc', hanc'⟩ := isAncestorIn_in_child hanc hc_ne_a
  have : c' = sub := mem_unique_child hd hc' hsub
    (isAncestorIn_mem_left hanc') hc_in_sub
  rw [this] at hanc'
  exact hanc'

/-! ## SibLt membership helpers -/

/-- A label involved in `SibLt` is a member of the tree. -/
theorem sibLt_mem_left {c₁ c₂ : α} {t : OrdTree α}
    (h : SibLt c₁ c₂ t) : c₁ ∈ t := by
  induction h with
  | here a cs hex =>
    obtain ⟨i, _, _, hlbl, _⟩ := hex
    rw [← hlbl]
    exact mem_child (List.get_mem cs i) (label_mem_self _)
  | descend _ cs sub hsub _ ih => exact mem_child hsub ih

theorem sibLt_mem_right {c₁ c₂ : α} {t : OrdTree α}
    (h : SibLt c₁ c₂ t) : c₂ ∈ t := by
  induction h with
  | here a cs hex =>
    obtain ⟨_, j, _, _, hlbl⟩ := hex
    rw [← hlbl]
    exact mem_child (List.get_mem cs j) (label_mem_self _)
  | descend _ cs sub hsub _ ih => exact mem_child hsub ih

/-! ## Helpers for Theorem 2.4 -/

/-- `flatMap` produces `[]` when every application gives `[]`. -/
private theorem flatMap_eq_nil_of_forall {β : Type*}
    {f : OrdTree α → List β} {cs : List (OrdTree α)}
    (h : ∀ c ∈ cs, f c = []) : cs.flatMap f = [] := by
  induction cs with
  | nil => rfl
  | cons d rest ih =>
    show f d ++ rest.flatMap f = []
    rw [h d (List.mem_cons_self ..), List.nil_append,
      ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- `subtreeDfs v t = []` when `v` is not a member of `t`. -/
private theorem subtreeDfs_eq_nil [DecidableEq α] {v : α} :
    ∀ (t : OrdTree α), v ∉ t → subtreeDfs v t = []
  | node a cs => fun hv => by
    simp only [subtreeDfs]
    split
    · next h => exact absurd (h ▸ label_mem_self _) hv
    · show cs.flatMap (fun c => subtreeDfs v c) = []
      exact flatMap_eq_nil_of_forall
        (fun c hc => subtreeDfs_eq_nil c (fun h => hv (mem_child hc h)))

/-- The `flatMap` of `subtreeDfs v` over children is an infix of the
    `flatMap` of `toList` over the same children. -/
private theorem flatMap_subtreeDfs_infix [DecidableEq α] {v : α}
    (cs : List (OrdTree α))
    (hnd : (cs.flatMap (fun c => c.toList)).Nodup)
    (hv : v ∈ cs.flatMap (fun c => c.toList))
    (ih_child : ∀ c ∈ cs, c.Distinct → v ∈ c →
      ∃ pre suf, c.toList = pre ++ subtreeDfs v c ++ suf) :
    ∃ pre suf, cs.flatMap (fun c => c.toList) =
      pre ++ cs.flatMap (fun c => subtreeDfs v c) ++ suf := by
  induction cs with
  | nil => simp at hv
  | cons d rest ih_cs =>
    show ∃ pre suf, d.toList ++ rest.flatMap (fun c => c.toList) =
      pre ++ (subtreeDfs v d ++ rest.flatMap (fun c => subtreeDfs v c)) ++ suf
    have hnd_fm := List.nodup_flatMap.mp hnd
    have hnd_d : d.Distinct := hnd_fm.1 d (List.mem_cons_self ..)
    have hnd_rest : (rest.flatMap (fun c => c.toList)).Nodup :=
      List.nodup_flatMap.mpr
        ⟨fun c hc => hnd_fm.1 c (List.mem_cons_of_mem _ hc),
         (List.pairwise_cons.mp hnd_fm.2).2⟩
    have hdisj := List.disjoint_of_nodup_append hnd
    rcases List.mem_append.mp hv with hv_d | hv_rest
    · -- v ∈ d: rest contributes nothing
      have hrest_nil : rest.flatMap (fun c => subtreeDfs v c) = [] :=
        flatMap_eq_nil_of_forall (fun c' hc' =>
          subtreeDfs_eq_nil c' (fun hv' =>
            hdisj hv_d (List.mem_flatMap.mpr ⟨c', hc', hv'⟩)))
      obtain ⟨p, s, hd_eq⟩ := ih_child d (List.mem_cons_self ..) hnd_d hv_d
      rw [hrest_nil, List.append_nil, hd_eq]
      exact ⟨p, s ++ rest.flatMap (fun c => c.toList), by simp [List.append_assoc]⟩
    · -- v ∈ rest: d contributes nothing
      have hd_nil : subtreeDfs v d = [] :=
        subtreeDfs_eq_nil d (fun hv_d => hdisj hv_d hv_rest)
      obtain ⟨p, s, hrest_eq⟩ := ih_cs hnd_rest hv_rest
        (fun c hc hdc hvc => ih_child c (List.mem_cons_of_mem _ hc) hdc hvc)
      rw [hd_nil, List.nil_append, hrest_eq]
      exact ⟨d.toList ++ p, s, by simp [List.append_assoc]⟩

/-! ## Theorem 2.4: Subtree Contiguity -/

/-- **Theorem 2.4 (Subtree Contiguity)**: The DFS of a subtree rooted at `v`
    appears as a contiguous block in the DFS of the full tree. -/
theorem dfs_subtree_contiguous [DecidableEq α] {v : α} :
    ∀ (t : OrdTree α), t.Distinct → v ∈ t →
    ∃ (pre suf : List α), t.dfs = pre ++ (subtreeDfs v t) ++ suf
  | node a cs => fun hd hv => by
    simp only [dfs, toList_node, subtreeDfs]
    split
    · exact ⟨[], [], by simp⟩
    · rename_i hav
      have hv' : v ∈ cs.flatMap (fun c => c.toList) := by
        simp only [mem_def, toList_node] at hv
        exact (List.mem_cons.mp hv).resolve_left (Ne.symm hav)
      have hnd : (cs.flatMap (fun c => c.toList)).Nodup := by
        simp only [Distinct, toList_node] at hd
        exact (List.nodup_cons.mp hd).2
      obtain ⟨p, s, h⟩ := flatMap_subtreeDfs_infix cs hnd hv'
        (fun c hc hdc hvc => dfs_subtree_contiguous c hdc hvc)
      exact ⟨a :: p, s, by simp [h]⟩

/-! ## Corollary 2.5: Ancestor Precedes Descendant -/

/-- **Corollary 2.5**: If `x` is a proper ancestor of `y`, then `x` appears
    before `y` in the DFS traversal. -/
theorem ancestor_precedes_in_dfs {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn x y t) :
    PrecedesIn x y t.dfs := by
  obtain ⟨hanc, hne⟩ := h
  induction hanc with
  | root cs hy =>
    simp only [dfs, toList_node]
    apply precedesIn_cons_of_mem
    rw [mem_def] at hy
    simp only [toList_node, List.mem_cons] at hy
    exact hy.resolve_left (Ne.symm hne)
  | descend r cs c hc _ ih =>
    simp only [dfs, toList_node]
    apply PrecedesIn.cons
    exact (ih (distinct_of_child hd hc)).of_infix (toList_infix_flatMap_toList hc)

/-! ## Theorem 2.6: Sibling Subtree Ordering -/

/-- **Theorem 2.6**: If `c₁` precedes `c₂` in the children list of their
    parent, then every node in `subtree(c₁)` precedes every node in
    `subtree(c₂)` in the DFS. -/
theorem sibling_subtree_ordering
    {u₁ u₂ c₁ c₂ : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hsib : SibLt c₁ c₂ t)
    (hu₁ : IsAncestorIn c₁ u₁ t ∨ c₁ = u₁)
    (hu₂ : IsAncestorIn c₂ u₂ t ∨ c₂ = u₂) :
    PrecedesIn u₁ u₂ t.dfs := by
  induction hsib with
  | here a cs hex =>
    obtain ⟨i, j, hij, hlbl₁, hlbl₂⟩ := hex
    simp only [dfs, toList_node]
    apply PrecedesIn.cons
    -- u₁ ∈ (cs.get i)
    have hu₁_mem : u₁ ∈ (cs.get i) := by
      rcases hu₁ with hanc | rfl
      · exact isAncestorIn_mem_right
          (isAncestorIn_restrict_to_child hd (List.get_mem _ _)
            (hlbl₁ ▸ label_mem_self _) hanc)
      · exact hlbl₁ ▸ label_mem_self _
    -- u₂ ∈ (cs.get j)
    have hu₂_mem : u₂ ∈ (cs.get j) := by
      rcases hu₂ with hanc | rfl
      · exact isAncestorIn_mem_right
          (isAncestorIn_restrict_to_child hd (List.get_mem _ _)
            (hlbl₂ ▸ label_mem_self _) hanc)
      · exact hlbl₂ ▸ label_mem_self _
    exact precedesIn_flatMap_of_get_lt hij hu₁_mem hu₂_mem
  | descend a cs sub hsub hsib_sub ih =>
    simp only [dfs, toList_node]
    apply PrecedesIn.cons
    have hc₁_in_sub : c₁ ∈ sub := sibLt_mem_left hsib_sub
    have hc₂_in_sub : c₂ ∈ sub := sibLt_mem_right hsib_sub
    -- Restrict hu₁, hu₂ to sub
    have hu₁_sub : IsAncestorIn c₁ u₁ sub ∨ c₁ = u₁ := by
      rcases hu₁ with hanc | rfl
      · exact Or.inl (isAncestorIn_restrict_to_child hd hsub hc₁_in_sub hanc)
      · exact Or.inr rfl
    have hu₂_sub : IsAncestorIn c₂ u₂ sub ∨ c₂ = u₂ := by
      rcases hu₂ with hanc | rfl
      · exact Or.inl (isAncestorIn_restrict_to_child hd hsub hc₂_in_sub hanc)
      · exact Or.inr rfl
    exact (ih (distinct_of_child hd hsub) hu₁_sub hu₂_sub).of_infix
      (toList_infix_flatMap_toList hsub)

end OrdTree

end OTProof

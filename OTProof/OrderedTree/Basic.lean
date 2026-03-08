/-
# Layer 0: Ordered Tree Definitions

Finite ordered trees with labeled nodes, the ancestor relation,
LCA, and child_toward — following §1 and §5.3 of
dfs-preorder-lca-characterization-v0.1.md.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Order.RelClasses

namespace OTProof

/-! ## Tree type -/

/-- A finite ordered tree: each node carries a label of type `α` and
    has an ordered list of children (sibling order = list position). -/
inductive OrdTree (α : Type*) where
  | node : α → List (OrdTree α) → OrdTree α
  deriving Inhabited

namespace OrdTree

variable {α : Type*}

/-! ## Basic operations -/

/-- The label at the root of the tree. -/
def label : OrdTree α → α
  | node a _ => a

/-- The ordered list of immediate children. -/
def children : OrdTree α → List (OrdTree α)
  | node _ cs => cs

@[simp] theorem label_node (a : α) (cs : List (OrdTree α)) :
    (node a cs).label = a := rfl

@[simp] theorem children_node (a : α) (cs : List (OrdTree α)) :
    (node a cs).children = cs := rfl

/-! ## DFS / toList -/

/-- All labels in the tree, listed in DFS preorder.
    This also serves as the canonical flattening for membership. -/
def toList : OrdTree α → List α
  | .node a cs => a :: (cs.flatMap fun c => toList c)

@[simp] theorem toList_node (a : α) (cs : List (OrdTree α)) :
    (node a cs).toList = a :: (cs.flatMap fun c => c.toList) := by
  conv_lhs => unfold toList

/-! ## Membership -/

/-- Tree membership: `x` occurs as a label somewhere in tree `t`. -/
def TreeMem (x : α) (t : OrdTree α) : Prop := x ∈ t.toList

instance : Membership α (OrdTree α) where
  mem t x := TreeMem x t

theorem mem_def {x : α} {t : OrdTree α} :
    x ∈ t ↔ x ∈ t.toList := by
  constructor
  · intro h; exact h
  · intro h; exact h

@[simp] theorem mem_node_iff {x a : α} {cs : List (OrdTree α)} :
    x ∈ (node a cs : OrdTree α) ↔ x = a ∨ ∃ c ∈ cs, x ∈ c := by
  simp only [mem_def, toList_node, List.mem_cons, List.mem_flatMap]

theorem mem_root (a : α) (cs : List (OrdTree α)) :
    a ∈ (node a cs : OrdTree α) := by
  rw [mem_node_iff]; left; rfl

theorem mem_child {x : α} {c : OrdTree α} {a : α} {cs : List (OrdTree α)}
    (hc : c ∈ cs) (hx : x ∈ c) : x ∈ (node a cs : OrdTree α) := by
  rw [mem_node_iff]
  right
  exact ⟨c, hc, hx⟩

/-! ## Distinct (all labels unique) -/

/-- All labels in the tree are distinct (the toList has no duplicates). -/
def Distinct (t : OrdTree α) : Prop :=
  t.toList.Nodup

/-! ## Ancestor relation -/

/-- `IsAncestorIn x y t` means `x` is an ancestor of `y` in tree `t`
    (i.e., `x` is on the path from `y` to the root). -/
inductive IsAncestorIn (x y : α) : OrdTree α → Prop where
  | root : (cs : List (OrdTree α)) → y ∈ (node x cs : OrdTree α) →
      IsAncestorIn x y (node x cs)
  | descend : (a : α) → (cs : List (OrdTree α)) → (c : OrdTree α) →
      c ∈ cs → IsAncestorIn x y c → IsAncestorIn x y (node a cs)

/-- `IsProperAncestorIn x y t`: x is a proper ancestor of y in t. -/
def IsProperAncestorIn (x y : α) (t : OrdTree α) : Prop :=
  IsAncestorIn x y t ∧ x ≠ y

/-! ### Helper lemmas -/

/-- If x is an ancestor of y in t, then y ∈ t. -/
theorem isAncestorIn_mem_right {x y : α} {t : OrdTree α}
    (h : IsAncestorIn x y t) : y ∈ t := by
  induction h with
  | root cs hy => exact hy
  | descend a cs c hc _ ih => exact mem_child hc ih

/-- If x is an ancestor of y in t, then x ∈ t. -/
theorem isAncestorIn_mem_left {x y : α} {t : OrdTree α}
    (h : IsAncestorIn x y t) : x ∈ t := by
  induction h with
  | root cs _ => exact mem_root x cs
  | descend a cs c hc _ ih => exact mem_child hc ih

/-- Distinct is inherited by children. -/
theorem distinct_of_child {a : α} {cs : List (OrdTree α)} {c : OrdTree α}
    (hd : (node a cs).Distinct) (hc : c ∈ cs) : c.Distinct := by
  unfold Distinct at hd ⊢
  rw [toList_node] at hd
  exact (List.nodup_flatMap.mp (List.nodup_cons.mp hd).2).1 c hc

/-- The root label is not in any child's toList. -/
theorem root_not_mem_child {a : α} {cs : List (OrdTree α)} {c : OrdTree α}
    (hd : (node a cs).Distinct) (hc : c ∈ cs) : a ∉ c := by
  unfold Distinct at hd
  rw [toList_node] at hd
  intro ha
  exact (List.nodup_cons.mp hd).1 (List.mem_flatMap.mpr ⟨c, hc, ha⟩)

/-- In a distinct tree, an element can be in at most one child. -/
theorem mem_unique_child {y a : α} {cs : List (OrdTree α)}
    {c₁ c₂ : OrdTree α}
    (hd : (node a cs).Distinct)
    (hc₁ : c₁ ∈ cs) (hc₂ : c₂ ∈ cs)
    (hy₁ : y ∈ c₁) (hy₂ : y ∈ c₂) : c₁ = c₂ := by
  by_contra hne
  unfold Distinct at hd
  rw [toList_node] at hd
  have hfm_nd := (List.nodup_cons.mp hd).2
  have ⟨_, hpw⟩ := List.nodup_flatMap.mp hfm_nd
  exact (hpw.forall (fun ⦃_ _⦄ => List.disjoint_symm) hc₁ hc₂ hne) hy₁ hy₂

/-- If a' is ancestor of x in (node r cs) and a' ≠ r, then a' is ancestor
    of x in some child c ∈ cs. -/
theorem isAncestorIn_in_child {a' x r : α} {cs : List (OrdTree α)}
    (h : IsAncestorIn a' x (node r cs)) (hne : a' ≠ r) :
    ∃ c ∈ cs, IsAncestorIn a' x c := by
  cases h with
  | root _ _ => exact absurd rfl hne
  | descend _ _ c hc h' => exact ⟨c, hc, h'⟩

/-! ### Ancestor properties (A1, A2, A3) -/

/-- A1 (reflexivity part): x is an ancestor of itself if x ∈ t. -/
theorem isAncestorIn_refl {x : α} {t : OrdTree α} (hx : x ∈ t) :
    IsAncestorIn x x t := by
  match t, hx with
  | node a cs, hx =>
    simp only [mem_node_iff] at hx
    rcases hx with rfl | ⟨c, hc, hxc⟩
    · exact IsAncestorIn.root cs (mem_root x cs)
    · exact IsAncestorIn.descend a cs c hc (isAncestorIn_refl hxc)
termination_by t

/-- A2: The root is an ancestor of every node. -/
theorem root_isAncestorIn {t : OrdTree α} {y : α} (hy : y ∈ t) :
    IsAncestorIn t.label y t := by
  cases t with
  | node a cs => exact IsAncestorIn.root cs hy

/-- A1 (transitivity): Ancestor relation is transitive. -/
theorem isAncestorIn_trans {x y z : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hxy : IsAncestorIn x y t) (hyz : IsAncestorIn y z t) :
    IsAncestorIn x z t := by
  induction hxy with
  | root cs _ =>
    exact .root cs (isAncestorIn_mem_right hyz)
  | descend r cs c hc hxy' ih =>
    cases hyz with
    | root _ _ =>
      exact absurd (isAncestorIn_mem_right hxy') (root_not_mem_child hd hc)
    | descend _ _ c' hc' hyz' =>
      have heq := mem_unique_child hd hc hc'
        (isAncestorIn_mem_right hxy') (isAncestorIn_mem_left hyz')
      subst heq
      exact .descend r cs c hc (ih (distinct_of_child hd hc) hyz')

/-- A3: The ancestors of any node form a chain (total order). -/
theorem ancestors_chain {x a b : α} {t : OrdTree α}
    (hd : t.Distinct)
    (ha : IsAncestorIn a x t) (hb : IsAncestorIn b x t) :
    IsAncestorIn a b t ∨ IsAncestorIn b a t := by
  induction ha with
  | root cs _ =>
    left; exact .root cs (isAncestorIn_mem_left hb)
  | descend r cs ca hca ha' ih =>
    cases hb with
    | root _ _ =>
      right; exact .root cs (mem_child hca (isAncestorIn_mem_left ha'))
    | descend _ _ cb hcb hb' =>
      have heq := mem_unique_child hd hca hcb
        (isAncestorIn_mem_right ha') (isAncestorIn_mem_right hb')
      subst heq
      rcases ih (distinct_of_child hd hca) hb' with h | h
      · left; exact .descend r cs ca hca h
      · right; exact .descend r cs ca hca h

/-- Antisymmetry: mutual ancestors must be equal (in a distinct tree). -/
theorem isAncestorIn_antisymm {a b : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hab : IsAncestorIn a b t) (hba : IsAncestorIn b a t) :
    a = b := by
  induction hab with
  | root cs _ =>
    cases hba with
    | root _ _ => rfl
    | descend _ _ c hc hba' =>
      exact absurd (isAncestorIn_mem_right hba') (root_not_mem_child hd hc)
  | descend r cs c hc hab' ih =>
    cases hba with
    | root _ _ =>
      exact absurd (isAncestorIn_mem_right hab') (root_not_mem_child hd hc)
    | descend _ _ c' hc' hba' =>
      have heq := mem_unique_child hd hc hc'
        (isAncestorIn_mem_left hab') (isAncestorIn_mem_right hba')
      subst heq
      exact ih (distinct_of_child hd hc) hba'

/-! ## LCA (Lowest Common Ancestor) -/

/-- `IsLCA a x y t` means `a` is the LCA of `x` and `y` in tree `t`. -/
def IsLCA (a x y : α) (t : OrdTree α) : Prop :=
  IsAncestorIn a x t ∧ IsAncestorIn a y t ∧
  ∀ a', IsAncestorIn a' x t → IsAncestorIn a' y t → IsAncestorIn a' a t

/-- LCA exists for any two nodes in a tree with distinct labels. -/
theorem lca_exists {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) :
    ∃ a, IsLCA a x y t := by
  match t, hd, hx, hy with
  | node r cs, hd, hx, hy =>
    rw [mem_node_iff] at hx
    rcases hx with rfl | ⟨cx, hcx, hx'⟩
    · -- x = r: rfl eliminates r, x stays; hy unchanged
      exact ⟨x, isAncestorIn_refl (mem_root x cs), .root cs hy,
        fun _ ha' _ => ha'⟩
    · rw [mem_node_iff] at hy
      rcases hy with rfl | ⟨cy, hcy, hy'⟩
      · -- y = r: rfl eliminates r, y stays
        exact ⟨y, .root cs (mem_child hcx hx'), isAncestorIn_refl (mem_root y cs),
          fun _ _ ha' => ha'⟩
      · -- Both x, y in children; r still in scope
        by_cases heq : cx = cy
        · -- Same child: convert hy' using heq, keep cx
          have hy'_cx : y ∈ cx := heq ▸ hy'
          have ⟨a, hlca⟩ := lca_exists (distinct_of_child hd hcx) hx' hy'_cx
          refine ⟨a,
            .descend r cs cx hcx hlca.1,
            .descend r cs cx hcx hlca.2.1,
            fun a' ha'x ha'y => ?_⟩
          by_cases ha'r : a' = r
          · rw [ha'r]
            exact .root cs (mem_child hcx (isAncestorIn_mem_left hlca.1))
          · obtain ⟨c₁, hc₁, ha'x'⟩ := isAncestorIn_in_child ha'x ha'r
            obtain ⟨c₂, hc₂, ha'y'⟩ := isAncestorIn_in_child ha'y ha'r
            rw [mem_unique_child hd hc₁ hcx
              (isAncestorIn_mem_right ha'x') hx'] at ha'x'
            rw [mem_unique_child hd hc₂ hcx
              (isAncestorIn_mem_right ha'y') hy'_cx] at ha'y'
            exact .descend r cs cx hcx (hlca.2.2 a' ha'x' ha'y')
        · -- Different children: LCA is root
          refine ⟨r, .root cs (mem_child hcx hx'), .root cs (mem_child hcy hy'),
            fun a' ha'x ha'y => ?_⟩
          by_cases ha'r : a' = r
          · rw [ha'r]; exact isAncestorIn_refl (mem_root r cs)
          · obtain ⟨c₁, hc₁, ha'x'⟩ := isAncestorIn_in_child ha'x ha'r
            obtain ⟨c₂, hc₂, ha'y'⟩ := isAncestorIn_in_child ha'y ha'r
            rw [mem_unique_child hd hc₁ hcx
              (isAncestorIn_mem_right ha'x') hx'] at ha'x'
            rw [mem_unique_child hd hc₂ hcy
              (isAncestorIn_mem_right ha'y') hy'] at ha'y'
            exact absurd (mem_unique_child hd hcx hcy
              (isAncestorIn_mem_left ha'x') (isAncestorIn_mem_left ha'y')) heq
termination_by t

/-- LCA is unique in a tree with distinct labels. -/
theorem lca_unique {a₁ a₂ x y : α} {t : OrdTree α}
    (hd : t.Distinct)
    (h₁ : IsLCA a₁ x y t) (h₂ : IsLCA a₂ x y t) :
    a₁ = a₂ :=
  isAncestorIn_antisymm hd
    (h₂.2.2 a₁ h₁.1 h₁.2.1)
    (h₁.2.2 a₂ h₂.1 h₂.2.1)

/-! ## child_toward -/

/-- `IsChildToward c a x t` means `c` is the label of the child of the `a`-rooted
    subtree that contains `x`. -/
inductive IsChildToward (c a x : α) : OrdTree α → Prop where
  | here : (cs : List (OrdTree α)) →
      (∃ child ∈ cs, child.label = c ∧ x ∈ child) →
      IsChildToward c a x (node a cs)
  | descend : (b : α) → (cs : List (OrdTree α)) → (sub : OrdTree α) →
      sub ∈ cs → IsChildToward c a x sub → IsChildToward c a x (node b cs)

/-- IsChildToward implies the ancestor label is in the tree. -/
theorem isChildToward_mem_ancestor {c a x : α} {t : OrdTree α}
    (h : IsChildToward c a x t) : a ∈ t := by
  induction h with
  | here cs _ => exact mem_root a cs
  | descend b cs sub hsub _ ih => exact mem_child hsub ih

/-- IsChildToward implies the target is in the tree. -/
theorem isChildToward_mem_target {c a x : α} {t : OrdTree α}
    (h : IsChildToward c a x t) : x ∈ t := by
  induction h with
  | here cs hex =>
    obtain ⟨child, hchild, _, hx_in⟩ := hex
    exact mem_child hchild hx_in
  | descend b cs sub hsub _ ih => exact mem_child hsub ih

/-- child_toward existence: if a is a proper ancestor of x, there is a unique
    child of a toward x. -/
theorem childToward_exists {a x : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn a x t) :
    ∃ c, IsChildToward c a x t := by
  obtain ⟨hanc, hne⟩ := h
  induction hanc with
  | root cs hx =>
    rw [mem_node_iff] at hx
    rcases hx with rfl | ⟨child, hchild, hx_in⟩
    · exact absurd rfl hne
    · exact ⟨child.label, .here cs ⟨child, hchild, rfl, hx_in⟩⟩
  | descend r cs c hc _ ih =>
    have ⟨c', hct⟩ := ih (distinct_of_child hd hc)
    exact ⟨c', .descend r cs c hc hct⟩

/-- child_toward uniqueness. -/
theorem childToward_unique {c₁ c₂ a x : α} {t : OrdTree α}
    (hd : t.Distinct)
    (h₁ : IsChildToward c₁ a x t) (h₂ : IsChildToward c₂ a x t) :
    c₁ = c₂ := by
  induction h₁ with
  | here cs hex₁ =>
    cases h₂ with
    | here _ hex₂ =>
      obtain ⟨child₁, hc₁, hlbl₁, hx₁⟩ := hex₁
      obtain ⟨child₂, hc₂, hlbl₂, hx₂⟩ := hex₂
      have := mem_unique_child hd hc₁ hc₂ hx₁ hx₂
      rw [← hlbl₁, ← hlbl₂, this]
    | descend _ _ sub hsub h₂' =>
      exact absurd (isChildToward_mem_ancestor h₂') (root_not_mem_child hd hsub)
  | descend b cs sub hsub _ ih =>
    cases h₂ with
    | here _ _ =>
      exact absurd (isChildToward_mem_ancestor ‹IsChildToward c₁ a x sub›)
        (root_not_mem_child hd hsub)
    | descend _ _ sub₂ hsub₂ h₂' =>
      have heq := mem_unique_child hd hsub hsub₂
        (isChildToward_mem_target ‹IsChildToward c₁ a x sub›)
        (isChildToward_mem_target h₂')
      exact ih (distinct_of_child hd hsub) (heq ▸ h₂')

/-- CT-compose: if a <_A b ≤_A x, then child_toward(a, x) = child_toward(a, b). -/
theorem childToward_compose {a b x c : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hab : IsProperAncestorIn a b t)
    (hbx : IsAncestorIn b x t)
    (hc : IsChildToward c a x t) :
    IsChildToward c a b t := by
  induction hc with
  | here cs hex =>
    -- t = node a cs, child toward x is here
    obtain ⟨child, hchild, hlabel, hx_in⟩ := hex
    -- b is in the tree, b ≠ a, so b is in some child
    have hne := hab.2
    have hbx_anc := hbx
    -- b is ancestor of x, b ≠ a (root), so b descends into a child
    have hb_mem : b ∈ (node a cs : OrdTree α) := isAncestorIn_mem_left hbx
    rw [mem_node_iff] at hb_mem
    rcases hb_mem with rfl | ⟨child_b, hcb, hb_in⟩
    · exact absurd rfl hne.symm
    · -- b ∈ child_b, x ∈ child. Need: child_b = child
      -- x is in child. b is ancestor of x, so x is reachable from b.
      -- Since b ≠ a, IsAncestorIn b x (node a cs) must descend into some child.
      have hb_ne_a : b ≠ a := hne.symm
      obtain ⟨cb, hcb', hbx_in_cb⟩ := isAncestorIn_in_child hbx hb_ne_a
      have hx_in_cb : x ∈ cb := isAncestorIn_mem_right hbx_in_cb
      have : cb = child := mem_unique_child hd hcb' hchild hx_in_cb hx_in
      rw [this] at hbx_in_cb
      have hb_in_child : b ∈ child := isAncestorIn_mem_left hbx_in_cb
      exact .here cs ⟨child, hchild, hlabel, hb_in_child⟩
  | descend r cs sub hsub _ ih =>
    -- t = node r cs, IsChildToward c a x sub
    -- a ∈ sub (from the inner IsChildToward)
    -- a ≠ r (since a ∈ sub and root ∉ sub by distinct)
    have ha_in_sub : a ∈ sub := isChildToward_mem_ancestor
      ‹IsChildToward c a x sub›
    have ha_ne_r : a ≠ r := fun h => root_not_mem_child hd hsub (h ▸ ha_in_sub)
    -- hab : IsProperAncestorIn a b (node r cs)
    -- Since a ≠ r, IsAncestorIn a b must descend into a child
    obtain ⟨ca, hca, hab_in_ca⟩ := isAncestorIn_in_child hab.1 ha_ne_r
    -- a ∈ ca and a ∈ sub, so ca = sub
    have : ca = sub := mem_unique_child hd hca hsub
      (isAncestorIn_mem_left hab_in_ca) ha_in_sub
    rw [this] at hab_in_ca
    -- hbx : IsAncestorIn b x (node r cs), b ∈ sub
    have hb_in_sub : b ∈ sub := isAncestorIn_mem_right hab_in_ca
    have hx_in_sub : x ∈ sub := isChildToward_mem_target ‹IsChildToward c a x sub›
    -- b ≠ r (since b ∈ sub and root ∉ sub)
    have hb_ne_r : b ≠ r := fun h => root_not_mem_child hd hsub (h ▸ hb_in_sub)
    obtain ⟨cb, hcb, hbx_in_cb⟩ := isAncestorIn_in_child hbx hb_ne_r
    -- x ∈ cb, x ∈ sub, so cb = sub
    have : cb = sub := mem_unique_child hd hcb hsub
      (isAncestorIn_mem_right hbx_in_cb) hx_in_sub
    rw [this] at hbx_in_cb
    exact .descend r cs sub hsub
      (ih (distinct_of_child hd hsub) ⟨hab_in_ca, hab.2⟩ hbx_in_cb)

/-- If `IsChildToward c a x t`, then `c` is an ancestor of `x` in `t` (or `c = x`). -/
theorem isChildToward_ancestor_or_eq {c a x : α} {t : OrdTree α}
    (h : IsChildToward c a x t) : IsAncestorIn c x t ∨ c = x := by
  induction h with
  | here cs hex =>
    obtain ⟨child, hchild, hlabel, hx_in⟩ := hex
    by_cases hcx : c = x
    · exact Or.inr hcx
    · left
      exact .descend a cs child hchild
        (hlabel ▸ root_isAncestorIn hx_in)
  | descend b cs sub hsub _ ih =>
    rcases ih with hanc | rfl
    · exact Or.inl (.descend b cs sub hsub hanc)
    · exact Or.inr rfl

/-- The label of a tree is a member of that tree. -/
theorem label_mem_self (t : OrdTree α) : t.label ∈ t := by
  cases t with | node a cs => exact mem_root a cs

/-- IsChildToward implies the ancestor is an ancestor of the child label. -/
theorem isChildToward_anc_of_child {c a x : α} {t : OrdTree α}
    (h : IsChildToward c a x t) : IsAncestorIn a c t := by
  induction h with
  | here cs hex =>
    obtain ⟨child, hchild, hlabel, _⟩ := hex
    exact .root cs (mem_child hchild (hlabel ▸ label_mem_self child))
  | descend b cs sub hsub _ ih =>
    exact .descend b cs sub hsub ih

/-- In a distinct tree, child_toward label differs from the ancestor label. -/
theorem isChildToward_ne {c a x : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsChildToward c a x t) : a ≠ c := by
  induction h with
  | here cs hex =>
    obtain ⟨child, hchild, hlabel, _⟩ := hex
    intro heq
    exact root_not_mem_child hd hchild (heq ▸ hlabel ▸ label_mem_self child)
  | descend _ cs sub hsub _ ih =>
    exact ih (distinct_of_child hd hsub)

/-- In a distinct tree, `IsChildToward c a x (node a cs)` must use the `here`
    constructor (the ancestor is at the root). -/
theorem isChildToward_here_of_root {c a x : α} {cs : List (OrdTree α)}
    (hd : (node a cs).Distinct)
    (h : IsChildToward c a x (node a cs)) :
    ∃ child ∈ cs, child.label = c ∧ x ∈ child := by
  cases h with
  | here _ hex => exact hex
  | descend _ _ sub hsub h' =>
    exact absurd (isChildToward_mem_ancestor h') (root_not_mem_child hd hsub)

/-! ## Sibling ordering -/

/-- `SibLt c₁ c₂ t` means `c₁` and `c₂` are siblings (children of the same
    node) in tree `t`, and `c₁` precedes `c₂` in the children list.
    Here `c₁`, `c₂` are labels. -/
inductive SibLt (c₁ c₂ : α) : OrdTree α → Prop where
  | here : (a : α) → (cs : List (OrdTree α)) →
      (∃ (i j : Fin cs.length),
        i.val < j.val ∧
        (cs.get i).label = c₁ ∧
        (cs.get j).label = c₂) →
      SibLt c₁ c₂ (node a cs)
  | descend : (a : α) → (cs : List (OrdTree α)) → (sub : OrdTree α) →
      sub ∈ cs → SibLt c₁ c₂ sub → SibLt c₁ c₂ (node a cs)

/-- SibLt totality for distinct child_toward labels. -/
theorem sibLt_total_of_childToward {cx cy a x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hne : cx ≠ cy)
    (hcx : IsChildToward cx a x t) (hcy : IsChildToward cy a y t) :
    SibLt cx cy t ∨ SibLt cy cx t := by
  induction hcx with
  | here cs hex =>
    have hey := isChildToward_here_of_root hd hcy
    obtain ⟨child_x, hcx_mem, hcx_lbl, _⟩ := hex
    obtain ⟨child_y, hcy_mem, hcy_lbl, _⟩ := hey
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hcx_mem
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hcy_mem
    have hij : i ≠ j := by
      intro heq; rw [heq] at hi
      exact hne ((congrArg label hi).symm.trans (congrArg label hj) |>.symm.trans
        hcx_lbl |>.symm |>.trans hcy_lbl |>.symm).symm
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · left; exact .here a cs ⟨i, j, h,
        (congrArg label hi).trans hcx_lbl,
        (congrArg label hj).trans hcy_lbl⟩
    · right; exact .here a cs ⟨j, i, h,
        (congrArg label hj).trans hcy_lbl,
        (congrArg label hi).trans hcx_lbl⟩
  | descend b cs' sub' hsub' hcx_sub ih =>
    cases hcy with
    | here _ _ =>
      exact absurd (isChildToward_mem_ancestor hcx_sub) (root_not_mem_child hd hsub')
    | descend _ _ sub₂ hsub₂ hcy' =>
      have ha_sub := isChildToward_mem_ancestor hcx_sub
      have ha_sub₂ := isChildToward_mem_ancestor hcy'
      have heq : sub₂ = sub' := mem_unique_child hd hsub₂ hsub' ha_sub₂ ha_sub
      rcases ih (distinct_of_child hd hsub') (heq ▸ hcy') with h | h
      · left; exact .descend b cs' sub' hsub' h
      · right; exact .descend b cs' sub' hsub' h

end OrdTree

end OTProof

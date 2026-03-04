/-
# Layer 0: Ordered Tree Definitions

Finite ordered trees with labeled nodes, the ancestor relation,
LCA, and child_toward — following §1 and §5.3 of
dfs-preorder-lca-characterization-v0.1.md.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
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
  sorry

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

/-! ### Ancestor properties (A1, A2, A3) -/

/-- A1 (reflexivity part): x is an ancestor of itself if x ∈ t. -/
theorem isAncestorIn_refl {x : α} {t : OrdTree α} (hx : x ∈ t) :
    IsAncestorIn x x t := by
  sorry

/-- A2: The root is an ancestor of every node. -/
theorem root_isAncestorIn {t : OrdTree α} {y : α} (hy : y ∈ t) :
    IsAncestorIn t.label y t := by
  sorry

/-- A1 (transitivity): Ancestor relation is transitive. -/
theorem isAncestorIn_trans {x y z : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hxy : IsAncestorIn x y t) (hyz : IsAncestorIn y z t) :
    IsAncestorIn x z t := by
  sorry

/-- A3: The ancestors of any node form a chain (total order). -/
theorem ancestors_chain {x a b : α} {t : OrdTree α}
    (hd : t.Distinct)
    (ha : IsAncestorIn a x t) (hb : IsAncestorIn b x t) :
    IsAncestorIn a b t ∨ IsAncestorIn b a t := by
  sorry

/-! ## LCA (Lowest Common Ancestor) -/

/-- `IsLCA a x y t` means `a` is the LCA of `x` and `y` in tree `t`. -/
def IsLCA (a x y : α) (t : OrdTree α) : Prop :=
  IsAncestorIn a x t ∧ IsAncestorIn a y t ∧
  ∀ a', IsAncestorIn a' x t → IsAncestorIn a' y t → IsAncestorIn a' a t

/-- LCA exists for any two nodes in a tree with distinct labels. -/
theorem lca_exists {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ t) (hy : y ∈ t) :
    ∃ a, IsLCA a x y t := by
  sorry

/-- LCA is unique in a tree with distinct labels. -/
theorem lca_unique {a₁ a₂ x y : α} {t : OrdTree α}
    (hd : t.Distinct)
    (h₁ : IsLCA a₁ x y t) (h₂ : IsLCA a₂ x y t) :
    a₁ = a₂ := by
  sorry

/-! ## child_toward -/

/-- `IsChildToward c a x t` means `c` is the label of the child of the `a`-rooted
    subtree that contains `x`. -/
inductive IsChildToward (c a x : α) : OrdTree α → Prop where
  | here : (cs : List (OrdTree α)) →
      (∃ child ∈ cs, child.label = c ∧ x ∈ child) →
      IsChildToward c a x (node a cs)
  | descend : (b : α) → (cs : List (OrdTree α)) → (sub : OrdTree α) →
      sub ∈ cs → IsChildToward c a x sub → IsChildToward c a x (node b cs)

/-- child_toward existence: if a is a proper ancestor of x, there is a unique
    child of a toward x. -/
theorem childToward_exists {a x : α} {t : OrdTree α}
    (hd : t.Distinct) (h : IsProperAncestorIn a x t) :
    ∃ c, IsChildToward c a x t := by
  sorry

/-- child_toward uniqueness. -/
theorem childToward_unique {c₁ c₂ a x : α} {t : OrdTree α}
    (hd : t.Distinct)
    (h₁ : IsChildToward c₁ a x t) (h₂ : IsChildToward c₂ a x t) :
    c₁ = c₂ := by
  sorry

/-- CT-compose: if a <_A b ≤_A x, then child_toward(a, x) = child_toward(a, b). -/
theorem childToward_compose {a b x c : α} {t : OrdTree α}
    (hd : t.Distinct)
    (hab : IsProperAncestorIn a b t)
    (hbx : IsAncestorIn b x t)
    (hc : IsChildToward c a x t) :
    IsChildToward c a b t := by
  sorry

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

end OrdTree

end OTProof

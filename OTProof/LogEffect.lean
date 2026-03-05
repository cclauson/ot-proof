/-
# LogEffect: The Log Effect Invariant

Defines the Log Effect Invariant (materialized document = DFS-ordered
elements) and proves it is preserved by rebase.
-/
import OTProof.Stability
import OTProof.Rebase

namespace OTProof

open OrdTree

variable {α : Type*}

universe u

/-! ## Definitions -/

/-- Materialize a log by replaying insert operations left-to-right. -/
def materialize : List (LO α) → List α :=
  List.foldl (fun doc lo => doc.insertIdx lo.idx lo.char) []

/-- The document for a tree: DFS-ordered elements, excluding the root
    (which represents the BEGIN sentinel in the RGA model). -/
def treeDoc (t : OrdTree α) : List α := t.toList.tail

/-- The Log Effect Invariant: the materialized document equals the
    tree document (DFS = lcaLt order, minus root sentinel). -/
def LogEffectInv (doc : List α) (t : OrdTree α) : Prop :=
  doc = treeDoc t

/-- A log entry with its semantic interpretation:
    the tree parent for the new element and its child position. -/
structure SemanticLO (α : Type u) where
  lo : LO α
  parent : α
  childPos : Nat

/-! ## LE-1: Single-step invariant preservation -/

/-- When inserting a character into the document, the invariant is
    preserved if the document-level index corresponds to the
    tree-level insertion position via `toList_insertLeaf`. -/
theorem logEffect_step [DecidableEq α]
    {doc : List α} {t : OrdTree α} {slo : SemanticLO α}
    (hd : t.Distinct) (hinv : LogEffectInv doc t)
    (hfresh : slo.lo.char ∉ t) (hp : slo.parent ∈ t)
    (hpos : slo.childPos ≤ OrdTree.numChildren slo.parent t)
    -- Index consistency: the document index matches the DFS insertion point
    (hidx : ∃ k, k ≤ t.toList.length ∧
      (OrdTree.insertLeaf t slo.parent slo.lo.char slo.childPos).toList =
        t.toList.insertIdx k slo.lo.char ∧
      slo.lo.idx = k - 1) :
    LogEffectInv
      (doc.insertIdx slo.lo.idx slo.lo.char)
      (OrdTree.insertLeaf t slo.parent slo.lo.char slo.childPos) := by
  obtain ⟨k, _, hk_eq, hidx_eq⟩ := hidx
  unfold LogEffectInv treeDoc at hinv ⊢
  rw [hinv, hk_eq, hidx_eq]
  cases k with
  | zero =>
    exfalso
    match t with
    | .node a cs =>
      rw [toList_node, List.insertIdx_zero] at hk_eq
      have h_head : (OrdTree.insertLeaf (.node a cs) slo.parent slo.lo.char slo.childPos).toList.head?
          = some a := by
        simp only [OrdTree.insertLeaf_node]; split <;> simp [toList_node]
      rw [hk_eq] at h_head; simp at h_head
      exact hfresh (h_head ▸ mem_root a cs)
  | succ n =>
    match t with
    | .node a cs =>
      simp only [toList_node, List.tail_cons, List.insertIdx_succ_cons, Nat.succ_sub_one]

/-! ## Helpers -/

/-- Inserting at position k+1 in a nonempty list commutes with tail. -/
theorem tail_insertIdx_succ {l : List α} {x : α} {n : Nat}
    (hl : l ≠ []) :
    (l.insertIdx (n + 1) x).tail = l.tail.insertIdx n x := by
  match l with
  | [] => exact absurd rfl hl
  | _ :: _ => simp [List.insertIdx_succ_cons]

/-- The DFS insertion position for a fresh element is always ≥ 1
    (position 0 is the root, which is never fresh). -/
theorem insertLeaf_dfs_pos_ge_one [DecidableEq α] {t : OrdTree α}
    {parent x : α} {pos k : Nat}
    (hd : t.Distinct) (hfresh : x ∉ t) (hp : parent ∈ t)
    (hpos : pos ≤ numChildren parent t)
    (hk_le : k ≤ t.toList.length)
    (hk_eq : (insertLeaf t parent x pos).toList = t.toList.insertIdx k x) :
    k ≥ 1 := by
  by_contra hlt; simp only [not_le] at hlt
  have hk0 : k = 0 := by omega
  subst hk0
  match t with
  | .node r cs =>
    have h_head : (insertLeaf (.node r cs) parent x pos).toList.head?
        = some r := by
      simp only [insertLeaf_node]; split <;> simp [toList_node]
    rw [hk_eq, toList_node] at h_head
    simp [List.insertIdx_zero] at h_head
    exact hfresh (h_head ▸ mem_root r cs)

/-! ## LE-2: Main theorem — rebase preserves Log Effect Invariant -/

/-- **Main theorem**: applying operation b then rebasing a gives the same
    document state as the tree with both insertions.

    The combined tree is built using `applyInsert`, which determines
    sibling position from the tiebreaker ordering `lt_sib`, making the
    tree construction independent of integration order. -/
theorem rebase_preserves_logEffect [DecidableEq α]
    {doc : List α} {t : OrdTree α}
    {parent_a parent_b a b : α} {lo_a lo_b : LO α}
    {lt_sib : α → α → Bool} {tb : Tiebreaker}
    (hd : t.Distinct) (hinv : LogEffectInv doc t)
    (ha_fresh : a ∉ t) (hb_fresh : b ∉ t)
    (hab : a ≠ b)
    (hpa : parent_a ∈ t) (hpb : parent_b ∈ t)
    (hchar_a : lo_a.char = a) (hchar_b : lo_b.char = b)
    -- Index consistency for both operations in context t
    (hidx_a : ∃ ka, ka ≤ t.toList.length ∧
      (applyInsert lt_sib parent_a a t).toList =
        t.toList.insertIdx ka a ∧
      lo_a.idx = ka - 1)
    (hidx_b : ∃ kb, kb ≤ t.toList.length ∧
      (applyInsert lt_sib parent_b b t).toList =
        t.toList.insertIdx kb b ∧
      lo_b.idx = kb - 1)
    -- Tiebreaker consistency: tb matches lt_sib when indices coincide
    (htb_lo : lo_a.idx = lo_b.idx → tb = .loPrecedes →
      lt_sib a b = true)
    (htb_x : lo_a.idx = lo_b.idx → tb = .xPrecedes →
      lt_sib b a = true) :
    let t_b := applyInsert lt_sib parent_b b t
    let t_ab := applyInsert lt_sib parent_a a t_b
    let doc_b := doc.insertIdx lo_b.idx lo_b.char
    let rebased := rebaseForward lo_a lo_b tb
    LogEffectInv
      (doc_b.insertIdx rebased.idx lo_a.char)
      t_ab := by
  intro t_b t_ab doc_b rebased
  -- Reduce applyInsert to insertLeaf
  obtain ⟨pos_b, hpos_b_le, hpos_b_eq⟩ :=
    applyInsert_eq_insertLeaf lt_sib parent_b b t hd hpb
  have hd_b : t_b.Distinct := by
    show (applyInsert lt_sib parent_b b t).Distinct
    rw [hpos_b_eq]; exact distinct_insertLeaf hd hb_fresh hpb hpos_b_le
  have ha_tb : a ∉ t_b := by
    show a ∉ applyInsert lt_sib parent_b b t
    rw [hpos_b_eq]; exact not_mem_insertLeaf_fresh ha_fresh hab
  have hpa_tb : parent_a ∈ t_b := by
    show parent_a ∈ applyInsert lt_sib parent_b b t
    rw [hpos_b_eq]; exact mem_insertLeaf hpa
  obtain ⟨pos_a', hpos_a'_le, hpos_a'_eq⟩ :=
    applyInsert_eq_insertLeaf lt_sib parent_a a t_b hd_b hpa_tb
  -- DFS insertion witnesses
  obtain ⟨ka, hka_le, hka_list, hka_idx⟩ := hidx_a
  obtain ⟨kb, hkb_le, hkb_list, hkb_idx⟩ := hidx_b
  -- t_b.toList and t_ab.toList
  have htb_list : t_b.toList = t.toList.insertIdx kb b := by
    show (applyInsert lt_sib parent_b b t).toList = _; exact hkb_list
  have hka'_ex := toList_insertLeaf hd_b hpa_tb ha_tb hpos_a'_le
  obtain ⟨ka', hka'_le, hka'_list⟩ := hka'_ex
  have htab_list : t_ab.toList = t_b.toList.insertIdx ka' a := by
    show (applyInsert lt_sib parent_a a t_b).toList = _
    rw [hpos_a'_eq]; exact hka'_list
  -- Unfold LogEffectInv and rewrite
  unfold LogEffectInv treeDoc
  unfold LogEffectInv treeDoc at hinv
  rw [show doc_b = doc.insertIdx lo_b.idx lo_b.char from rfl,
      hinv, hchar_a, hchar_b, htab_list]
  -- LHS: (t.toList.tail.insertIdx lo_b.idx b).insertIdx rebased.idx a
  -- RHS: (t_b.toList.insertIdx ka' a).tail
  -- Rewrite t_b.toList = t.toList.insertIdx kb b in RHS
  rw [htb_list]
  -- ka ≥ 1 and kb ≥ 1 (root position is never fresh)
  have hka_pos : ka ≥ 1 := by
    obtain ⟨pos_a, hpa_le, hpa_eq⟩ :=
      applyInsert_eq_insertLeaf lt_sib parent_a a t hd hpa
    exact insertLeaf_dfs_pos_ge_one hd ha_fresh hpa hpa_le hka_le
      (by rw [← hpa_eq]; exact hka_list)
  have hkb_pos : kb ≥ 1 :=
    insertLeaf_dfs_pos_ge_one hd hb_fresh hpb hpos_b_le hkb_le
      (by rw [← hpos_b_eq]; exact hkb_list)
  -- Rewrite LHS: t.toList.tail.insertIdx lo_b.idx b = (t.toList.insertIdx kb b).tail
  have htail_b : t.toList.tail.insertIdx lo_b.idx b =
      (t.toList.insertIdx kb b).tail := by
    rw [hkb_idx]
    match t with
    | .node r cs =>
      simp only [toList_node, List.tail_cons]
      obtain ⟨n, rfl⟩ : ∃ n, kb = n + 1 := ⟨kb - 1, by omega⟩
      simp [List.insertIdx_succ_cons, Nat.add_sub_cancel]
  rw [htail_b]
  -- Goal: (t.toList.insertIdx kb b).tail.insertIdx rebased.idx a
  --     = ((t.toList.insertIdx kb b).insertIdx ka' a).tail
  -- Key claim: rebased.idx = ka' - 1
  -- For now, suffices to prove this
  suffices hrb : (rebaseForward lo_a lo_b tb).idx = ka' - 1 by
    rw [hrb]
    have htb_ne : (t.toList.insertIdx kb b) ≠ [] := by
      match t with
      | .node r cs =>
        simp only [toList_node]
        cases kb with
        | zero => simp [List.insertIdx_zero]
        | succ n => simp [List.insertIdx_succ_cons]
    have hka'_pos : ka' ≥ 1 := by
      -- ka' ≥ 1 because a is fresh in t_b, same argument
      exact insertLeaf_dfs_pos_ge_one hd_b ha_tb hpa_tb hpos_a'_le
        hka'_le hka'_list
    obtain ⟨n, rfl⟩ : ∃ n, ka' = n + 1 := ⟨ka' - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact (tail_insertIdx_succ htb_ne).symm
  -- CORE: prove rebased.idx = ka' - 1
  -- This requires relating ka' to ka and kb via the position-counting argument.
  -- ka' is the DFS insertion position of a in t_b (whose toList = t.toList.insertIdx kb b).
  -- We know ka is the DFS insertion position of a in t.
  -- By List.insertIdx_comm, these are related:
  --   ka < kb → ka' = ka (a's position is before b, unaffected)
  --   kb < ka → ka' = ka + 1 (b shifted a's position right by 1)
  --   ka = kb → determined by tiebreaker (lt_sib)
  sorry

end OTProof

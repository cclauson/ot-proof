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

/-! ## Position uniqueness for insertIdx -/

/-- If `x ∉ l`, inserting `x` at two different valid positions gives
    different lists. Contrapositively: same list ⟹ same position. -/
private theorem insertIdx_pos_unique {l : List α} {x : α} {i j : Nat}
    (hx : x ∉ l) (hi : i ≤ l.length) (hj : j ≤ l.length)
    (heq : l.insertIdx i x = l.insertIdx j x) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi hj; omega
  | cons a l ih =>
    have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxl : x ∉ l := fun h => hx (List.mem_cons_of_mem a h)
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        -- heq : x :: a :: l = a :: l.insertIdx j x → x = a, contradiction
        rw [List.insertIdx_zero, List.insertIdx_succ_cons] at heq
        exact absurd (List.cons.inj heq).1 hxa
    | succ i =>
      cases j with
      | zero =>
        rw [List.insertIdx_zero, List.insertIdx_succ_cons] at heq
        exact absurd (List.cons.inj heq).1.symm hxa
      | succ j =>
        rw [List.insertIdx_succ_cons, List.insertIdx_succ_cons] at heq
        simp only [List.length_cons, Nat.succ_le_succ_iff] at hi hj
        exact congr_arg Nat.succ (ih hxl hi hj (List.cons.inj heq).2)

/-- Given two representations of the same double insertion with `ka < kb`,
    the positions are determined: `ka' = ka` and `kb' = kb + 1`. -/
private theorem double_insertIdx_lt {l : List α} {a b : α}
    {ka kb ka' kb' : Nat}
    (ha : a ∉ l) (hb : b ∉ l) (hab : a ≠ b)
    (hka : ka ≤ l.length) (hkb : kb ≤ l.length)
    (hka' : ka' ≤ (l.insertIdx kb b).length)
    (hkb' : kb' ≤ (l.insertIdx ka a).length)
    (heq : (l.insertIdx kb b).insertIdx ka' a =
           (l.insertIdx ka a).insertIdx kb' b)
    (hlt : ka < kb) :
    ka' = ka ∧ kb' = kb + 1 := by
  induction l generalizing ka kb ka' kb' with
  | nil => simp at hka hkb; omega
  | cons c l ih =>
    have hac : a ≠ c := by intro h; exact ha (by simp [h])
    have hbc : b ≠ c := by intro h; exact hb (by simp [h])
    have hal : a ∉ l := fun h => ha (List.mem_cons_of_mem _ h)
    have hbl : b ∉ l := fun h => hb (List.mem_cons_of_mem _ h)
    -- Case split on ka, kb (using plain `cases` for direct substitution)
    cases ka with
    | zero =>
      cases kb with
      | zero => omega
      | succ kb =>
        simp only [List.insertIdx_succ_cons, List.insertIdx_zero,
                    List.length_cons, Nat.succ_le_succ_iff] at heq hkb hka' hkb' ⊢
        cases ka' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          cases kb' with
          | zero =>
            simp only [List.insertIdx_zero] at heq
            exact absurd (List.cons.inj heq).1 hab
          | succ kb' =>
            simp only [List.insertIdx_succ_cons] at heq
            obtain ⟨_, h2⟩ := List.cons.inj heq
            refine ⟨rfl, ?_⟩
            cases kb' with
            | zero =>
              simp only [List.insertIdx_zero] at h2
              exact absurd (List.cons.inj h2).1.symm hbc
            | succ m =>
              simp only [List.insertIdx_succ_cons] at h2
              have := insertIdx_pos_unique hbl hkb (by omega) (List.cons.inj h2).2
              omega
        | succ ka' =>
          simp only [List.insertIdx_succ_cons] at heq
          cases kb' with
          | zero =>
            simp only [List.insertIdx_zero] at heq
            exact absurd (List.cons.inj heq).1 hbc.symm
          | succ kb' =>
            simp only [List.insertIdx_succ_cons] at heq
            exact absurd (List.cons.inj heq).1 hac.symm
    | succ ka =>
      cases kb with
      | zero => omega
      | succ kb =>
        simp only [List.insertIdx_succ_cons, List.length_cons,
                    Nat.succ_le_succ_iff] at heq hka hkb hka' hkb' hlt ⊢
        cases ka' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          cases kb' with
          | zero =>
            simp only [List.insertIdx_zero] at heq
            exact absurd (List.cons.inj heq).1 hab
          | succ kb' =>
            simp only [List.insertIdx_succ_cons] at heq
            exact absurd (List.cons.inj heq).1 hac
        | succ ka' =>
          simp only [List.insertIdx_succ_cons] at heq
          cases kb' with
          | zero =>
            simp only [List.insertIdx_zero] at heq
            exact absurd (List.cons.inj heq).1 (Ne.symm hbc)
          | succ kb' =>
            simp only [List.insertIdx_succ_cons] at heq
            obtain ⟨_, htail⟩ := List.cons.inj heq
            have ⟨h1, h2⟩ := ih hal hbl (by omega) (by omega)
              (by omega) (by omega) htail (by omega)
            exact ⟨congr_arg Nat.succ h1, congr_arg Nat.succ h2⟩

/-- Symmetric version for `kb < ka`. -/
private theorem double_insertIdx_gt {l : List α} {a b : α}
    {ka kb ka' kb' : Nat}
    (ha : a ∉ l) (hb : b ∉ l) (hab : a ≠ b)
    (hka : ka ≤ l.length) (hkb : kb ≤ l.length)
    (hka' : ka' ≤ (l.insertIdx kb b).length)
    (hkb' : kb' ≤ (l.insertIdx ka a).length)
    (heq : (l.insertIdx kb b).insertIdx ka' a =
           (l.insertIdx ka a).insertIdx kb' b)
    (hgt : kb < ka) :
    ka' = ka + 1 ∧ kb' = kb := by
  -- Swap a/b roles and apply double_insertIdx_lt
  have heq' := heq.symm
  have ⟨h1, h2⟩ := double_insertIdx_lt hb ha hab.symm hkb hka hkb' hka' heq' hgt
  exact ⟨h2, h1⟩

/-- When `ka = kb`, the double-insertion equation has exactly two solutions. -/
private theorem double_insertIdx_eq {l : List α} {a b : α}
    {ka ka' kb' : Nat}
    (ha : a ∉ l) (hb : b ∉ l) (hab : a ≠ b)
    (hka : ka ≤ l.length)
    (hka' : ka' ≤ (l.insertIdx ka b).length)
    (hkb' : kb' ≤ (l.insertIdx ka a).length)
    (heq : (l.insertIdx ka b).insertIdx ka' a =
           (l.insertIdx ka a).insertIdx kb' b) :
    (ka' = ka ∧ kb' = ka + 1) ∨ (ka' = ka + 1 ∧ kb' = ka) := by
  induction l generalizing ka ka' kb' with
  | nil =>
    simp at hka; subst hka
    simp only [List.insertIdx_zero, List.length_singleton] at hka' hkb' heq
    -- ka' ≤ 1 and kb' ≤ 1, so 4 cases
    cases ka' with
    | zero =>
      cases kb' with
      | zero =>
        simp only [List.insertIdx_zero] at heq
        exact absurd (List.cons.inj heq).1 hab
      | succ n =>
        have : n = 0 := by omega
        subst this
        exact .inl ⟨rfl, rfl⟩
    | succ n =>
      have : n = 0 := by omega
      subst this
      cases kb' with
      | zero => exact .inr ⟨rfl, rfl⟩
      | succ m =>
        have : m = 0 := by omega
        subst this
        simp only [List.insertIdx_zero, List.insertIdx_succ_cons] at heq
        exact absurd (List.cons.inj heq).1 hab.symm
  | cons c l ih =>
    have hac : a ≠ c := fun h => ha (h ▸ List.mem_cons_self ..)
    have hbc : b ≠ c := fun h => hb (h ▸ List.mem_cons_self ..)
    have hal : a ∉ l := fun h => ha (List.mem_cons_of_mem _ h)
    have hbl : b ∉ l := fun h => hb (List.mem_cons_of_mem _ h)
    cases ka with
    | zero =>
      simp only [List.insertIdx_zero, List.length_cons] at heq hka' hkb' ⊢
      cases ka' with
      | zero =>
        simp only [List.insertIdx_zero] at heq
        cases kb' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          exact absurd (List.cons.inj heq).1 hab
        | succ kb' =>
          simp only [List.insertIdx_succ_cons] at heq
          obtain ⟨_, h2⟩ := List.cons.inj heq
          left; refine ⟨rfl, ?_⟩
          cases kb' with
          | zero => simp only [List.insertIdx_zero] at h2; rfl
          | succ m =>
            simp only [List.insertIdx_succ_cons] at h2
            exact absurd (List.cons.inj h2).1 hbc
      | succ ka' =>
        simp only [List.insertIdx_succ_cons] at heq
        cases kb' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          obtain ⟨_, h2⟩ := List.cons.inj heq
          right; refine ⟨?_, rfl⟩
          cases ka' with
          | zero => simp only [List.insertIdx_zero] at h2; rfl
          | succ m =>
            simp only [List.insertIdx_succ_cons] at h2
            exact absurd (List.cons.inj h2).1.symm hac
        | succ kb' =>
          simp only [List.insertIdx_succ_cons] at heq
          exact absurd (List.cons.inj heq).1.symm hab
    | succ ka =>
      simp only [List.insertIdx_succ_cons, List.length_cons,
                  Nat.succ_le_succ_iff] at heq hka hka' hkb' ⊢
      cases ka' with
      | zero =>
        simp only [List.insertIdx_zero] at heq
        cases kb' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          exact absurd (List.cons.inj heq).1 hab
        | succ kb' =>
          simp only [List.insertIdx_succ_cons] at heq
          exact absurd (List.cons.inj heq).1 hac
      | succ ka' =>
        simp only [List.insertIdx_succ_cons] at heq
        cases kb' with
        | zero =>
          simp only [List.insertIdx_zero] at heq
          exact absurd (List.cons.inj heq).1 (Ne.symm hbc)
        | succ kb' =>
          simp only [List.insertIdx_succ_cons] at heq
          obtain ⟨_, htail⟩ := List.cons.inj heq
          rcases ih hal hbl (by omega) (by omega) (by omega) htail with
            ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact .inl ⟨congr_arg Nat.succ h1, congr_arg Nat.succ h2⟩
          · exact .inr ⟨congr_arg Nat.succ h1, congr_arg Nat.succ h2⟩

/-- Inserting b at k then a at k+1 gives PrecedesIn b a. -/
private theorem precedesIn_insertIdx_succ {l : List α} {a b : α} {k : Nat}
    (hk : k ≤ l.length) :
    PrecedesIn b a ((l.insertIdx k b).insertIdx (k + 1) a) := by
  induction l generalizing k with
  | nil =>
    simp at hk; subst hk
    exact ⟨[], [], [], by simp [List.insertIdx_zero, List.insertIdx_succ_cons]⟩
  | cons c l ih =>
    cases k with
    | zero =>
      exact ⟨[], [], c :: l, by simp [List.insertIdx_zero, List.insertIdx_succ_cons]⟩
    | succ k =>
      simp only [List.insertIdx_succ_cons]
      exact (ih (by simp only [List.length_cons] at hk; omega)).cons c

/-- Inserting b at k then a at k gives PrecedesIn a b. -/
private theorem precedesIn_insertIdx_self {l : List α} {a b : α} {k : Nat}
    (hk : k ≤ l.length) :
    PrecedesIn a b ((l.insertIdx k b).insertIdx k a) := by
  induction l generalizing k with
  | nil =>
    simp at hk; subst hk
    exact ⟨[], [], [], by simp [List.insertIdx_zero]⟩
  | cons c l ih =>
    cases k with
    | zero =>
      exact ⟨[], [], c :: l, by simp [List.insertIdx_zero]⟩
    | succ k =>
      simp only [List.insertIdx_succ_cons]
      exact (ih (by simp only [List.length_cons] at hk; omega)).cons c

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
    -- lt_sib properties (needed for applyInsert_comm)
    (hlt_trans : ∀ x y z, lt_sib x y = true → lt_sib y z = true → lt_sib x z = true)
    (hlt_total_ab : lt_sib a b = true ∨ lt_sib b a = true)
    (hlt_asym_ab : lt_sib a b = true → lt_sib b a = false)
    -- Tiebreaker consistency: when indices coincide, DFS ordering is determined
    (htb_lo : lo_a.idx = lo_b.idx → tb = .loPrecedes →
      PrecedesIn a b (applyInsert lt_sib parent_a a
        (applyInsert lt_sib parent_b b t)).toList)
    (htb_x : lo_a.idx = lo_b.idx → tb = .xPrecedes →
      PrecedesIn b a (applyInsert lt_sib parent_a a
        (applyInsert lt_sib parent_b b t)).toList) :
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
  -- Way B: use applyInsert_comm to get alternate DFS decomposition
  have hcomm := applyInsert_comm lt_sib hd ha_fresh hb_fresh hab hpa hpb
      hlt_trans hlt_total_ab hlt_asym_ab
  -- Properties of t_a = applyInsert lt_sib parent_a a t
  have hd_a : (applyInsert lt_sib parent_a a t).Distinct := by
    obtain ⟨pos, hle, heq⟩ := applyInsert_eq_insertLeaf lt_sib parent_a a t hd hpa
    rw [heq]; exact distinct_insertLeaf hd ha_fresh hpa hle
  have hb_ta : b ∉ applyInsert lt_sib parent_a a t := by
    obtain ⟨pos, _, heq⟩ := applyInsert_eq_insertLeaf lt_sib parent_a a t hd hpa
    rw [heq]; exact not_mem_insertLeaf_fresh hb_fresh hab.symm
  have hpb_ta : parent_b ∈ applyInsert lt_sib parent_a a t := by
    obtain ⟨pos, _, heq⟩ := applyInsert_eq_insertLeaf lt_sib parent_a a t hd hpa
    rw [heq]; exact mem_insertLeaf hpb
  obtain ⟨_, hpos_b''_le, hpos_b''_eq⟩ :=
    applyInsert_eq_insertLeaf lt_sib parent_b b
      (applyInsert lt_sib parent_a a t) hd_a hpb_ta
  obtain ⟨kb', hkb'_le, hkb'_list⟩ :=
    toList_insertLeaf hd_a hpb_ta hb_ta hpos_b''_le
  -- Way A: t_ab.toList via inserting b first then a
  have htab_wayA : t_ab.toList = (t.toList.insertIdx kb b).insertIdx ka' a := by
    rw [htab_list, htb_list]
  -- Way B: t_ab.toList via inserting a first then b (using commutativity)
  have htab_wayB : t_ab.toList = (t.toList.insertIdx ka a).insertIdx kb' b := by
    show (applyInsert lt_sib parent_a a (applyInsert lt_sib parent_b b t)).toList = _
    rw [hcomm, hpos_b''_eq, hkb'_list, hka_list]
  -- Double insertion equation: equate Way A and Way B
  have heq_double : (t.toList.insertIdx kb b).insertIdx ka' a =
      (t.toList.insertIdx ka a).insertIdx kb' b :=
    htab_wayA.symm.trans htab_wayB
  -- Bounds for double_insertIdx lemmas
  have hka'_bound : ka' ≤ (t.toList.insertIdx kb b).length := by
    rw [← htb_list]; exact hka'_le
  have hkb'_bound : kb' ≤ (t.toList.insertIdx ka a).length := by
    rw [← hka_list]; exact hkb'_le
  -- Distinct for t_ab (needed for PrecedesIn antisymmetry in equal case)
  have hd_ab : t_ab.Distinct := by
    show (applyInsert lt_sib parent_a a t_b).Distinct
    rw [hpos_a'_eq]; exact distinct_insertLeaf hd_b ha_tb hpa_tb hpos_a'_le
  -- Now case-split on ka vs kb to determine ka'
  unfold rebaseForward
  simp only [hka_idx, hkb_idx]
  by_cases h1 : ka - 1 < kb - 1
  · -- ka < kb → ka' = ka
    simp [h1]
    have ⟨hka'_val, _⟩ := double_insertIdx_lt ha_fresh hb_fresh hab
        hka_le hkb_le hka'_bound hkb'_bound heq_double (by omega)
    omega
  · by_cases h2 : kb - 1 < ka - 1
    · -- kb < ka → ka' = ka + 1
      simp [h1, h2]
      have ⟨hka'_val, _⟩ := double_insertIdx_gt ha_fresh hb_fresh hab
          hka_le hkb_le hka'_bound hkb'_bound heq_double (by omega)
      omega
    · -- ka = kb → use tiebreaker
      have hkakb : ka = kb := by omega
      simp [h1, h2]
      -- Rewrite heq_double for equal positions
      have heq_eq : (t.toList.insertIdx ka b).insertIdx ka' a =
          (t.toList.insertIdx ka a).insertIdx kb' b := by
        have h := heq_double; rw [hkakb.symm] at h; exact h
      have hka'_bound' : ka' ≤ (t.toList.insertIdx ka b).length := by
        rw [hkakb]; exact hka'_bound
      cases tb with
      | loPrecedes =>
        simp
        -- double_insertIdx_eq: ka' = ka ∨ ka' = ka + 1
        rcases double_insertIdx_eq ha_fresh hb_fresh hab hka_le
            hka'_bound' hkb'_bound heq_eq with
          ⟨hka'_val, _⟩ | ⟨hka'_val, _⟩
        · omega  -- ka' = ka ✓
        · -- ka' = ka + 1 contradicts PrecedesIn from htb_lo
          exfalso
          have htab_form : t_ab.toList =
              (t.toList.insertIdx ka b).insertIdx (ka + 1) a := by
            rw [htab_wayA, hkakb.symm, hka'_val]
          have h_prec_ba : PrecedesIn b a t_ab.toList := by
            rw [htab_form]; exact precedesIn_insertIdx_succ hka_le
          exact precedesIn_antisymm hd_ab (htb_lo (by omega) rfl) h_prec_ba
      | xPrecedes =>
        simp
        -- double_insertIdx_eq: ka' = ka ∨ ka' = ka + 1
        rcases double_insertIdx_eq ha_fresh hb_fresh hab hka_le
            hka'_bound' hkb'_bound heq_eq with
          ⟨hka'_val, _⟩ | ⟨hka'_val, _⟩
        · -- ka' = ka contradicts PrecedesIn from htb_x
          exfalso
          have htab_form : t_ab.toList =
              (t.toList.insertIdx ka b).insertIdx ka a := by
            rw [htab_wayA, hkakb.symm, hka'_val]
          have h_prec_ab : PrecedesIn a b t_ab.toList := by
            rw [htab_form]; exact precedesIn_insertIdx_self hka_le
          exact precedesIn_antisymm hd_ab h_prec_ab (htb_x (by omega) rfl)
        · omega  -- ka' = ka + 1 ✓

end OTProof

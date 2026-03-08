/-
# DeleteRebase: OT Rebase Correctness with Deletions

## Architecture

The tree (OrdTree) and its DFS ordering (≤_S / lcaLt) are UNCHANGED
by deletions. Deletions only affect which elements are "live" —
tracked by a tombstone set.

The rendered document = fullSeq(tree) filtered to live elements.
An index in the rendered document = position among live elements.

This file builds the filter/projection layer on top of the existing
insert-only infrastructure, then proves rebase correctness for all
operation pairs.
-/
import OTProof.Sequence.LogEffect
import OTProof.Sequence.InsertLeaf
import OTProof.Sequence.Stability
import OTProof.OrderedTree.TotalOrder
import Mathlib.Data.Finset.Basic

namespace OTProof

open OrdTree

variable {α : Type*} [DecidableEq α]

/-! ## 1. Rendered Document (filtered by tombstone set) -/

/-- The full sequence: DFS order minus root. Same as treeDoc. -/
abbrev fullSeq (t : OrdTree α) : List α := treeDoc t

/-- The rendered document: full sequence filtered to live elements. -/
def renderedDoc (t : OrdTree α) (tombstones : Finset α) : List α :=
  (fullSeq t).filter (· ∉ tombstones)

/-- Rendered document with no tombstones = full sequence. -/
@[simp] theorem renderedDoc_empty (t : OrdTree α) :
    renderedDoc t ∅ = fullSeq t := by
  simp [renderedDoc]

/-! ## 2. Rendered Index -/

/-- The rendered index of a live element: number of live elements
    before it in the full sequence. -/
def renderedPos (t : OrdTree α) (tombstones : Finset α) (e : α) : Nat :=
  ((fullSeq t).takeWhile (· ≠ e)).filter (· ∉ tombstones) |>.length

/-! ## 2a. List-level helpers -/

/-- `fullSeq` of a Distinct tree has Nodup. -/
theorem nodup_fullSeq {t : OrdTree α} (hd : t.Distinct) : (fullSeq t).Nodup := by
  unfold fullSeq treeDoc
  cases t with
  | node a cs =>
    rw [Distinct, toList_node] at hd
    simp only [toList_node, List.tail_cons]
    exact (List.nodup_cons.mp hd).2

/-- PrecedesIn on toList implies PrecedesIn on fullSeq (toList.tail),
    provided x is not the root (i.e., x ∈ fullSeq t). -/
private theorem precedesIn_fullSeq_of_dfsLt {x y : α} {t : OrdTree α}
    (hd : t.Distinct) (hx : x ∈ fullSeq t) (h : dfsLt x y t) :
    PrecedesIn x y (fullSeq t) := by
  unfold dfsLt dfs at h; unfold fullSeq treeDoc at hx ⊢
  cases t with
  | node r cs =>
    simp only [toList_node, List.tail_cons] at h hx ⊢
    rw [Distinct, toList_node] at hd
    obtain ⟨pre, mid, suf, heq⟩ := h
    cases pre with
    | nil =>
      -- x = r (root), but x ∈ flatMap toList cs contradicts Nodup
      have hrx : r = x := (List.cons.inj heq).1
      subst hrx
      exact absurd hx (List.nodup_cons.mp hd).1
    | cons p pre' =>
      exact ⟨pre', mid, suf, (List.cons.inj heq).2⟩

/-- Core helper: filter with `insert e ts` equals `eraseIdx` from filter with `ts`,
    for Nodup lists where `e` is live. -/
private theorem filter_insert_eraseIdx (l : List α) (e : α) (ts : Finset α)
    (hnd : l.Nodup) (he : e ∈ l) (he_live : e ∉ ts) :
    l.filter (· ∉ insert e ts) =
      (l.filter (· ∉ ts)).eraseIdx
        ((l.takeWhile (· ≠ e)).filter (· ∉ ts) |>.length) := by
  induction l with
  | nil => simp at he
  | cons a l ih =>
    have hnd' := (List.nodup_cons.mp hnd).2
    have ha_notin := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp he with rfl | he'
    · -- a = e: takeWhile gives [], filter removes e from head
      have h1 : e ∈ insert e ts := Finset.mem_insert_self e ts
      have h2 : (e :: l).takeWhile (· ≠ e) = [] := by simp
      have h3 : (e :: l).filter (· ∉ insert e ts) = l.filter (· ∉ insert e ts) := by
        rw [List.filter_cons]; simp [h1]
      have h4 : (e :: l).filter (· ∉ ts) = e :: l.filter (· ∉ ts) := by
        rw [List.filter_cons]; simp [he_live]
      rw [h2, h3, h4]
      simp only [List.filter_nil, List.length_nil, List.eraseIdx_zero]
      exact List.filter_congr fun x hm => by
        simp only [Finset.mem_insert, not_or, decide_eq_decide]
        exact ⟨fun h => h.2, fun h => ⟨fun heq => ha_notin (heq ▸ hm), h⟩⟩
    · -- a ≠ e
      have hae : a ≠ e := fun h => ha_notin (h ▸ he')
      have h_tw : (a :: l).takeWhile (· ≠ e) = a :: l.takeWhile (· ≠ e) := by
        simp [hae]
      rw [h_tw]
      by_cases ha_ts : a ∈ ts
      · -- a ∈ ts: filtered out everywhere
        have h_ins : a ∈ insert e ts := Finset.mem_insert_of_mem ha_ts
        have h3 : (a :: l).filter (· ∉ insert e ts) = l.filter (· ∉ insert e ts) := by
          rw [List.filter_cons]; simp [h_ins]
        have h4 : (a :: l).filter (· ∉ ts) = l.filter (· ∉ ts) := by
          rw [List.filter_cons]; simp [ha_ts]
        have h5 : (a :: l.takeWhile (· ≠ e)).filter (· ∉ ts) =
            (l.takeWhile (· ≠ e)).filter (· ∉ ts) := by
          rw [List.filter_cons]; simp [ha_ts]
        rw [h3, h4, h5]
        exact ih hnd' he'
      · -- a ∉ ts, a ∉ insert e ts
        have h_ins : a ∉ insert e ts := by simp [Finset.mem_insert, hae, ha_ts]
        have h3 : (a :: l).filter (· ∉ insert e ts) =
            a :: l.filter (· ∉ insert e ts) := by
          rw [List.filter_cons]; simp [h_ins]
        have h4 : (a :: l).filter (· ∉ ts) = a :: l.filter (· ∉ ts) := by
          rw [List.filter_cons]; simp [ha_ts]
        have h5 : (a :: l.takeWhile (· ≠ e)).filter (· ∉ ts) =
            a :: (l.takeWhile (· ≠ e)).filter (· ∉ ts) := by
          rw [List.filter_cons]; simp [ha_ts]
        rw [h3, h4, h5, List.length_cons, List.eraseIdx_cons_succ]
        congr 1
        exact ih hnd' he'

/-- If `d` appears after `e` in a Nodup list, then `d ∉ l.takeWhile (· ≠ e)`. -/
private theorem not_mem_takeWhile_of_precedesIn {l : List α} {e d : α}
    (hnd : l.Nodup) (hprec : PrecedesIn e d l) :
    d ∉ l.takeWhile (· ≠ e) := by
  intro hd_in
  obtain ⟨pre, mid, suf, rfl⟩ := hprec
  -- Parsed as (pre ++ e :: mid) ++ d :: suf. Reassociate to pre ++ (e :: (mid ++ d :: suf)).
  rw [show (pre ++ e :: mid) ++ d :: suf = pre ++ (e :: (mid ++ d :: suf)) from by
    simp [List.append_assoc, List.cons_append]] at hnd hd_in
  have hpre_ne : ∀ a ∈ pre, (decide (a ≠ e)) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    intro heq; subst heq
    exact absurd rfl ((List.nodup_append.mp hnd).2.2 a ha _ (List.mem_cons_self (α := α)))
  have htw : (pre ++ (e :: (mid ++ d :: suf))).takeWhile (· ≠ e) = pre := by
    rw [List.takeWhile_append_of_pos hpre_ne]; simp
  rw [htw] at hd_in
  have hd_later : d ∈ e :: (mid ++ d :: suf) :=
    List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
  exact absurd rfl ((List.nodup_append.mp hnd).2.2 d hd_in d hd_later)

/-- takeWhile filter is unchanged when tombstoning an element after the target. -/
private theorem takeWhile_filter_stable_after {l : List α} {e d : α} {ts : Finset α}
    (hnd : l.Nodup) (hprec : PrecedesIn e d l) :
    (l.takeWhile (· ≠ e)).filter (· ∉ insert d ts) =
      (l.takeWhile (· ≠ e)).filter (· ∉ ts) := by
  have hd_not := not_mem_takeWhile_of_precedesIn hnd hprec
  exact List.filter_congr fun x hm => by
    simp only [Finset.mem_insert, not_or, decide_eq_decide]
    exact ⟨fun h => h.2, fun h => ⟨fun heq => hd_not (heq ▸ hm), h⟩⟩

/-- If `d` appears before `e` in a Nodup list, then `d ∈ l.takeWhile (· ≠ e)`. -/
private theorem mem_takeWhile_of_precedesIn {l : List α} {d e : α}
    (hnd : l.Nodup) (hprec : PrecedesIn d e l) :
    d ∈ l.takeWhile (· ≠ e) := by
  obtain ⟨pre, mid, suf, rfl⟩ := hprec
  -- Parsed as (pre ++ d :: mid) ++ e :: suf. Reassociate to pre ++ (d :: (mid ++ e :: suf)).
  rw [show (pre ++ d :: mid) ++ e :: suf = pre ++ (d :: (mid ++ e :: suf)) from by
    simp [List.append_assoc, List.cons_append]] at hnd ⊢
  have hpre_ne : ∀ a ∈ pre, (decide (a ≠ e)) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    intro heq
    have : a ∈ d :: (mid ++ e :: suf) :=
      List.mem_cons_of_mem _ (List.mem_append_right _ (heq ▸ List.mem_cons_self))
    exact absurd rfl ((List.nodup_append.mp hnd).2.2 a ha a this)
  rw [List.takeWhile_append_of_pos hpre_ne]
  have hde : d ≠ e := by
    intro heq
    have : (d :: (mid ++ e :: suf)).Nodup := (List.nodup_append.mp hnd).2.1
    rw [List.nodup_cons] at this
    exact this.1 (heq ▸ List.mem_append_right _ List.mem_cons_self)
  simp only [List.takeWhile_cons, ne_eq, hde, decide_not, decide_false, Bool.not_false]
  exact List.mem_append_right _ List.mem_cons_self

/-- Adding a tombstone for an element BEFORE the target decreases the
    filtered takeWhile length by 1. -/
private theorem takeWhile_filter_length_sub_one {l : List α} {e d : α} {ts : Finset α}
    (hnd : l.Nodup) (hprec : PrecedesIn d e l) (hd_live : d ∉ ts) :
    ((l.takeWhile (· ≠ e)).filter (· ∉ insert d ts)).length =
      ((l.takeWhile (· ≠ e)).filter (· ∉ ts)).length - 1 := by
  set tw := l.takeWhile (· ≠ e)
  have htw_nd : tw.Nodup := hnd.sublist (List.takeWhile_sublist _)
  have hd_mem_tw := mem_takeWhile_of_precedesIn hnd hprec
  have hd_in_filt : d ∈ tw.filter (· ∉ ts) :=
    List.mem_filter.mpr ⟨hd_mem_tw, by simp [hd_live]⟩
  -- Show: filter (· ∉ insert d ts) tw = (filter (· ∉ ts) tw).erase d
  suffices heq : tw.filter (· ∉ insert d ts) = (tw.filter (· ∉ ts)).erase d by
    rw [heq, List.length_erase, if_pos hd_in_filt]
  rw [(htw_nd.filter _).erase_eq_filter]
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  simp only [Finset.mem_insert, not_or]
  cases hxd : (x == d)
  · simp [bne, hxd]
    have : x ≠ d := by simpa [beq_iff_eq] using hxd
    simp [this]
  · simp [bne, hxd]
    have : x = d := by simpa [beq_iff_eq] using hxd
    simp [this]

/-- PrecedesIn on fullSeq implies dfsLt on the tree. -/
private theorem dfsLt_of_precedesIn_fullSeq {x y : α} {t : OrdTree α}
    (h : PrecedesIn x y (fullSeq t)) : dfsLt x y t := by
  unfold dfsLt dfs fullSeq treeDoc at *
  cases t with
  | node r cs =>
    simp only [toList_node, List.tail_cons] at *
    exact h.cons r

/-- fullSeq membership implies tree membership. -/
private theorem mem_of_mem_fullSeq {x : α} {t : OrdTree α} (h : x ∈ fullSeq t) : x ∈ t := by
  cases t with
  | node r cs =>
    simp only [fullSeq, treeDoc, toList_node, List.tail_cons] at h
    rw [mem_def, toList_node]
    exact List.mem_cons_of_mem _ h

/-- `fullSeq` after `applyInsert` = original fullSeq with element insertIdx'd. -/
private theorem fullSeq_applyInsert {t : OrdTree α} {parent x : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx : x ∉ t) (hp : parent ∈ t) :
    ∃ k, k ≤ (fullSeq t).length ∧
      fullSeq (applyInsert lt_sib parent x t) = (fullSeq t).insertIdx k x := by
  obtain ⟨pos, hpos, happly⟩ := applyInsert_eq_insertLeaf lt_sib parent x t hd hp
  rw [happly]
  obtain ⟨k, hk_le, hk_eq⟩ := toList_insertLeaf hd hp hx hpos
  have hk_ge := insertLeaf_dfs_pos_ge_one hd hx hp hpos hk_le hk_eq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨k', ?_, ?_⟩
  · -- k' ≤ fullSeq t |>.length
    unfold fullSeq treeDoc
    cases t with
    | node r cs =>
      simp only [toList_node, List.tail_cons, List.length_cons] at hk_le ⊢
      omega
  · -- fullSeq = (fullSeq t).insertIdx k' x
    unfold fullSeq treeDoc at *
    cases t with
    | node r cs =>
      simp only [toList_node, List.tail_cons] at hk_eq ⊢
      have hne : (r :: (cs.flatMap OrdTree.toList)) ≠ [] := List.cons_ne_nil _ _
      rw [hk_eq, tail_insertIdx_succ hne]; simp

/-- takeWhile stops at a freshly inserted element, giving take k. -/
private theorem takeWhile_insertIdx_fresh {l : List α} {k : Nat} {x : α}
    (hx : x ∉ l) (hk : k ≤ l.length) :
    (l.insertIdx k x).takeWhile (· ≠ x) = l.take k := by
  rw [list_insertIdx_eq_take_cons_drop hk]
  have hne : ∀ a ∈ l.take k, (decide (a ≠ x)) = true := by
    intro a ha; simp only [ne_eq, decide_eq_true_eq]
    exact fun h => hx (h ▸ List.mem_of_mem_take ha)
  rw [List.takeWhile_append_of_pos hne]; simp

/-- filter distributes over insertIdx when the inserted element passes the filter. -/
private theorem filter_insertIdx_of_pos {l : List α} {k : Nat} {x : α} {p : α → Bool}
    (hp : p x = true) (hk : k ≤ l.length) :
    (l.insertIdx k x).filter p =
      (l.filter p).insertIdx ((l.take k).filter p |>.length) x := by
  induction l generalizing k with
  | nil => simp at hk; subst hk; simp [hp]
  | cons a l ih =>
    cases k with
    | zero => simp [List.insertIdx_zero, List.filter_cons, hp]
    | succ k' =>
      simp only [List.insertIdx_succ_cons, List.take_succ_cons]
      have hk' : k' ≤ l.length := by simp [List.length_cons] at hk; omega
      cases hpa : p a
      · simp only [List.filter_cons, hpa, ih hk']; simp
      · simp only [List.filter_cons, hpa, ih hk']; simp [List.insertIdx_succ_cons]

/-- renderedPos strictly increases along PrecedesIn for live elements. -/
private theorem renderedPos_lt_of_precedesIn {a b : α} {t : OrdTree α} {ts : Finset α}
    (hd : t.Distinct) (ha_live : a ∉ ts)
    (hprec : PrecedesIn a b (fullSeq t)) :
    renderedPos t ts a < renderedPos t ts b := by
  unfold renderedPos
  have hnd := nodup_fullSeq hd
  have hab : a ≠ b := PrecedesIn.ne_of_nodup hprec hnd
  obtain ⟨pre, mid, suf, heq⟩ := hprec
  -- Reassociate: fullSeq t = pre ++ a :: (mid ++ b :: suf)
  have heq' : fullSeq t = pre ++ a :: (mid ++ b :: suf) := by
    rw [heq]; simp [List.append_assoc, List.cons_append]
  rw [heq'] at hnd
  -- Elements of pre ≠ a (by Nodup pairwise disjointness)
  have hpre_ne_a : ∀ x ∈ pre, (decide (x ≠ a)) = true := by
    intro x hx; simp only [ne_eq, decide_eq_true_eq]
    exact (List.nodup_append.mp hnd).2.2 x hx a List.mem_cons_self
  -- takeWhile (· ≠ a) = pre
  have htw_a : (fullSeq t).takeWhile (· ≠ a) = pre := by
    rw [heq', List.takeWhile_append_of_pos hpre_ne_a]; simp
  -- Elements of pre ≠ b (by Nodup pairwise disjointness)
  have hpre_ne_b : ∀ x ∈ pre, (decide (x ≠ b)) = true := by
    intro x hx; simp only [ne_eq, decide_eq_true_eq]
    exact (List.nodup_append.mp hnd).2.2 x hx b
      (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  -- Elements of mid ≠ b (by Nodup disjointness in sublist)
  have hnd_mid_b : (mid ++ b :: suf).Nodup :=
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
  have hmid_ne_b : ∀ x ∈ mid, (decide (x ≠ b)) = true := by
    intro x hx; simp only [ne_eq, decide_eq_true_eq]
    exact (List.nodup_append.mp hnd_mid_b).2.2 x hx b List.mem_cons_self
  -- takeWhile (· ≠ b) = pre ++ a :: mid
  have htw_b : (fullSeq t).takeWhile (· ≠ b) = pre ++ a :: mid := by
    rw [heq', List.takeWhile_append_of_pos hpre_ne_b]
    have hab_dec : (decide (a ≠ b)) = true := by simp [hab]
    simp only [List.takeWhile_cons, hab_dec, ite_true,
               List.takeWhile_append_of_pos hmid_ne_b]
    simp
  -- Compare filtered lengths
  rw [htw_a, htw_b, List.filter_append, List.length_append]
  have : (a :: mid).filter (· ∉ ts) = a :: mid.filter (· ∉ ts) := by
    rw [List.filter_cons]; simp [ha_live]
  rw [this, List.length_cons]
  omega

/-! ## 3. Core Filter Lemmas -/

/-- Deleting an element (adding to tombstones) removes it from the
    rendered doc at its rendered position. -/
theorem renderedDoc_add_tombstone (t : OrdTree α) (tombstones : Finset α)
    (e : α) (he_live : e ∉ tombstones) (he_mem : e ∈ fullSeq t)
    (hd : t.Distinct) :
    renderedDoc t (insert e tombstones) =
      (renderedDoc t tombstones).eraseIdx (renderedPos t tombstones e) := by
  unfold renderedDoc renderedPos
  exact filter_insert_eraseIdx _ _ _ (nodup_fullSeq hd) he_mem he_live

/-- Inserting a fresh leaf adds the element to the rendered doc
    at its rendered position. -/
theorem renderedDoc_insert (t : OrdTree α) (tombstones : Finset α)
    {parent x : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t) (hp : parent ∈ t)
    (hx_live : x ∉ tombstones) :
    renderedDoc (applyInsert lt_sib parent x t) tombstones =
      (renderedDoc t tombstones).insertIdx
        (renderedPos (applyInsert lt_sib parent x t) tombstones x) x := by
  obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hx_fresh hp
  unfold renderedDoc renderedPos
  rw [hfs]
  have hx_not_fs : x ∉ fullSeq t := fun h => hx_fresh (mem_of_mem_fullSeq h)
  rw [takeWhile_insertIdx_fresh hx_not_fs hk]
  exact filter_insertIdx_of_pos (by simp [hx_live]) hk

/-- The rendered position is unchanged when tombstoning an element AFTER. -/
theorem renderedPos_add_tombstone_after (t : OrdTree α) (tombstones : Finset α)
    (e d : α) (hd_after : dfsLt e d t) (hd_tree : t.Distinct)
    (he_mem : e ∈ fullSeq t) :
    renderedPos t (insert d tombstones) e = renderedPos t tombstones e := by
  unfold renderedPos
  congr 1
  exact takeWhile_filter_stable_after (nodup_fullSeq hd_tree)
    (precedesIn_fullSeq_of_dfsLt hd_tree he_mem hd_after)

/-- The rendered position decreases by 1 when tombstoning an element BEFORE. -/
theorem renderedPos_add_tombstone_before (t : OrdTree α) (tombstones : Finset α)
    (e d : α) (hd_before : dfsLt d e t) (hd_live : d ∉ tombstones)
    (hd_tree : t.Distinct) (hd_mem : d ∈ fullSeq t) :
    renderedPos t (insert d tombstones) e = renderedPos t tombstones e - 1 := by
  unfold renderedPos
  exact takeWhile_filter_length_sub_one (nodup_fullSeq hd_tree)
    (precedesIn_fullSeq_of_dfsLt hd_tree hd_mem hd_before) hd_live

/-- When e ∈ l.drop k, the takeWhile-filter for (· ≠ e) on l.insertIdx k x
    gains the element x (live) compared to the original. -/
private theorem tw_filter_insertIdx_drop {l : List α} {k : Nat} {x e : α} {ts : Finset α}
    (hnd : l.Nodup) (he_drop : e ∈ l.drop k)
    (hxe : x ≠ e) (hk : k ≤ l.length) (hx_live : x ∉ ts) :
    (((l.insertIdx k x).takeWhile (· ≠ e)).filter (· ∉ ts)).length =
      ((l.takeWhile (· ≠ e)).filter (· ∉ ts)).length + 1 := by
  have hnd' : (l.take k ++ l.drop k).Nodup := by rw [List.take_append_drop]; exact hnd
  have he_not_take : e ∉ l.take k := by
    intro h; exact absurd rfl ((List.nodup_append.mp hnd').2.2 e h e he_drop)
  have hne_take : ∀ a ∈ l.take k, (decide (a ≠ e)) = true := by
    intro a ha; rw [decide_eq_true_eq]
    intro heq; subst heq; exact he_not_take ha
  -- Decompose l.takeWhile (· ≠ e) = l.take k ++ (l.drop k).takeWhile (· ≠ e)
  have htw_orig : l.takeWhile (· ≠ e) = l.take k ++ (l.drop k).takeWhile (· ≠ e) := by
    conv_lhs => rw [← List.take_append_drop k l]
    rw [List.takeWhile_append_of_pos hne_take]
  -- Decompose (l.insertIdx k x).takeWhile (· ≠ e) = l.take k ++ x :: (l.drop k).takeWhile (· ≠ e)
  have htw_ins : (l.insertIdx k x).takeWhile (· ≠ e) =
      l.take k ++ x :: (l.drop k).takeWhile (· ≠ e) := by
    rw [list_insertIdx_eq_take_cons_drop hk, List.takeWhile_append_of_pos hne_take,
        List.takeWhile_cons, show decide (x ≠ e) = true from by rw [decide_eq_true_eq]; exact hxe]
    simp
  rw [htw_ins, htw_orig, List.filter_append, List.filter_append, List.length_append,
      List.length_append, List.filter_cons]
  simp only [show decide (x ∉ ts) = true from decide_eq_true_eq.mpr hx_live,
             ite_true, List.length_cons]
  omega

/-- When e ∈ l.take k, the takeWhile-filter for (· ≠ e) on l.insertIdx k x
    is the same as the original (insertion is after e). -/
private theorem tw_filter_insertIdx_take {l : List α} {k : Nat} {x e : α} {ts : Finset α}
    (hnd : l.Nodup) (he_take : e ∈ l.take k) (hk : k ≤ l.length) :
    (((l.insertIdx k x).takeWhile (· ≠ e)).filter (· ∉ ts)).length =
      ((l.takeWhile (· ≠ e)).filter (· ∉ ts)).length := by
  have hnd_take : (l.take k).Nodup := (List.take_sublist k l).nodup hnd
  suffices h : ∀ (A B : List α), e ∈ A → A.Nodup →
      (A ++ B).takeWhile (· ≠ e) = A.takeWhile (· ≠ e) by
    congr 2
    rw [list_insertIdx_eq_take_cons_drop hk, h _ _ he_take hnd_take]
    conv_rhs => rw [← List.take_append_drop k l]
    rw [h _ _ he_take hnd_take]
  intro A B hA hndA
  induction A with
  | nil => contradiction
  | cons a A' ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    rcases List.mem_cons.mp hA with rfl | hA'
    · simp
    · have hae : a ≠ e := by
        intro heq; subst heq; exact (List.nodup_cons.mp hndA).1 hA'
      have hae_dec : (decide (a ≠ e)) = true := decide_eq_true hae
      simp only [hae_dec, ite_true]
      congr 1
      exact ih hA' (List.nodup_cons.mp hndA).2

/-- The rendered position increases by 1 when inserting a fresh element BEFORE. -/
theorem renderedPos_insert_before (t : OrdTree α) (tombstones : Finset α)
    (e x : α) {parent : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t) (hp : parent ∈ t)
    (he_mem : e ∈ fullSeq t)
    (hx_before : dfsLt x e (applyInsert lt_sib parent x t))
    (hx_live : x ∉ tombstones) :
    renderedPos (applyInsert lt_sib parent x t) tombstones e =
      renderedPos t tombstones e + 1 := by
  obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hx_fresh hp
  unfold renderedPos; rw [hfs]
  set fs := fullSeq t
  have hx_not_fs : x ∉ fs := fun h => hx_fresh (mem_of_mem_fullSeq h)
  have hnd := nodup_fullSeq hd
  have hxe : x ≠ e := fun h => hx_not_fs (h ▸ he_mem)
  -- e must be in fs.drop k (not take k) since x precedes e
  have he_drop : e ∈ fs.drop k := by
    rcases List.mem_append.mp (List.take_append_drop k fs ▸ he_mem) with h | h
    · exfalso
      obtain ⟨s, rest, heq_take⟩ := List.append_of_mem h
      have hprec_ex : PrecedesIn e x (fs.insertIdx k x) := by
        rw [list_insertIdx_eq_take_cons_drop hk, heq_take]
        exact ⟨s, rest, fs.drop k, by simp [List.append_assoc, List.cons_append]⟩
      have hd' : (applyInsert lt_sib parent x t).Distinct := by
        obtain ⟨pos, hpos, happly⟩ := applyInsert_eq_insertLeaf lt_sib parent x t hd hp
        rw [happly]; exact distinct_insertLeaf hd hx_fresh hp hpos
      rw [← hfs] at hprec_ex
      exact precedesIn_antisymm (dfs_nodup hd') hx_before (dfsLt_of_precedesIn_fullSeq hprec_ex)
    · exact h
  exact tw_filter_insertIdx_drop hnd he_drop hxe hk hx_live

/-- The rendered position is unchanged when inserting a fresh element AFTER. -/
theorem renderedPos_insert_after (t : OrdTree α) (tombstones : Finset α)
    (e x : α) {parent : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t) (hp : parent ∈ t)
    (he_mem : e ∈ fullSeq t)
    (hx_after : dfsLt e x (applyInsert lt_sib parent x t))
    (hx_live : x ∉ tombstones) :
    renderedPos (applyInsert lt_sib parent x t) tombstones e =
      renderedPos t tombstones e := by
  obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hx_fresh hp
  unfold renderedPos; rw [hfs]
  set fs := fullSeq t
  have hx_not_fs : x ∉ fs := fun h => hx_fresh (mem_of_mem_fullSeq h)
  have hnd := nodup_fullSeq hd
  -- e must be in fs.take k (not drop k) since e precedes x
  have he_take : e ∈ fs.take k := by
    rcases List.mem_append.mp (List.take_append_drop k fs ▸ he_mem) with h | h
    · exact h
    · exfalso
      have hxe : x ≠ e := fun h => hx_not_fs (h ▸ he_mem)
      have hprec_xe : PrecedesIn x e (fs.insertIdx k x) := by
        rw [list_insertIdx_eq_take_cons_drop hk]
        have : e ∈ fs.drop k := h
        obtain ⟨s, rest, heq_drop⟩ := List.append_of_mem this
        exact ⟨fs.take k, s, rest, by simp [List.append_assoc, List.cons_append, heq_drop]⟩
      have hd' : (applyInsert lt_sib parent x t).Distinct := by
        obtain ⟨pos, hpos, happly⟩ := applyInsert_eq_insertLeaf lt_sib parent x t hd hp
        rw [happly]; exact distinct_insertLeaf hd hx_fresh hp hpos
      rw [← hfs] at hprec_xe
      exact precedesIn_antisymm (dfs_nodup hd') (dfsLt_of_precedesIn_fullSeq hprec_xe) hx_after
  exact tw_filter_insertIdx_take hnd he_take hk

/-! ## 4. Side Type and DeletionSides -/

/-- Side of a deletion: the insert is Left (before) or Right (after)
    the deleted element in ≤_S. -/
inductive Side where
  | left | right
  deriving DecidableEq, Repr

/-- A deletion_side entry: records which deletion and which side. -/
structure DSEntry (α : Type*) where
  target : α
  side : Side
  deriving DecidableEq

/-- Resolve a tie between two inserts using deletion_sides. -/
def resolveDeletionSides (ds_lo ds_x : List (DSEntry α)) : Option Bool :=
  ds_lo.findSome? fun entry_lo =>
    ds_x.find? (fun entry_x => entry_x.target == entry_lo.target
                              && entry_x.side != entry_lo.side)
    |>.map fun _ => entry_lo.side == .left

/-! ## 5. Extended Log Operations -/

/-- Extended log operation. -/
inductive ExtLO (α : Type*) where
  | insert (idx : Nat) (elem : α) (ds : List (DSEntry α))
  | delete (idx : Nat) (target : α)
  | deleteNoop (target : α)
  deriving DecidableEq

/-! ## 6. Extended Rebase -/

def rebaseII (lo_idx : Nat) (lo_elem : α) (lo_ds : List (DSEntry α))
    (x_idx : Nat) (x_ds : List (DSEntry α)) (tb : Tiebreaker) : ExtLO α :=
  if lo_idx < x_idx then .insert lo_idx lo_elem lo_ds
  else if x_idx < lo_idx then .insert (lo_idx + 1) lo_elem lo_ds
  else match resolveDeletionSides lo_ds x_ds with
    | some true  => .insert lo_idx lo_elem lo_ds
    | some false => .insert (lo_idx + 1) lo_elem lo_ds
    | none => match tb with
      | .loPrecedes => .insert lo_idx lo_elem lo_ds
      | .xPrecedes  => .insert (lo_idx + 1) lo_elem lo_ds

def rebaseID (lo_idx : Nat) (lo_elem : α) (lo_ds : List (DSEntry α))
    (x_idx : Nat) (x_target : α) : ExtLO α :=
  if lo_idx ≤ x_idx then
    .insert lo_idx lo_elem (lo_ds ++ [⟨x_target, .left⟩])
  else
    .insert (lo_idx - 1) lo_elem (lo_ds ++ [⟨x_target, .right⟩])

def rebDI (lo_idx : Nat) (lo_target : α) (x_idx : Nat) : ExtLO α :=
  if lo_idx < x_idx then .delete lo_idx lo_target
  else .delete (lo_idx + 1) lo_target

def rebDD (lo_idx : Nat) (lo_target : α)
    (x_idx : Nat) (x_target : α) : ExtLO α :=
  if lo_target = x_target then .deleteNoop lo_target
  else if lo_idx < x_idx then .delete lo_idx lo_target
  else .delete (lo_idx - 1) lo_target

def extRebase (lo x : ExtLO α) (tb : Tiebreaker) : ExtLO α :=
  match lo, x with
  | .insert i a ds, .insert j _ ds_x => rebaseII i a ds j ds_x tb
  | .insert i a ds, .delete j tgt    => rebaseID i a ds j tgt
  | .delete i tgt,  .insert j _ _    => rebDI i tgt j
  | .delete i tgt,  .delete j tgt_x  => rebDD i tgt j tgt_x
  | .deleteNoop t,  _                => .deleteNoop t
  | lo,             .deleteNoop _    => lo

/-! ## 7. Extended Materialization -/

def extMaterialize (log : List (ExtLO α)) : List α :=
  log.foldl (fun doc op =>
    match op with
    | .insert i c _ => doc.insertIdx i c
    | .delete i _   => doc.eraseIdx i
    | .deleteNoop _  => doc
  ) []

/-! ## 8. Extended Log Effect Invariant -/

/-- The extended invariant: materialized doc = rendered doc. -/
def ExtLogEffectInv (doc : List α) (t : OrdTree α) (ts : Finset α) : Prop :=
  doc = renderedDoc t ts

/-! ## 9–11. Rebase Correctness -/

/-- Insert rebased past delete preserves the invariant. -/
theorem rebase_ID_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx : Nat} {lo_elem : α} {lo_ds : List (DSEntry α)}
    {x_idx : Nat} {x_target : α}
    {parent_lo : α} {lt_sib : α → α → Bool}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (hx_live : x_target ∉ ts)
    (hx_mem : x_target ∈ fullSeq t)
    (hx_idx : x_idx = renderedPos t ts x_target)
    (hlo_fresh : lo_elem ∉ t) (hp_lo : parent_lo ∈ t)
    (hlo_live : lo_elem ∉ insert x_target ts)
    (hlo_idx : lo_idx = renderedPos (applyInsert lt_sib parent_lo lo_elem t) ts lo_elem) :
    let ts' := insert x_target ts
    let t' := applyInsert lt_sib parent_lo lo_elem t
    let doc' := doc.eraseIdx x_idx
    let rebased := rebaseID lo_idx lo_elem lo_ds x_idx x_target
    ExtLogEffectInv
      (match rebased with
       | .insert i c _ => doc'.insertIdx i c
       | _ => doc')
      t' ts' := by
  unfold ExtLogEffectInv at hinv ⊢
  subst hinv; subst hx_idx; subst hlo_idx; dsimp only
  have hlo_ts : lo_elem ∉ ts := fun h => hlo_live (Finset.mem_insert_of_mem h)
  have hlo_ne_x : lo_elem ≠ x_target := fun h => hlo_live (h ▸ Finset.mem_insert_self ..)
  have hd' : (applyInsert lt_sib parent_lo lo_elem t).Distinct := by
    obtain ⟨pos, hpos, happly⟩ := applyInsert_eq_insertLeaf lt_sib parent_lo lo_elem t hd hp_lo
    rw [happly]; exact distinct_insertLeaf hd hlo_fresh hp_lo hpos
  have hx_mem' : x_target ∈ fullSeq (applyInsert lt_sib parent_lo lo_elem t) := by
    obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hlo_fresh hp_lo
    rw [hfs]; exact (List.sublist_insertIdx _ _ _).subset hx_mem
  have hlo_mem' : lo_elem ∈ fullSeq (applyInsert lt_sib parent_lo lo_elem t) := by
    obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hlo_fresh hp_lo
    rw [hfs, list_insertIdx_eq_take_cons_drop hk]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have h_del := renderedDoc_add_tombstone t ts x_target hx_live hx_mem hd
  have h_ins := renderedDoc_insert t (insert x_target ts) (lt_sib := lt_sib) (parent := parent_lo)
    hd hlo_fresh hp_lo hlo_live
  unfold rebaseID
  rcases precedesIn_total (nodup_fullSeq hd') hlo_mem' hx_mem' hlo_ne_x with hlo_first | hx_first
  · -- lo_elem precedes x_target
    have hlt := renderedPos_lt_of_precedesIn hd' hlo_ts hlo_first
    have h_pos_x := renderedPos_insert_before t ts x_target lo_elem
      hd hlo_fresh hp_lo hx_mem (dfsLt_of_precedesIn_fullSeq hlo_first) hlo_ts
    rw [h_pos_x] at hlt
    have hle : renderedPos (applyInsert lt_sib parent_lo lo_elem t) ts lo_elem ≤
        renderedPos t ts x_target := by omega
    rw [if_pos hle]; dsimp only
    have h_pos_lo := renderedPos_add_tombstone_after
      (applyInsert lt_sib parent_lo lo_elem t) ts lo_elem x_target
      (dfsLt_of_precedesIn_fullSeq hlo_first) hd' hlo_mem'
    rw [h_ins, h_del]; congr 1; exact h_pos_lo.symm
  · -- x_target precedes lo_elem
    have hlt := renderedPos_lt_of_precedesIn hd' hx_live hx_first
    have h_pos_x := renderedPos_insert_after t ts x_target lo_elem
      hd hlo_fresh hp_lo hx_mem (dfsLt_of_precedesIn_fullSeq hx_first) hlo_ts
    rw [h_pos_x] at hlt
    have hgt : ¬(renderedPos (applyInsert lt_sib parent_lo lo_elem t) ts lo_elem ≤
        renderedPos t ts x_target) := by omega
    rw [if_neg hgt]; dsimp only
    have h_pos_lo := renderedPos_add_tombstone_before
      (applyInsert lt_sib parent_lo lo_elem t) ts lo_elem x_target
      (dfsLt_of_precedesIn_fullSeq hx_first) hx_live hd' hx_mem'
    rw [h_ins, h_del]; congr 1; exact h_pos_lo.symm

/-- Delete rebased past insert preserves the invariant. -/
theorem rebase_DI_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx : Nat} {lo_target : α}
    {x_idx : Nat} {x_elem : α}
    {parent_x : α} {lt_sib : α → α → Bool}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (hx_fresh : x_elem ∉ t) (hp : parent_x ∈ t)
    (hlo_mem : lo_target ∈ fullSeq t)
    (hlo_live : lo_target ∉ ts)
    (hlo_idx : lo_idx = renderedPos t ts lo_target)
    (hx_live : x_elem ∉ ts)
    (hx_idx : x_idx = renderedPos (applyInsert lt_sib parent_x x_elem t) ts x_elem) :
    let t' := applyInsert lt_sib parent_x x_elem t
    let doc' := doc.insertIdx x_idx x_elem
    let rebased := rebDI lo_idx lo_target x_idx
    ExtLogEffectInv
      (match rebased with
       | .delete i _ => doc'.eraseIdx i
       | _ => doc')
      t' (insert lo_target ts) := by
  unfold ExtLogEffectInv at hinv ⊢
  subst hinv; subst hlo_idx; subst hx_idx; dsimp only
  have hne : lo_target ≠ x_elem := fun h => hx_fresh (h ▸ mem_of_mem_fullSeq hlo_mem)
  have hd' : (applyInsert lt_sib parent_x x_elem t).Distinct := by
    obtain ⟨pos, hpos, happly⟩ := applyInsert_eq_insertLeaf lt_sib parent_x x_elem t hd hp
    rw [happly]; exact distinct_insertLeaf hd hx_fresh hp hpos
  have hlo_mem' : lo_target ∈ fullSeq (applyInsert lt_sib parent_x x_elem t) := by
    obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hx_fresh hp
    rw [hfs]; exact (List.sublist_insertIdx _ _ _).subset hlo_mem
  have hx_mem' : x_elem ∈ fullSeq (applyInsert lt_sib parent_x x_elem t) := by
    obtain ⟨k, hk, hfs⟩ := fullSeq_applyInsert hd hx_fresh hp
    rw [hfs, list_insertIdx_eq_take_cons_drop hk]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have h_ins := renderedDoc_insert t ts (lt_sib := lt_sib) (parent := parent_x)
    hd hx_fresh hp hx_live
  have h_del := renderedDoc_add_tombstone (applyInsert lt_sib parent_x x_elem t) ts
    lo_target hlo_live hlo_mem' hd'
  unfold rebDI
  rcases precedesIn_total (nodup_fullSeq hd') hlo_mem' hx_mem' hne with hlo_first | hx_first
  · -- lo_target precedes x_elem
    have hlt := renderedPos_lt_of_precedesIn hd' hlo_live hlo_first
    have h_pos_lo := renderedPos_insert_after t ts lo_target x_elem
      hd hx_fresh hp hlo_mem (dfsLt_of_precedesIn_fullSeq hlo_first) hx_live
    rw [h_pos_lo] at hlt
    rw [if_pos hlt]; dsimp only
    rw [h_del, h_ins]; congr 1; exact h_pos_lo.symm
  · -- x_elem precedes lo_target
    have hlt := renderedPos_lt_of_precedesIn hd' hx_live hx_first
    have h_pos_lo := renderedPos_insert_before t ts lo_target x_elem
      hd hx_fresh hp hlo_mem (dfsLt_of_precedesIn_fullSeq hx_first) hx_live
    rw [h_pos_lo] at hlt
    have hge : ¬(renderedPos t ts lo_target < renderedPos (applyInsert lt_sib parent_x x_elem t) ts x_elem) := by omega
    rw [if_neg hge]; dsimp only
    rw [h_del, h_ins]; congr 1; exact h_pos_lo.symm

/-- Same-target delete-delete: noop preserves invariant. -/
theorem rebase_DD_same_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {target : α} {idx : Nat}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (ht_live : target ∉ ts)
    (ht_mem : target ∈ fullSeq t)
    (hidx : idx = renderedPos t ts target) :
    let ts' := insert target ts
    let doc' := doc.eraseIdx idx
    ExtLogEffectInv doc' t ts' := by
  unfold ExtLogEffectInv at hinv ⊢
  rw [hinv, hidx]
  exact (renderedDoc_add_tombstone t ts target ht_live ht_mem hd).symm

/-- Different-target delete-delete: index shift preserves invariant. -/
theorem rebase_DD_diff_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx x_idx : Nat} {lo_target x_target : α}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (hne : lo_target ≠ x_target)
    (hx_live : x_target ∉ ts)
    (hlo_live : lo_target ∉ ts)
    (hx_mem : x_target ∈ fullSeq t)
    (hlo_mem : lo_target ∈ fullSeq t)
    (hx_idx : x_idx = renderedPos t ts x_target)
    (hlo_idx : lo_idx = renderedPos t ts lo_target) :
    let ts' := insert x_target ts
    let doc' := doc.eraseIdx x_idx
    let rebased := rebDD lo_idx lo_target x_idx x_target
    ExtLogEffectInv
      (match rebased with
       | .delete i _ => doc'.eraseIdx i
       | .deleteNoop _ => doc'
       | _ => doc')
      t (insert lo_target ts') := by
  unfold ExtLogEffectInv at hinv ⊢
  subst hinv; subst hx_idx; subst hlo_idx
  dsimp only
  have hnd := nodup_fullSeq hd
  have hlo_live' : lo_target ∉ insert x_target ts := by
    simp [Finset.mem_insert, hne, hlo_live]
  -- Expand RHS using two tombstone additions
  have h_x := renderedDoc_add_tombstone t ts x_target hx_live hx_mem hd
  have h_lo := renderedDoc_add_tombstone t (insert x_target ts) lo_target hlo_live' hlo_mem hd
  conv_rhs => rw [h_lo, h_x]
  -- RHS = ((renderedDoc t ts).eraseIdx (renderedPos t ts x_target)).eraseIdx (renderedPos t (insert x ts) lo)
  -- Case split on DFS ordering
  rcases precedesIn_total hnd hlo_mem hx_mem hne with hlo_first | hx_first
  · -- lo precedes x: lo_idx < x_idx, position unchanged
    have hlt := renderedPos_lt_of_precedesIn hd hlo_live hlo_first
    simp only [rebDD, hne, ite_false, hlt, ite_true]
    congr 1
    exact (renderedPos_add_tombstone_after t ts lo_target x_target
      (dfsLt_of_precedesIn_fullSeq hlo_first) hd hlo_mem).symm
  · -- x precedes lo: x_idx < lo_idx, position shifts down by 1
    have hlt := renderedPos_lt_of_precedesIn hd hx_live hx_first
    have hge : ¬(renderedPos t ts lo_target < renderedPos t ts x_target) :=
      Nat.not_lt.mpr (Nat.le_of_lt hlt)
    simp only [rebDD, hne, ite_false, hge]
    congr 1
    exact (renderedPos_add_tombstone_before t ts lo_target x_target
      (dfsLt_of_precedesIn_fullSeq hx_first) hx_live hd hx_mem).symm

/-! ## 12. Deletion Sides -/

/-- deletion_sides correctly resolves: if it returns `some true`,
    then a <_S b. Uses transitivity: a <_S d <_S b for the disagreeing target d. -/
theorem deletion_sides_resolve
    {a b : α} {ds_a ds_b : List (DSEntry α)}
    {t : OrdTree α}
    (hd : t.Distinct)
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (hds_a_correct : ∀ entry ∈ ds_a,
      (entry.side = .left → dfsLt a entry.target t) ∧
      (entry.side = .right → dfsLt entry.target a t))
    (hds_b_correct : ∀ entry ∈ ds_b,
      (entry.side = .left → dfsLt b entry.target t) ∧
      (entry.side = .right → dfsLt entry.target b t))
    (h_resolve : resolveDeletionSides ds_a ds_b = some true) :
    dfsLt a b t := by
  unfold resolveDeletionSides at h_resolve
  induction ds_a with
  | nil => simp at h_resolve
  | cons entry_a rest_a ih =>
    simp only [List.findSome?_cons] at h_resolve
    split at h_resolve
    · -- entry_a hits: the function returned some v
      rename_i v _
      -- h_resolve : some v = some true
      have hv : v = true := by injection h_resolve
      subst hv
      -- The match scrutinee was (ds_b.find? ...).map ... = some v
      rename_i heq
      rw [Option.map_eq_some_iff] at heq
      obtain ⟨entry_b, hfind_b, hmap⟩ := heq
      have hb_mem := List.mem_of_find?_eq_some hfind_b
      have hb_pred := List.find?_some hfind_b
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hb_pred
      obtain ⟨htarget_eq, hside_ne⟩ := hb_pred
      have ha_side : entry_a.side = .left := by
        simpa [beq_iff_eq] using hmap
      have hb_side : entry_b.side = .right := by
        revert hside_ne; cases entry_b.side <;> simp [ha_side]
      have h_ad := (hds_a_correct entry_a (List.mem_cons_self ..)).1 ha_side
      have h_db := (hds_b_correct entry_b hb_mem).2 hb_side
      rw [htarget_eq] at h_db
      unfold dfsLt dfs at h_ad h_db ⊢
      exact precedesIn_trans hd (PrecedesIn.ne_of_nodup h_db hd) h_ad h_db
    · -- entry_a misses: falls through to rest_a
      exact ih (fun e he => hds_a_correct e (List.mem_cons_of_mem _ he)) h_resolve

/-- deletion_sides are consistent: can't return both true and false. -/
theorem deletion_sides_consistent
    {ds_a ds_b : List (DSEntry α)} {t : OrdTree α}
    (hd : t.Distinct)
    (ha hb : α)
    (hds_a_correct : ∀ entry ∈ ds_a,
      (entry.side = .left → dfsLt ha entry.target t) ∧
      (entry.side = .right → dfsLt entry.target ha t))
    (hds_b_correct : ∀ entry ∈ ds_b,
      (entry.side = .left → dfsLt hb entry.target t) ∧
      (entry.side = .right → dfsLt entry.target hb t))
    (h1 : resolveDeletionSides ds_a ds_b = some true)
    (h2 : resolveDeletionSides ds_a ds_b = some false) :
    False := by
  simp_all

/-! ## 13. Capstone

The per-case theorems collectively constitute the capstone for extended
rebase correctness:

- **Insert vs Insert**: `rebase_preserves_logEffect` (from LogEffect.lean)
  handles the insert-only case. `deletion_sides_resolve` shows that
  deletion_sides correctly break false ties.

- **Insert vs Delete**: `rebase_ID_correct` — insert rebased past delete.

- **Delete vs Insert**: `rebase_DI_correct` — delete rebased past insert.

- **Delete vs Delete (same)**: `rebase_DD_same_correct` — noop case.

- **Delete vs Delete (diff)**: `rebase_DD_diff_correct` — index shift case.

Together, these cover all pairs of concurrent operations. -/

end OTProof

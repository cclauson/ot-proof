/-
# Stability: lcaLt is preserved under leaf insertion

PrecedesIn preservation under insertIdx, dfsLt preservation,
and lcaLt stability — proving that existing ordering relationships
are undisturbed when a fresh leaf is added.
-/
import OTProof.InsertLeaf
import OTProof.Characterization
import OTProof.Consequences

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## S-1: PrecedesIn preservation under insertIdx -/

/-- PrecedesIn is preserved by sublists: if x precedes y in a sublist,
    then x precedes y in the superlist. -/
private theorem precedesIn_of_sublist_aux {x y : α} :
    ∀ {l₁ l₂ : List α},
    List.Sublist l₁ l₂ → PrecedesIn x y l₁ → PrecedesIn x y l₂ := by
  intro l₁ l₂ hs
  induction hs with
  | slnil => exact id
  | cons a _ ih => exact fun h => (ih h).cons a
  | cons₂ a _ ih =>
    intro h
    obtain ⟨pre, mid, suf, heq⟩ := h
    cases pre with
    | nil =>
      simp at heq
      obtain ⟨rfl, rfl⟩ := heq
      apply precedesIn_cons_of_mem
      exact ‹List.Sublist _ _›.subset
        (List.mem_append_right _ (List.mem_cons_self ..))
    | cons b pre' =>
      simp [List.cons_append] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact (ih ⟨pre', mid, suf, by simp [List.append_assoc]⟩).cons a

theorem PrecedesIn.of_sublist {x y : α} {l₁ l₂ : List α}
    (h : PrecedesIn x y l₁) (hs : List.Sublist l₁ l₂) : PrecedesIn x y l₂ :=
  precedesIn_of_sublist_aux hs h

/-- Inserting a new element into a list preserves PrecedesIn for
    existing elements. -/
theorem PrecedesIn.insertIdx {x y z : α} {l : List α} {k : Nat}
    (h : PrecedesIn x y l) (_hk : k ≤ l.length) :
    PrecedesIn x y (l.insertIdx k z) :=
  h.of_sublist (List.sublist_insertIdx l k z)

/-- Reverse: removing an inserted element preserves PrecedesIn for
    elements distinct from the inserted one. -/
theorem PrecedesIn.of_insertIdx {x y z : α} {l : List α} {k : Nat}
    (h : PrecedesIn x y (l.insertIdx k z))
    (hx : x ≠ z) (hy : y ≠ z)
    (hk : k ≤ l.length) :
    PrecedesIn x y l := by
  -- Decompose h into: l.insertIdx k z = pre ++ x :: mid ++ y :: suf
  -- and l = (l.insertIdx k z).eraseIdx k
  -- Since x ≠ z and y ≠ z, erasing z preserves the PrecedesIn witness.
  rw [list_insertIdx_eq_take_cons_drop hk] at h
  rw [← List.take_append_drop k l]
  -- Suffices: removing z from the middle of A ++ z :: B preserves PrecedesIn
  suffices ∀ (A B : List α),
      PrecedesIn x y (A ++ z :: B) → PrecedesIn x y (A ++ B) by
    exact this _ _ h
  intro A
  induction A with
  | nil =>
    intro B ⟨pre, mid, suf, heq⟩
    simp only [List.nil_append] at heq ⊢
    cases pre with
    | nil =>
      simp at heq
      exact absurd heq.1 (Ne.symm hx)
    | cons p pre' =>
      simp [List.cons_append] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨pre', mid, suf, by simp [List.append_assoc]⟩
  | cons a A' ih =>
    intro B ⟨pre, mid, suf, heq⟩
    cases pre with
    | nil =>
      simp at heq
      obtain ⟨rfl, hmid⟩ := heq
      apply precedesIn_cons_of_mem
      have hy_in : y ∈ A' ++ z :: B := by
        rw [hmid]; exact List.mem_append_right _ (List.mem_cons_self ..)
      rcases List.mem_append.mp hy_in with h₁ | h₂
      · exact List.mem_append_left _ h₁
      · exact List.mem_append_right _ ((List.mem_cons.mp h₂).resolve_left hy)
    | cons p pre' =>
      simp [List.cons_append] at heq
      obtain ⟨rfl, heq'⟩ := heq
      exact (ih _ ⟨pre', mid, suf, by simp [List.append_assoc] at heq' ⊢; exact heq'⟩).cons a

/-! ## S-2: dfsLt preservation -/

/-- DFS ordering is preserved by leaf insertion. -/
theorem dfsLt_insertLeaf [DecidableEq α] {a b : α} {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hp : parent ∈ t) (hx : x ∉ t)
    (hpos : pos ≤ numChildren parent t)
    (hab : dfsLt a b t) :
    dfsLt a b (insertLeaf t parent x pos) := by
  obtain ⟨k, hk_le, hk_eq⟩ := toList_insertLeaf hd hp hx hpos
  unfold dfsLt at hab ⊢
  show PrecedesIn a b (insertLeaf t parent x pos).toList
  rw [hk_eq]
  exact hab.insertIdx hk_le

/-- Reverse: dfsLt in the modified tree implies dfsLt in the original
    (for elements already in the tree). -/
theorem dfsLt_of_dfsLt_insertLeaf [DecidableEq α] {a b : α} {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hp : parent ∈ t) (hx : x ∉ t)
    (hpos : pos ≤ numChildren parent t)
    (ha : a ≠ x) (hb : b ≠ x)
    (hab : dfsLt a b (insertLeaf t parent x pos)) :
    dfsLt a b t := by
  obtain ⟨k, hk_le, hk_eq⟩ := toList_insertLeaf hd hp hx hpos
  unfold dfsLt dfs at hab ⊢
  rw [hk_eq] at hab
  exact hab.of_insertIdx ha hb hk_le

/-! ## S-3: lcaLt stability -/

/-- **lcaLt stability**: For elements already in the tree, their lcaLt
    ordering is unchanged by inserting a fresh leaf. -/
theorem lcaLt_stable_iff [DecidableEq α] {a b : α} {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hp : parent ∈ t) (hx : x ∉ t)
    (hpos : pos ≤ numChildren parent t)
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) :
    lcaLt a b t ↔ lcaLt a b (insertLeaf t parent x pos) := by
  have ha' : a ∈ insertLeaf t parent x pos := mem_insertLeaf ha
  have hb' : b ∈ insertLeaf t parent x pos := mem_insertLeaf hb
  have hd' : (insertLeaf t parent x pos).Distinct :=
    distinct_insertLeaf hd hx hp hpos
  have hax : a ≠ x := fun h => hx (h ▸ ha)
  have hbx : b ≠ x := fun h => hx (h ▸ hb)
  constructor
  · intro h
    exact (dfsLt_iff_lcaLt hd' ha' hb' hab).mp
      (dfsLt_insertLeaf hd hp hx hpos
        ((dfsLt_iff_lcaLt hd ha hb hab).mpr h))
  · intro h
    exact (dfsLt_iff_lcaLt hd ha hb hab).mp
      (dfsLt_of_dfsLt_insertLeaf hd hp hx hpos hax hbx
        ((dfsLt_iff_lcaLt hd' ha' hb' hab).mpr h))

end OrdTree

end OTProof

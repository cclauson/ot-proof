/-
# Rebase Correctness (Sections 7-8)

The `rebaseForward` function and Theorem 8.1 from
rebase-correctness-v0.1.md.

Key insight: the proof reduces to list-insertion commutativity
via `List.insertIdx_comm` from Lean 4 core.
-/

namespace OTProof

/-! ## Definitions -/

universe u

/-- A log operation: insert character `char` at index `idx`. -/
structure LO (α : Type u) where
  idx : Nat
  char : α

/-- Tiebreaker for concurrent inserts at the same index. -/
inductive Tiebreaker where
  | loPrecedes
  | xPrecedes

variable {α : Type u}

/-- Rebase `lo` forward past a concurrent insert `x`.
    Returns the adjusted LO with the correct index. -/
def rebaseForward (lo x : LO α) (tb : Tiebreaker) : LO α :=
  if lo.idx < x.idx then lo
  else if x.idx < lo.idx then LO.mk (lo.idx + 1) lo.char
  else match tb with
    | .loPrecedes => lo
    | .xPrecedes  => LO.mk (lo.idx + 1) lo.char

/-! ## Main theorem -/

/-- **Theorem 8.1 (Rebase Correctness).**

Inserting `a` at index `i` then `b` at the appropriate adjusted index
gives the same list as inserting `b` at index `j` then `a` at the
rebased index. The four cases (i < j, i > j, i = j with each
tiebreaker) all reduce to `List.insertIdx_comm`. -/
theorem rebase_correct (l : List α) (a b : α) (i j : Nat)
    (hi : i ≤ l.length) (hj : j ≤ l.length) (tb : Tiebreaker)
    (target : List α)
    (h_lt : i < j → target = (l.insertIdx i a).insertIdx (j + 1) b)
    (h_gt : j < i → target = (l.insertIdx i a).insertIdx j b)
    (h_eq_lo : i = j → tb = .loPrecedes →
        target = (l.insertIdx i a).insertIdx (i + 1) b)
    (h_eq_x : i = j → tb = .xPrecedes →
        target = (l.insertIdx i a).insertIdx i b) :
    target = (l.insertIdx j b).insertIdx (rebaseForward (LO.mk i a) (LO.mk j b) tb).idx a := by
  unfold rebaseForward
  simp only
  by_cases hij : i < j
  · -- Case i < j: rebase keeps index i
    simp [hij]
    rw [h_lt hij]
    exact List.insertIdx_comm a b (Nat.le_of_lt hij) hj
  · -- i ≥ j
    simp [hij]
    by_cases hji : j < i
    · -- Case j < i: rebase gives index i + 1
      simp [hji]
      rw [h_gt hji]
      exact (List.insertIdx_comm b a (Nat.le_of_lt hji) hi).symm
    · -- Case i = j
      simp [hji]
      have heq : i = j := Nat.le_antisymm (Nat.le_of_not_lt hji) (Nat.le_of_not_lt hij)
      subst heq
      cases tb with
      | loPrecedes =>
        simp
        rw [h_eq_lo rfl rfl]
        exact List.insertIdx_comm a b (Nat.le_refl i) hj
      | xPrecedes =>
        simp
        rw [h_eq_x rfl rfl]
        exact (List.insertIdx_comm b a (Nat.le_refl i) hi).symm

end OTProof

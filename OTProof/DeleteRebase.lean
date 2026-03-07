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

## Key insight

Every rebase case reduces to: "count live elements preceding the
target in ≤_S." This is the same position-counting argument as
insert-only, but counting over live elements instead of all elements.

## Dependencies

- OTProof.LogEffect (insert-only rebase, Log Effect Invariant)
- OTProof.InsertLeaf (applyInsert, tree operations)
- OTProof.Stability (lcaLt preserved under leaf insertion)
- OTProof.Consequences (lcaLt is a total order)
-/
import OTProof.LogEffect
import OTProof.InsertLeaf
import OTProof.Stability
import OTProof.Consequences

namespace OTProof

open OrdTree

variable {α : Type*} [DecidableEq α]

/-! ## 1. Rendered Document (filtered by tombstone set) -/

/-- The full sequence: DFS order minus root. Same as treeDoc.
    This does NOT change when elements are deleted — only when inserted. -/
abbrev fullSeq (t : OrdTree α) : List α := treeDoc t

/-- The rendered document: full sequence filtered to live elements. -/
def renderedDoc (t : OrdTree α) (tombstones : Finset α) : List α :=
  (fullSeq t).filter (· ∉ tombstones)

/-- Rendered document with no tombstones = full sequence. -/
@[simp] theorem renderedDoc_empty (t : OrdTree α) :
    renderedDoc t ∅ = fullSeq t := by
  simp [renderedDoc, List.filter_eq_self]

/-! ## 2. Rendered Index -/

/-- The rendered index of a live element: number of live elements
    before it in the full sequence. Returns the length of the
    rendered doc if e is not found (not live or not in tree). -/
def renderedPos (t : OrdTree α) (tombstones : Finset α) (e : α) : Nat :=
  ((fullSeq t).takeWhile (· ≠ e)).filter (· ∉ tombstones) |>.length

/-! ## 3. Core Filter Lemmas -/

/-- Deleting an element (adding to tombstones) removes it from the
    rendered doc. The rendered doc shrinks by 1 at the element's
    rendered position.

    This is the key lemma connecting tombstoning to list operations. -/
theorem renderedDoc_add_tombstone (t : OrdTree α) (tombstones : Finset α)
    (e : α) (he_live : e ∉ tombstones) (he_mem : e ∈ fullSeq t) :
    renderedDoc t (insert e tombstones) =
      (renderedDoc t tombstones).eraseIdx (renderedPos t tombstones e) := by
  sorry

/-- Inserting a fresh leaf adds the element to the rendered doc
    at its rendered position (determined by ≤_S among live elements). -/
theorem renderedDoc_insert (t : OrdTree α) (tombstones : Finset α)
    {parent x : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t) (hp : parent ∈ t)
    (hx_live : x ∉ tombstones) :
    renderedDoc (applyInsert lt_sib parent x t) tombstones =
      (renderedDoc t tombstones).insertIdx
        (renderedPos (applyInsert lt_sib parent x t) tombstones x) x := by
  sorry

/-- The rendered position of a live element doesn't change when a
    tombstone is added for a DIFFERENT element that is AFTER it in ≤_S. -/
theorem renderedPos_add_tombstone_after (t : OrdTree α) (tombstones : Finset α)
    (e d : α) (he_ne_d : e ≠ d) (hd_after : dfsLt e d t) :
    renderedPos t (insert d tombstones) e = renderedPos t tombstones e := by
  sorry

/-- The rendered position decreases by 1 when a tombstone is added
    for an element BEFORE it in ≤_S. -/
theorem renderedPos_add_tombstone_before (t : OrdTree α) (tombstones : Finset α)
    (e d : α) (hd_before : dfsLt d e t) (hd_live : d ∉ tombstones) :
    renderedPos t (insert d tombstones) e = renderedPos t tombstones e - 1 := by
  sorry

/-- The rendered position increases by 1 when a fresh element is
    inserted BEFORE it in ≤_S. -/
theorem renderedPos_insert_before (t : OrdTree α) (tombstones : Finset α)
    (e x : α) {parent : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t)
    (hx_before : dfsLt x e (applyInsert lt_sib parent x t))
    (hx_live : x ∉ tombstones) :
    renderedPos (applyInsert lt_sib parent x t) tombstones e =
      renderedPos t tombstones e + 1 := by
  sorry

/-- The rendered position is unchanged when a fresh element is
    inserted AFTER it in ≤_S. -/
theorem renderedPos_insert_after (t : OrdTree α) (tombstones : Finset α)
    (e x : α) {parent : α} {lt_sib : α → α → Bool}
    (hd : t.Distinct) (hx_fresh : x ∉ t)
    (hx_after : dfsLt e x (applyInsert lt_sib parent x t))
    (hx_live : x ∉ tombstones) :
    renderedPos (applyInsert lt_sib parent x t) tombstones e =
      renderedPos t tombstones e := by
  sorry

/-! ## 4. Side Type and DeletionSides -/

/-- Side of a deletion: the insert is Left (before) or Right (after)
    the deleted element in ≤_S. -/
inductive Side where
  | left   -- insert element <_S deleted element
  | right  -- deleted element <_S insert element
  deriving DecidableEq, Repr

/-- A deletion_side entry: records which deletion and which side. -/
structure DSEntry (α : Type*) where
  target : α
  side : Side
  deriving DecidableEq

/-- Resolve a tie between two inserts using deletion_sides.
    Returns `some true` if lo should come first (lo <_S x),
    `some false` if x should come first,
    `none` if no disagreement found (true tie). -/
def resolveDeletionSides (ds_lo ds_x : List (DSEntry α)) : Option Bool :=
  -- Find first target where sides disagree
  ds_lo.findSome? fun entry_lo =>
    ds_x.find? (fun entry_x => entry_x.target == entry_lo.target
                              && entry_x.side != entry_lo.side)
    |>.map fun entry_x =>
      -- lo is Left, x is Right → lo comes first (true)
      -- lo is Right, x is Left → x comes first (false)
      entry_lo.side == .left

/-! ## 5. Extended Log Operations -/

/-- Extended log operation. -/
inductive ExtLO (α : Type*) where
  | insert (idx : Nat) (elem : α) (ds : List (DSEntry α))
  | delete (idx : Nat) (target : α)  -- target is the element being deleted
  | deleteNoop (target : α)           -- target was already deleted
  deriving DecidableEq

/-! ## 6. Extended Rebase -/

/-- Rebase insert past insert. -/
def rebaseII (lo_idx : Nat) (lo_elem : α) (lo_ds : List (DSEntry α))
    (x_idx : Nat) (x_ds : List (DSEntry α)) (tb : Tiebreaker) : ExtLO α :=
  if lo_idx < x_idx then .insert lo_idx lo_elem lo_ds
  else if x_idx < lo_idx then .insert (lo_idx + 1) lo_elem lo_ds
  else -- same index: check deletion_sides, then tiebreaker
    match resolveDeletionSides lo_ds x_ds with
    | some true  => .insert lo_idx lo_elem lo_ds       -- lo first
    | some false => .insert (lo_idx + 1) lo_elem lo_ds -- x first
    | none =>  -- true tie, use tiebreaker
      match tb with
      | .loPrecedes => .insert lo_idx lo_elem lo_ds
      | .xPrecedes  => .insert (lo_idx + 1) lo_elem lo_ds

/-- Rebase insert past delete. Records deletion side. -/
def rebaseID (lo_idx : Nat) (lo_elem : α) (lo_ds : List (DSEntry α))
    (x_idx : Nat) (x_target : α) : ExtLO α :=
  if lo_idx ≤ x_idx then
    .insert lo_idx lo_elem (lo_ds ++ [⟨x_target, .left⟩])
  else
    .insert (lo_idx - 1) lo_elem (lo_ds ++ [⟨x_target, .right⟩])

/-- Rebase delete past insert. -/
def rebDI (lo_idx : Nat) (lo_target : α)
    (x_idx : Nat) : ExtLO α :=
  if lo_idx < x_idx then .delete lo_idx lo_target
  else .delete (lo_idx + 1) lo_target

/-- Rebase delete past delete. -/
def rebDD (lo_idx : Nat) (lo_target : α)
    (x_idx : Nat) (x_target : α) : ExtLO α :=
  if lo_target = x_target then .deleteNoop lo_target  -- same element
  else if lo_idx < x_idx then .delete lo_idx lo_target
  else .delete (lo_idx - 1) lo_target

/-- Full extended rebase. -/
def extRebase (lo x : ExtLO α) (tb : Tiebreaker) : ExtLO α :=
  match lo, x with
  | .insert i a ds, .insert j _ ds_x => rebaseII i a ds j ds_x tb
  | .insert i a ds, .delete j tgt    => rebaseID i a ds j tgt
  | .delete i tgt,  .insert j _ _    => rebDI i tgt j
  | .delete i tgt,  .delete j tgt_x  => rebDD i tgt j tgt_x
  | .deleteNoop t,  _                => .deleteNoop t
  | lo,             .deleteNoop _    => lo

/-! ## 7. Extended Materialization -/

/-- Materialize an extended log via foldl. -/
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

/-! ## 9. Rebase Correctness — Insert vs Delete (§5.2) -/

/-- When insert lo is rebased past delete x:
    - If lo_idx ≤ x_idx (insert at or before delete): lo is Left of deletion,
      rendered index unchanged because deleted element was at or after.
    - If lo_idx > x_idx (insert after delete): lo is Right of deletion,
      rendered index decreases by 1 because deleted element was before. -/
theorem rebase_ID_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx : Nat} {lo_elem : α} {lo_ds : List (DSEntry α)}
    {x_idx : Nat} {x_target : α}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    -- lo inserts lo_elem at rendered position lo_idx
    -- x deletes x_target at rendered position x_idx
    -- x_target is live
    (hx_live : x_target ∉ ts)
    -- After applying x (tombstoning x_target), then rebased lo:
    :
    let ts' := insert x_target ts
    let doc' := doc.eraseIdx x_idx
    let rebased := rebaseID lo_idx lo_elem lo_ds x_idx x_target
    ExtLogEffectInv
      (match rebased with
       | .insert i c _ => doc'.insertIdx i c
       | _ => doc')
      t ts' := by
  sorry

/-! ## 10. Rebase Correctness — Delete vs Insert (§5.3) -/

theorem rebase_DI_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx : Nat} {lo_target : α}
    {x_idx : Nat} {x_elem : α} {x_ds : List (DSEntry α)}
    {parent_x : α} {lt_sib : α → α → Bool}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (hx_fresh : x_elem ∉ t) (hp : parent_x ∈ t)
    -- After applying x (inserting x_elem), then rebased lo (delete):
    :
    let t' := applyInsert lt_sib parent_x x_elem t
    let doc' := doc.insertIdx x_idx x_elem
    let rebased := rebDI lo_idx lo_target x_idx
    ExtLogEffectInv
      (match rebased with
       | .delete i _ => doc'.eraseIdx i
       | _ => doc')
      t' (insert lo_target ts) := by
  sorry

/-! ## 11. Rebase Correctness — Delete vs Delete (§5.4-5.5) -/

/-- Same target: noop. -/
theorem rebase_DD_same_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {target : α} {idx : Nat}
    (hinv : ExtLogEffectInv doc t ts)
    (ht_live : target ∉ ts) :
    let ts' := insert target ts
    let doc' := doc.eraseIdx idx
    -- After x deletes target, lo's delete of same target is noop
    ExtLogEffectInv doc' t ts' := by
  sorry

/-- Different targets: index shifts. -/
theorem rebase_DD_diff_correct
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo_idx x_idx : Nat} {lo_target x_target : α}
    (hinv : ExtLogEffectInv doc t ts)
    (hd : t.Distinct)
    (hne : lo_target ≠ x_target)
    (hx_live : x_target ∉ ts) :
    let ts' := insert x_target ts
    let doc' := doc.eraseIdx x_idx
    let rebased := rebDD lo_idx lo_target x_idx x_target
    ExtLogEffectInv
      (match rebased with
       | .delete i _ => doc'.eraseIdx i
       | _ => doc')
      t (insert lo_target ts') := by
  sorry

/-! ## 12. Rebase Correctness — Insert vs Insert with deletion_sides (§5.6) -/

/-- deletion_sides correctly resolves false ties:
    if two inserts have the same rendered index but different ≤_S positions
    (separated by tombstones), deletion_sides finds the disagreement. -/
theorem deletion_sides_resolve
    {a b : α} {ds_a ds_b : List (DSEntry α)}
    {t : OrdTree α}
    (hd : t.Distinct)
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    -- ds_a correctly records a's side of each deletion
    (hds_a_correct : ∀ entry ∈ ds_a,
      (entry.side = .left → dfsLt a entry.target t) ∧
      (entry.side = .right → dfsLt entry.target a t))
    -- ds_b correctly records b's side of each deletion
    (hds_b_correct : ∀ entry ∈ ds_b,
      (entry.side = .left → dfsLt b entry.target t) ∧
      (entry.side = .right → dfsLt entry.target b t))
    -- If deletion_sides says lo first (a <_S b):
    (h_resolve : resolveDeletionSides ds_a ds_b = some true) :
    dfsLt a b t := by
  sorry

/-- deletion_sides are consistent: all disagreements give the same answer. -/
theorem deletion_sides_consistent
    {ds_a ds_b : List (DSEntry α)} {t : OrdTree α}
    (hd : t.Distinct)
    (ha : α) (hb : α)
    (hds_a_correct : ∀ entry ∈ ds_a,
      (entry.side = .left → dfsLt ha entry.target t) ∧
      (entry.side = .right → dfsLt entry.target ha t))
    (hds_b_correct : ∀ entry ∈ ds_b,
      (entry.side = .left → dfsLt hb entry.target t) ∧
      (entry.side = .right → dfsLt entry.target hb t))
    -- Can't get both `some true` and `some false`
    (h1 : resolveDeletionSides ds_a ds_b = some true)
    (h2 : resolveDeletionSides ds_a ds_b = some false) :
    False := by
  simp_all

/-! ## 13. Capstone -/

/-- **Extended rebase preserves the Log Effect Invariant.**
    For any concurrent operations lo and x (insert or delete),
    applying x then extRebase(lo, x) produces a document equal
    to the rendered document of the correct tree and tombstone state. -/
theorem ext_rebase_preserves_invariant
    {doc : List α} {t : OrdTree α} {ts : Finset α}
    {lo x : ExtLO α} {tb : Tiebreaker}
    (hd : t.Distinct)
    (hinv : ExtLogEffectInv doc t ts)
    -- ... preconditions for each operation ...
    :
    sorry -- state depends on the shape of lo and x
    := by
  sorry

end OTProof

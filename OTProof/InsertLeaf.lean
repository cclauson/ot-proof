/-
# InsertLeaf: Tree insertion and DFS decomposition

Defines `insertLeaf` (insert a new leaf as a child of a given parent)
and proves that DFS of the modified tree equals the old DFS with the
new element `insertIdx`'d at a specific position.
-/
import OTProof.DFS
import Mathlib.Data.List.InsertIdx

namespace OTProof

namespace OrdTree

variable {α : Type*}

/-! ## Definitions -/

/-- Number of children of the node labeled `a` in tree `t`.
    Returns 0 if `a` is not found. -/
def numChildren [DecidableEq α] (a : α) : OrdTree α → Nat
  | .node b cs =>
    if b = a then cs.length
    else cs.foldl (fun acc c => acc + numChildren a c) 0

@[simp] theorem numChildren_node [DecidableEq α] (a b : α) (cs : List (OrdTree α)) :
    numChildren a (.node b cs) =
      if b = a then cs.length
      else cs.foldl (fun acc c => acc + numChildren a c) 0 := by
  conv_lhs => unfold numChildren

/-- Insert a new leaf with label `x` as the `pos`-th child of the node
    labeled `parent`. If `parent` not found, tree unchanged. -/
def insertLeaf [DecidableEq α] : OrdTree α → α → α → Nat → OrdTree α
  | .node a cs, parent, x, pos =>
    if a = parent then .node a (cs.insertIdx pos (.node x []))
    else .node a (cs.map fun c => insertLeaf c parent x pos)

@[simp] theorem insertLeaf_node [DecidableEq α] (a : α) (cs : List (OrdTree α))
    (parent x : α) (pos : Nat) :
    insertLeaf (.node a cs) parent x pos =
      if a = parent then .node a (cs.insertIdx pos (.node x []))
      else .node a (cs.map fun c => insertLeaf c parent x pos) := by
  conv_lhs => unfold insertLeaf

/-- The root label is unchanged by insertLeaf. -/
@[simp] theorem label_insertLeaf [DecidableEq α] (t : OrdTree α)
    (parent x : α) (pos : Nat) :
    (insertLeaf t parent x pos).label = t.label := by
  cases t with
  | node a cs =>
    simp only [insertLeaf_node]
    split <;> simp [label]

/-! ## Helper: insertIdx = take ++ [v] ++ drop -/

/-- `List.insertIdx` decomposes as take ++ v :: drop when pos ≤ length. -/
theorem list_insertIdx_eq_take_cons_drop {l : List α} {v : α} {pos : Nat}
    (h : pos ≤ l.length) :
    l.insertIdx pos v = l.take pos ++ v :: l.drop pos := by
  induction l generalizing pos with
  | nil =>
    simp at h; subst h
    simp [List.insertIdx_zero]
  | cons a l ih =>
    cases pos with
    | zero => simp [List.insertIdx_zero]
    | succ n =>
      simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append]
      congr 1
      exact ih (Nat.le_of_succ_le_succ h)

/-! ## Helper: insertLeaf is identity when parent not in tree -/

/-- If parent is not in the tree, insertLeaf returns the tree unchanged. -/
@[simp] theorem insertLeaf_of_not_mem [DecidableEq α] {t : OrdTree α}
    {parent x : α} {pos : Nat} (h : parent ∉ t) :
    insertLeaf t parent x pos = t := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node]
    split
    · next heq => exact absurd (heq ▸ mem_root a cs) h
    · congr 1
      suffices ∀ (l : List (OrdTree α)),
          (∀ c ∈ l, insertLeaf c parent x pos = c) →
          l.map (fun c => insertLeaf c parent x pos) = l from
        this cs (fun c hc => insertLeaf_of_not_mem (fun hp => h (mem_child hc hp)))
      intro l hl
      induction l with
      | nil => rfl
      | cons d rest ih =>
        rw [List.map_cons, hl d (List.mem_cons_self ..)]
        congr 1
        exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
termination_by t

/-! ## IL-1: Membership preservation -/

/-- Existing members are preserved by insertLeaf. -/
theorem mem_insertLeaf [DecidableEq α] {t : OrdTree α}
    {parent x y : α} {pos : Nat} (hy : y ∈ t) :
    y ∈ insertLeaf t parent x pos := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node]
    split
    · -- a = parent: children list gets insertIdx
      rw [mem_node_iff] at hy ⊢
      rcases hy with rfl | ⟨c, hc, hyc⟩
      · left; rfl
      · right; exact ⟨c, List.subset_insertIdx cs pos (.node x []) hc, hyc⟩
    · -- a ≠ parent: recurse through children
      rw [mem_node_iff] at hy ⊢
      rcases hy with rfl | ⟨c, hc, hyc⟩
      · left; rfl
      · right
        exact ⟨insertLeaf c parent x pos,
          List.mem_map_of_mem (f := fun c => insertLeaf c parent x pos) hc,
          mem_insertLeaf hyc⟩
termination_by t

/-! ## IL-2: New element membership -/

/-- numChildren is 0 when the parent label is not in the tree. -/
theorem numChildren_eq_zero_of_not_mem [DecidableEq α]
    {parent : α} {t : OrdTree α} (h : parent ∉ t) :
    numChildren parent t = 0 := by
  match t with
  | .node a cs =>
    simp only [numChildren_node]
    split
    · next heq => exact absurd (heq ▸ mem_root a cs) h
    · -- foldl over children, each giving 0
      suffices ∀ c ∈ cs, numChildren parent c = 0 by
        clear h
        induction cs with
        | nil => rfl
        | cons d rest ih =>
          simp only [List.foldl_cons]
          rw [this d (List.mem_cons_self ..)]
          exact ih (fun c hc => this c (List.mem_cons_of_mem _ hc))
      intro c hc
      exact numChildren_eq_zero_of_not_mem (fun hm => h (mem_child hc hm))
termination_by t

-- The foldl proof is left as sorry. The key insight is that in a Distinct
-- tree, `parent` appears in exactly one child, so all other children
-- contribute 0 to the sum. This makes the foldl equal to numChildren parent c.

/-- In a distinct tree, if parent is in child c but not others,
    then numChildren parent (node a cs) = numChildren parent c. -/
theorem numChildren_eq_of_distinct [DecidableEq α]
    {parent a : α} {cs : List (OrdTree α)} {c : OrdTree α}
    (hd : (node a cs).Distinct) (hne : a ≠ parent)
    (hc : c ∈ cs) (hp : parent ∈ c) :
    numChildren parent (.node a cs) = numChildren parent c := by
  simp only [numChildren_node, if_neg hne]
  have hnd : (cs.flatMap fun c => c.toList).Nodup := by
    unfold Distinct at hd; rw [toList_node] at hd; exact (List.nodup_cons.mp hd).2
  -- Prove: foldl of numChildren over cs equals numChildren parent c
  -- by induction on a generalized list, using pairwise disjointness from Nodup
  suffices ∀ (l : List (OrdTree α)),
      (l.flatMap fun c => c.toList).Nodup →
      c ∈ l →
      l.foldl (fun acc x => acc + numChildren parent x) 0 = numChildren parent c from
    this cs hnd hc
  intro l
  induction l with
  | nil => intro _ hc'; exact absurd hc' List.not_mem_nil
  | cons d rest ih =>
    intro hnd_l hc_l
    simp only [List.foldl_cons, Nat.zero_add]
    have ⟨_, hpw_l⟩ := List.nodup_flatMap.mp hnd_l
    have hpw_hd := (List.pairwise_cons.mp hpw_l).1
    have hnd_rest : (rest.flatMap fun c => c.toList).Nodup :=
      List.nodup_flatMap.mpr
        ⟨fun c hc => (List.nodup_flatMap.mp hnd_l).1 c (List.mem_cons_of_mem _ hc),
         (List.pairwise_cons.mp hpw_l).2⟩
    by_cases hpd : parent ∈ d
    · rcases List.mem_cons.mp hc_l with rfl | hc_rest
      · -- d = c: all rest elements contribute 0 (by pairwise disjointness)
        suffices ∀ (l : List (OrdTree α)),
            (∀ e ∈ l, parent ∉ e) →
            ∀ init, l.foldl (fun acc x => acc + numChildren parent x) init = init from
          this rest (fun e he hpe => hpw_hd e he hpd hpe) _
        intro l' hl' init
        induction l' generalizing init with
        | nil => rfl
        | cons e rest' ih' =>
          simp only [List.foldl_cons,
            numChildren_eq_zero_of_not_mem (hl' e (List.mem_cons_self ..)), Nat.add_zero]
          exact ih' (fun e' he' => hl' e' (List.mem_cons_of_mem _ he')) init
      · -- c ∈ rest but parent ∈ d: contradicts pairwise disjointness
        exact absurd hp (hpw_hd c hc_rest hpd)
    · rw [numChildren_eq_zero_of_not_mem hpd]
      rcases List.mem_cons.mp hc_l with rfl | hc_rest
      · exact absurd hp hpd
      · exact ih hnd_rest hc_rest

/-- The newly inserted element is a member of the resulting tree,
    provided the parent exists, pos is valid, and the tree is distinct. -/
theorem mem_insertLeaf_new [DecidableEq α] {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hp : parent ∈ t) (hpos : pos ≤ numChildren parent t) :
    x ∈ insertLeaf t parent x pos := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node]
    split
    · next h =>
      -- a = parent
      rw [mem_node_iff]; right
      subst h
      simp only [numChildren_node] at hpos
      simp only [ite_true] at hpos
      refine ⟨.node x [], ?_, mem_root x []⟩
      rw [List.mem_insertIdx (by omega)]
      left; rfl
    · next h =>
      -- a ≠ parent: parent must be in some child
      rw [mem_node_iff]; right
      rw [mem_node_iff] at hp
      rcases hp with rfl | ⟨c, hc, hpc⟩
      · exact absurd rfl h
      · have hpos_c : pos ≤ numChildren parent c := by
          rw [numChildren_eq_of_distinct hd h hc hpc] at hpos
          exact hpos
        exact ⟨insertLeaf c parent x pos,
          List.mem_map_of_mem (f := fun c => insertLeaf c parent x pos) hc,
          mem_insertLeaf_new (distinct_of_child hd hc) hpc hpos_c⟩
termination_by t

/-! ## IL-3: DFS decomposition (central technical lemma) -/

/-- The DFS of `insertLeaf t parent x pos` equals the old DFS with `x`
    inserted at some position `k`. -/
theorem toList_insertLeaf [DecidableEq α] {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hp : parent ∈ t) (hx : x ∉ t)
    (hpos : pos ≤ numChildren parent t) :
    ∃ k, k ≤ t.toList.length ∧
      (insertLeaf t parent x pos).toList = t.toList.insertIdx k x := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node]
    split
    · -- Case: a = parent
      next h =>
      subst h
      simp only [numChildren_node] at hpos
      simp only [ite_true] at hpos
      rw [toList_node, toList_node]
      -- Decompose flatMap over insertIdx
      have hfm : (cs.insertIdx pos (.node x ([] : List (OrdTree α)))).flatMap
          (fun c => c.toList) =
          (cs.take pos).flatMap (fun c => c.toList) ++ [x] ++
          (cs.drop pos).flatMap (fun c => c.toList) := by
        rw [list_insertIdx_eq_take_cons_drop hpos]
        simp [List.flatMap_append, List.flatMap_cons, toList_node]
      set pfx := (cs.take pos).flatMap fun c => c.toList
      set sfx := (cs.drop pos).flatMap fun c => c.toList
      have hcat : cs.flatMap (fun c => c.toList) = pfx ++ sfx := by
        rw [← List.flatMap_append]
        congr 1
        exact (List.take_append_drop pos cs).symm
      refine ⟨1 + pfx.length, ?_, ?_⟩
      · -- k ≤ length
        rw [List.length_cons, hcat, List.length_append]
        omega
      · -- equality
        rw [hfm, hcat]
        rw [show (1 + pfx.length) = pfx.length + 1 from by omega]
        rw [List.insertIdx_succ_cons]
        congr 1
        rw [list_insertIdx_eq_take_cons_drop
          (show pfx.length ≤ (pfx ++ sfx).length from by
            rw [List.length_append]; omega)]
        simp [List.take_append_of_le_length (Nat.le_refl _),
              List.drop_append_of_le_length (Nat.le_refl _)]
    · -- Case: a ≠ parent
      next h =>
      rw [mem_node_iff] at hp
      rcases hp with rfl | ⟨c, hc, hpc⟩
      · exact absurd rfl h
      · have hd_c := distinct_of_child hd hc
        have hx_c : x ∉ c := fun hxc => hx (mem_child hc hxc)
        have hpos_c : pos ≤ numChildren parent c := by
          rw [numChildren_eq_of_distinct hd h hc hpc] at hpos
          exact hpos
        obtain ⟨k, hk_le, hk_eq⟩ := toList_insertLeaf hd_c hpc hx_c hpos_c
        rw [toList_node, toList_node]
        -- Decompose cs at c's position
        obtain ⟨cs₁, cs₂, hcs_eq⟩ := List.append_of_mem hc
        subst hcs_eq
        -- Extract pairwise disjointness from Distinct
        have hfm_nd : ((cs₁ ++ c :: cs₂).flatMap fun c => c.toList).Nodup := by
          unfold Distinct at hd; rw [toList_node] at hd; exact (List.nodup_cons.mp hd).2
        have hpw := (List.nodup_flatMap.mp hfm_nd).2
        have hpw_app := List.pairwise_append.mp hpw
        -- parent ∉ c' for elements of cs₁ and cs₂
        have hno₁ : ∀ c' ∈ cs₁, parent ∉ c' :=
          fun c' hc' hp' => (hpw_app.2.2 c' hc' c (List.mem_cons_self ..)) hp' hpc
        have hno₂ : ∀ c' ∈ cs₂, parent ∉ c' :=
          fun c' hc' => ((List.pairwise_cons.mp hpw_app.2.1).1 c' hc') hpc
        -- map insertLeaf preserves sublists where parent is absent
        have map_id : ∀ (l : List (OrdTree α)),
            (∀ c' ∈ l, parent ∉ c') →
            l.map (fun c' => insertLeaf c' parent x pos) = l := by
          intro l hl; induction l with
          | nil => rfl
          | cons d rest ih =>
            rw [List.map_cons, insertLeaf_of_not_mem (hl d (List.mem_cons_self ..))]
            congr 1; exact ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
        -- Set up abbreviations
        set A := cs₁.flatMap (fun c => c.toList) with hA_def
        set B := c.toList with hB_def
        set C := cs₂.flatMap (fun c => c.toList) with hC_def
        -- Compute the modified flatMap
        have hmod : ((cs₁ ++ c :: cs₂).map (fun c' => insertLeaf c' parent x pos)).flatMap
            (fun c => c.toList) = A ++ B.insertIdx k x ++ C := by
          rw [List.map_append, List.map_cons, map_id cs₁ hno₁, map_id cs₂ hno₂]
          simp only [List.flatMap_append, List.flatMap_cons, hk_eq,
            ← hA_def, ← hC_def, List.append_assoc]
        -- Compute the original flatMap
        have horig : (cs₁ ++ c :: cs₂).flatMap (fun c => c.toList) = A ++ B ++ C := by
          simp only [List.flatMap_append, List.flatMap_cons,
            ← hA_def, ← hB_def, ← hC_def, List.append_assoc]
        -- Helper: insertIdx distributes over A ++ B ++ C
        have ins_mid : ∀ (A' B' C' : List α) (k' : Nat) (x' : α),
            k' ≤ B'.length →
            (A' ++ B' ++ C').insertIdx (A'.length + k') x' =
              A' ++ B'.insertIdx k' x' ++ C' := by
          intro A'
          induction A' with
          | nil =>
            intro B' C' k' x' hk'
            simp only [List.nil_append, List.length_nil, Nat.zero_add]
            rw [list_insertIdx_eq_take_cons_drop (show k' ≤ (B' ++ C').length from by
                rw [List.length_append]; omega),
              List.take_append_of_le_length hk',
              List.drop_append_of_le_length hk',
              list_insertIdx_eq_take_cons_drop hk']
            simp [List.append_assoc]
          | cons a' A'' ih =>
            intro B' C' k' x' hk'
            simp only [List.cons_append, List.length_cons]
            rw [show A''.length + 1 + k' = (A''.length + k') + 1 from by omega,
                List.insertIdx_succ_cons]
            congr 1
            exact ih B' C' k' x' hk'
        -- Provide the witness k' = 1 + A.length + k
        refine ⟨1 + A.length + k, ?_, ?_⟩
        · -- k' ≤ length
          rw [List.length_cons, horig, List.length_append, List.length_append]
          omega
        · -- equality
          rw [hmod, horig,
              show 1 + A.length + k = (A.length + k) + 1 from by omega,
              List.insertIdx_succ_cons]
          congr 1
          exact (ins_mid A B C k x hk_le).symm
termination_by t

/-! ## IL-4: Distinct preservation -/

/-- Inserting into a Nodup list at a valid position preserves Nodup,
    provided the element is not already in the list. -/
theorem List.nodup_insertIdx {l : List α} {x : α} {k : Nat}
    (hnd : l.Nodup) (hx : x ∉ l) (hk : k ≤ l.length) :
    (l.insertIdx k x).Nodup := by
  rw [list_insertIdx_eq_take_cons_drop hk]
  rw [List.nodup_append]
  refine ⟨hnd.sublist (List.take_sublist k l),
    List.nodup_cons.mpr ⟨fun hm => hx (List.mem_of_mem_drop hm),
      hnd.sublist (List.drop_sublist k l)⟩,
    fun a ha b hb hab => ?_⟩
  subst hab
  rcases List.mem_cons.mp hb with rfl | hbd
  · exact hx (List.mem_of_mem_take ha)
  · -- a ∈ take k l, a ∈ drop k l, contradicts Nodup
    exact hnd.rel_of_mem_take_of_mem_drop ha hbd rfl

/-- Inserting a fresh leaf preserves Distinct. -/
theorem distinct_insertLeaf [DecidableEq α] {t : OrdTree α}
    {parent x : α} {pos : Nat}
    (hd : t.Distinct) (hx : x ∉ t)
    (hp : parent ∈ t) (hpos : pos ≤ numChildren parent t) :
    (insertLeaf t parent x pos).Distinct := by
  obtain ⟨k, hk_le, hk_eq⟩ := toList_insertLeaf hd hp hx hpos
  unfold Distinct
  rw [hk_eq]
  exact List.nodup_insertIdx hd (fun h => hx h) hk_le

end OrdTree

end OTProof

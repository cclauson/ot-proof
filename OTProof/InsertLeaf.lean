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

/-! ## IL-5: Membership in insertLeaf -/

/-- Any member of `insertLeaf t parent x pos` is either `x` or was already in `t`. -/
theorem mem_of_mem_insertLeaf [DecidableEq α] {t : OrdTree α}
    {parent x y : α} {pos : Nat} (h : y ∈ insertLeaf t parent x pos) :
    y ∈ t ∨ y = x := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node] at h
    split at h
    · -- a = parent: children = cs.insertIdx pos (node x [])
      rw [mem_node_iff] at h
      rcases h with rfl | ⟨c, hc, hyc⟩
      · left; exact mem_root _ cs
      · rcases List.eq_or_mem_of_mem_insertIdx hc with rfl | hc'
        · -- c = node x []
          rw [mem_node_iff] at hyc
          rcases hyc with rfl | ⟨_, hd, _⟩
          · right; rfl
          · simp at hd
        · left; exact mem_child hc' hyc
    · -- a ≠ parent: children mapped
      rw [mem_node_iff] at h
      rcases h with rfl | ⟨c, hc, hyc⟩
      · left; exact mem_root _ cs
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        rcases mem_of_mem_insertLeaf hyc with h | h
        · left; exact mem_child hc' h
        · right; exact h
termination_by t

/-! ## IL-6: numChildren monotonicity under insertLeaf -/

/-- foldl of addition is monotone in the initial value. -/
private theorem foldl_add_mono {γ : Type*} (f : γ → Nat) (l : List γ)
    {i j : Nat} (h : i ≤ j) :
    l.foldl (fun acc c => acc + f c) i ≤ l.foldl (fun acc c => acc + f c) j := by
  induction l generalizing i j with
  | nil => exact h
  | cons a l ih => exact ih (Nat.add_le_add_right h (f a))

/-- foldl of addition over insertIdx is ≥ the original foldl. -/
private theorem foldl_add_le_insertIdx {γ : Type*} (f : γ → Nat) (l : List γ)
    (k : Nat) (v : γ) (init : Nat) :
    l.foldl (fun acc c => acc + f c) init ≤
      (l.insertIdx k v).foldl (fun acc c => acc + f c) init := by
  induction l generalizing k init with
  | nil =>
    cases k with
    | zero => simp only [List.insertIdx_zero, List.foldl_cons, List.foldl_nil]; omega
    | succ n => simp only [List.insertIdx_succ_nil]; exact Nat.le_refl _
  | cons a l ih =>
    cases k with
    | zero =>
      simp only [List.insertIdx_zero, List.foldl_cons]
      exact foldl_add_mono f l (by omega : init + f a ≤ init + f v + f a)
    | succ n =>
      simp only [List.insertIdx_succ_cons, List.foldl_cons]
      exact ih n (init + f a)

/-- foldl of addition is monotone when each mapped value is ≥ the original. -/
private theorem foldl_add_map_le {γ : Type*} (f : γ → Nat) (g : γ → γ)
    (hfg : ∀ b, f b ≤ f (g b)) (l : List γ) (init : Nat) :
    l.foldl (fun acc c => acc + f c) init ≤
      (l.map g).foldl (fun acc c => acc + f c) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact Nat.le_trans (ih (init + f a))
      (foldl_add_mono f (l.map g) (Nat.add_le_add_left (hfg a) init))

/-- numChildren is monotone under insertLeaf. -/
theorem numChildren_le_insertLeaf [DecidableEq α] (qp : α) (t : OrdTree α)
    (parent x : α) (pos : Nat) :
    numChildren qp t ≤ numChildren qp (insertLeaf t parent x pos) := by
  match t with
  | .node a cs =>
    simp only [insertLeaf_node]
    by_cases hap : a = parent
    · subst hap
      simp only [ite_true, numChildren_node]
      by_cases haq : a = qp
      · subst haq; simp only [ite_true, List.length_insertIdx]
        by_cases h : pos ≤ cs.length <;> simp [h] <;> omega
      · simp only [if_neg haq]
        exact foldl_add_le_insertIdx (numChildren qp) cs pos (node x []) 0
    · simp only [if_neg hap, numChildren_node]
      by_cases haq : a = qp
      · subst haq; simp [ite_true, List.length_map]
      · simp only [if_neg haq]
        -- Per-child proof (tree recursion)
        have key : ∀ c ∈ cs,
            numChildren qp c ≤ numChildren qp (insertLeaf c parent x pos) :=
          fun c _hc => numChildren_le_insertLeaf qp c parent x pos
        -- Foldl inequality from pointwise inequality (list induction only)
        suffices ∀ (l : List (OrdTree α)),
            (∀ c ∈ l, numChildren qp c ≤ numChildren qp (insertLeaf c parent x pos)) →
            ∀ (init : Nat),
            l.foldl (fun acc c => acc + numChildren qp c) init ≤
              (l.map (fun c => insertLeaf c parent x pos)).foldl
                (fun acc c => acc + numChildren qp c) init from
          this cs key 0
        intro l
        induction l with
        | nil => intro _ init; exact Nat.le_refl _
        | cons d rest ih =>
          intro hl init
          simp only [List.map_cons, List.foldl_cons]
          exact Nat.le_trans
            (ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) (init + numChildren qp d))
            (foldl_add_mono (numChildren qp)
              (rest.map (fun c => insertLeaf c parent x pos))
              (Nat.add_le_add_left (hl d (List.mem_cons_self ..)) init))
termination_by t

/-- A fresh element not equal to the inserted element stays absent. -/
theorem not_mem_insertLeaf_fresh [DecidableEq α] {t : OrdTree α}
    {parent x y : α} {pos : Nat} (hy : y ∉ t) (hyx : y ≠ x) :
    y ∉ insertLeaf t parent x pos :=
  fun h => (mem_of_mem_insertLeaf h).elim hy hyx

/-! ## applyInsert: position-from-tiebreaker insertion -/

/-- Root label of a tree. -/
def rootLabel : OrdTree α → α
  | .node a _ => a

@[simp] theorem rootLabel_node (a : α) (cs : List (OrdTree α)) :
    rootLabel (.node a cs) = a := rfl

/-- Insert a new leaf `x` as a child of `parent`, with sibling position
    determined by the tiebreaker ordering `lt`.  `lt c x = true` means
    child `c` precedes `x` among siblings. -/
def applyInsert [DecidableEq α] (lt : α → α → Bool)
    (parent x : α) : OrdTree α → OrdTree α
  | .node a cs =>
    if a = parent then
      .node a (cs.insertIdx (cs.countP (fun c => lt c.rootLabel x)) (.node x []))
    else .node a (cs.map (applyInsert lt parent x))

@[simp] theorem applyInsert_node [DecidableEq α] (lt : α → α → Bool)
    (parent x a : α) (cs : List (OrdTree α)) :
    applyInsert lt parent x (.node a cs) =
      if a = parent then
        .node a (cs.insertIdx (cs.countP (fun c => lt c.rootLabel x)) (.node x []))
      else .node a (cs.map (applyInsert lt parent x)) := by
  conv_lhs => unfold applyInsert

/-- If parent is not in the tree, applyInsert returns the tree unchanged. -/
@[simp] theorem applyInsert_of_not_mem [DecidableEq α] {lt : α → α → Bool}
    {parent x : α} {t : OrdTree α} (h : parent ∉ t) :
    applyInsert lt parent x t = t := by
  match t with
  | .node a cs =>
    have hne : a ≠ parent := fun heq => h (heq ▸ mem_root a cs)
    simp only [applyInsert_node, if_neg hne]
    congr 1
    have key : ∀ c ∈ cs, applyInsert lt parent x c = c :=
      fun c hc => applyInsert_of_not_mem (fun hp => h (mem_child hc hp))
    suffices ∀ (l : List (OrdTree α)),
        (∀ c ∈ l, applyInsert lt parent x c = c) →
        l.map (applyInsert lt parent x) = l from this cs key
    intro l hl
    induction l with
    | nil => rfl
    | cons d rest ih =>
      rw [List.map_cons, hl d (List.mem_cons_self ..)]
      congr 1
      exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
termination_by t

/-- `applyInsert` equals `insertLeaf` for some position ≤ numChildren. -/
theorem applyInsert_eq_insertLeaf [DecidableEq α] (lt : α → α → Bool)
    (parent x : α) (t : OrdTree α) (hd : t.Distinct) (hp : parent ∈ t) :
    ∃ pos, pos ≤ numChildren parent t ∧
      applyInsert lt parent x t = insertLeaf t parent x pos := by
  match t with
  | .node a cs =>
    by_cases hap : a = parent
    · subst hap
      exact ⟨cs.countP (fun c => lt c.rootLabel x),
        by simp [numChildren_node, List.countP_le_length],
        by simp [applyInsert_node, insertLeaf_node]⟩
    · -- Parent is in exactly one child
      have hp' : ∃ c ∈ cs, parent ∈ c := by
        rw [mem_node_iff] at hp
        rcases hp with rfl | h
        · exact absurd rfl hap
        · exact h
      obtain ⟨ci, hci, hpci⟩ := hp'
      have hd_ci := distinct_of_child hd hci
      obtain ⟨pos, hpos_le, hpos_eq⟩ :=
        applyInsert_eq_insertLeaf lt parent x ci hd_ci hpci
      refine ⟨pos, ?_, ?_⟩
      · -- pos ≤ numChildren parent (node a cs)
        simp only [numChildren_node, if_neg hap]
        suffices h : numChildren parent ci ≤
            cs.foldl (fun acc c => acc + numChildren parent c) 0 from
          Nat.le_trans hpos_le h
        suffices ∀ (l : List (OrdTree α)) (c : OrdTree α) (init : Nat),
            c ∈ l → numChildren parent c ≤
              l.foldl (fun acc c => acc + numChildren parent c) init from
          this cs ci 0 hci
        intro l; induction l with
        | nil => intro c _ hc; simp at hc
        | cons d rest ih =>
          intro c init hc
          simp only [List.foldl_cons]
          rcases List.mem_cons.mp hc with rfl | hc'
          · have : init + numChildren parent c ≤
                rest.foldl (fun acc c => acc + numChildren parent c)
                  (init + numChildren parent c) := by
              suffices ∀ (l : List (OrdTree α)) (v : Nat),
                  v ≤ l.foldl (fun acc c => acc + numChildren parent c) v from
                this rest _
              intro l; induction l with
              | nil => intro v; exact Nat.le_refl _
              | cons e l' ih' => intro v; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_add_right ..) (ih' _)
            omega
          · exact ih c _ hc'
      · -- Both maps agree
        simp only [applyInsert_node, if_neg hap, insertLeaf_node, if_neg hap]
        congr 1
        have huniq : ∀ c' ∈ cs, c' ≠ ci → parent ∉ c' := by
          intro c' hc' hne hpc'
          exact hne (mem_unique_child hd hc' hci hpc' hpci)
        suffices ∀ (l : List (OrdTree α)),
            (∀ c ∈ l, c ≠ ci → parent ∉ c) →
            l.map (applyInsert lt parent x) =
              l.map (fun c => insertLeaf c parent x pos) from
          this cs huniq
        intro l; induction l with
        | nil => intros; rfl
        | cons d rest ih =>
          intro huniq'
          rw [List.map_cons, List.map_cons]
          congr 1
          · by_cases hd_eq : d = ci
            · exact hd_eq ▸ hpos_eq
            · rw [applyInsert_of_not_mem (huniq' d (List.mem_cons_self ..) hd_eq),
                   insertLeaf_of_not_mem (huniq' d (List.mem_cons_self ..) hd_eq)]
          · exact ih (fun c hc => huniq' c (List.mem_cons_of_mem _ hc))
termination_by t

/-! ## Helpers for applyInsert commutativity -/

/-- `applyInsert` preserves the root label. -/
@[simp] theorem rootLabel_applyInsert [DecidableEq α] (lt : α → α → Bool)
    (parent x : α) (t : OrdTree α) :
    (applyInsert lt parent x t).rootLabel = t.rootLabel := by
  cases t with | node a cs => simp [applyInsert_node]; split <;> rfl

/-- `countP` over `insertIdx` equals `countP` plus the predicate on the new element. -/
private theorem countP_insertIdx {α' : Type*} {p : α' → Bool} {l : List α'}
    {k : Nat} {v : α'} (hk : k ≤ l.length) :
    (l.insertIdx k v).countP p = l.countP p + if p v then 1 else 0 := by
  induction l generalizing k with
  | nil => simp at hk; subst hk; simp [List.insertIdx_zero]
  | cons a l ih =>
    cases k with
    | zero =>
      simp [List.insertIdx_zero, List.countP_cons]
    | succ n =>
      simp only [List.insertIdx_succ_cons, List.countP_cons]
      rw [ih (Nat.le_of_succ_le_succ hk)]
      omega

/-- `countP` is monotone under pointwise implication. -/
private theorem countP_le_countP_of_imp {α' : Type*} {p q : α' → Bool} {l : List α'}
    (h : ∀ x ∈ l, p x = true → q x = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : p a = true
    · rw [hp, h a (List.mem_cons_self ..) hp]; omega
    · simp only [Bool.not_eq_true] at hp; rw [hp]; simp; omega

/-- `applyInsert` on a leaf that doesn't contain the parent is identity. -/
private theorem applyInsert_leaf_ne [DecidableEq α] (lt : α → α → Bool)
    {parent x a : α} (hne : a ≠ parent) :
    applyInsert lt parent x (.node a []) = .node a [] := by
  simp [applyInsert_node, if_neg hne]

/-! ## applyInsert commutativity -/

/-- Two `applyInsert` operations on distinct fresh elements commute.
    Requires `lt_sib` to be transitive and total on `{a, b}`. -/
theorem applyInsert_comm [DecidableEq α] (lt_sib : α → α → Bool)
    {t : OrdTree α} {pa pb a b : α}
    (hd : t.Distinct) (ha : a ∉ t) (hb : b ∉ t) (hab : a ≠ b)
    (hpa : pa ∈ t) (hpb : pb ∈ t)
    (hlt_trans : ∀ x y z, lt_sib x y = true → lt_sib y z = true → lt_sib x z = true)
    (hlt_total_ab : lt_sib a b = true ∨ lt_sib b a = true)
    (hlt_asym_ab : lt_sib a b = true → lt_sib b a = false) :
    applyInsert lt_sib pa a (applyInsert lt_sib pb b t) =
    applyInsert lt_sib pb b (applyInsert lt_sib pa a t) := by
  -- Helper: members of applyInsert are either original or inserted element
  have mem_ai : ∀ {lt' : α → α → Bool} {p x y : α} {s : OrdTree α},
      s.Distinct → p ∈ s → y ∈ applyInsert lt' p x s → y ∈ s ∨ y = x := by
    intro lt' p x y s hds hps hy
    obtain ⟨pos, _, hpos_eq⟩ := applyInsert_eq_insertLeaf lt' p x s hds hps
    rw [hpos_eq] at hy; exact mem_of_mem_insertLeaf hy
  match t with
  | .node r cs =>
    by_cases hpa_r : r = pa <;> by_cases hpb_r : r = pb
    · -- Case 1: r = pa = pb (same parent)
      subst hpa_r; subst hpb_r
      simp only [applyInsert_node, ite_true]
      congr 1
      set cp_a := cs.countP (fun c => lt_sib c.rootLabel a)
      set cp_b := cs.countP (fun c => lt_sib c.rootLabel b)
      -- Adjusted countP after inserting the other leaf
      have hcp_a' : (cs.insertIdx cp_b (.node b [])).countP
            (fun c => lt_sib c.rootLabel a) =
          cp_a + if lt_sib b a then 1 else 0 :=
        countP_insertIdx (List.countP_le_length)
      have hcp_b' : (cs.insertIdx cp_a (.node a [])).countP
            (fun c => lt_sib c.rootLabel b) =
          cp_b + if lt_sib a b then 1 else 0 :=
        countP_insertIdx (List.countP_le_length)
      rw [hcp_a', hcp_b']
      rcases hlt_total_ab with hab_lt | hba_lt
      · -- lt_sib a b = true
        simp only [hab_lt, hlt_asym_ab hab_lt, ite_true, ite_false]
        exact (List.insertIdx_comm (OrdTree.node a []) (OrdTree.node b [])
          (countP_le_countP_of_imp fun c _ hc => hlt_trans c.rootLabel a b hc hab_lt)
          List.countP_le_length).symm
      · -- lt_sib b a = true
        have hab_f : lt_sib a b = false := by
          cases h : lt_sib a b <;> [rfl; simp [hlt_asym_ab h] at hba_lt]
        simp only [hba_lt, hab_f, ite_true, ite_false]
        exact List.insertIdx_comm (OrdTree.node b []) (OrdTree.node a [])
          (countP_le_countP_of_imp fun c _ hc => hlt_trans c.rootLabel b a hc hba_lt)
          List.countP_le_length
    · -- Case 2: r = pa, r ≠ pb
      subst hpa_r
      simp only [applyInsert_node, ite_true, if_neg hpb_r]
      congr 1
      -- countP preserved since applyInsert preserves rootLabel
      suffices hcp_eq : (cs.map (applyInsert lt_sib pb b)).countP
            (fun c => lt_sib c.rootLabel a) =
          cs.countP (fun c => lt_sib c.rootLabel a) by
        rw [hcp_eq, List.map_insertIdx]; congr 1
        exact (applyInsert_leaf_ne lt_sib
          (show a ≠ pb from fun h => ha (h ▸ hpb))).symm
      suffices ∀ (l : List (OrdTree α)),
          (l.map (applyInsert lt_sib pb b)).countP (fun c => lt_sib c.rootLabel a) =
          l.countP (fun c => lt_sib c.rootLabel a) from this cs
      intro l; induction l with
      | nil => simp
      | cons d rest ih =>
        simp only [List.map_cons, List.countP_cons, rootLabel_applyInsert, ih]
    · -- Case 3: r ≠ pa, r = pb
      subst hpb_r
      simp only [applyInsert_node, ite_true, if_neg hpa_r]
      congr 1
      suffices hcp_eq : (cs.map (applyInsert lt_sib pa a)).countP
            (fun c => lt_sib c.rootLabel b) =
          cs.countP (fun c => lt_sib c.rootLabel b) by
        rw [hcp_eq, List.map_insertIdx]; congr 1
        exact applyInsert_leaf_ne lt_sib
          (show b ≠ pa from fun h => hb (h ▸ hpa))
      suffices ∀ (l : List (OrdTree α)),
          (l.map (applyInsert lt_sib pa a)).countP (fun c => lt_sib c.rootLabel b) =
          l.countP (fun c => lt_sib c.rootLabel b) from this cs
      intro l; induction l with
      | nil => simp
      | cons d rest ih =>
        simp only [List.map_cons, List.countP_cons, rootLabel_applyInsert, ih]
    · -- Case 4: r ≠ pa, r ≠ pb (both recurse)
      simp only [applyInsert_node, if_neg hpa_r, if_neg hpb_r, List.map_map]
      congr 1
      -- Pointwise equality of composed maps
      suffices hfn : ∀ c ∈ cs,
          applyInsert lt_sib pa a (applyInsert lt_sib pb b c) =
          applyInsert lt_sib pb b (applyInsert lt_sib pa a c) by
        suffices ∀ {f g : OrdTree α → OrdTree α} (l : List (OrdTree α)),
            (∀ c ∈ l, f c = g c) → l.map f = l.map g from this cs hfn
        intro f g l hl; induction l with
        | nil => rfl
        | cons d rest ih =>
          simp only [List.map_cons]; congr 1
          · exact hl d (List.mem_cons_self ..)
          · exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
      intro c hc
      have hd_c := distinct_of_child hd hc
      have ha_c : a ∉ c := fun h => ha (mem_child hc h)
      have hb_c : b ∉ c := fun h => hb (mem_child hc h)
      by_cases hpa_c : pa ∈ c <;> by_cases hpb_c : pb ∈ c
      · exact applyInsert_comm lt_sib hd_c ha_c hb_c hab hpa_c hpb_c
          hlt_trans hlt_total_ab hlt_asym_ab
      · -- pa ∈ c, pb ∉ c
        have : pb ∉ applyInsert lt_sib pa a c := by
          intro hmem; rcases mem_ai hd_c hpa_c hmem with h | h
          · exact hpb_c h
          · exact ha (h ▸ hpb)
        rw [applyInsert_of_not_mem hpb_c, applyInsert_of_not_mem this]
      · -- pa ∉ c, pb ∈ c
        have : pa ∉ applyInsert lt_sib pb b c := by
          intro hmem; rcases mem_ai hd_c hpb_c hmem with h | h
          · exact hpa_c h
          · exact hb (h ▸ hpa)
        rw [applyInsert_of_not_mem hpa_c, applyInsert_of_not_mem this]
      · -- pa ∉ c, pb ∉ c
        conv_lhs => rw [applyInsert_of_not_mem hpb_c, applyInsert_of_not_mem hpa_c]
        conv_rhs => rw [applyInsert_of_not_mem hpa_c, applyInsert_of_not_mem hpb_c]
termination_by t

end OrdTree

end OTProof

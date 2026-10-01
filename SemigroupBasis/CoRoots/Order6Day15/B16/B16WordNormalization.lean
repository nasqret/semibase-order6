import SemigroupBasis.CoRoots.Order6Day15.B16.B16Decomposition

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

def nonsimpleSupport (xs : List Nat) : List Nat :=
  canonicalSupport (xs.filter (fun a => decide (2 ≤ xs.count a)))

theorem mem_nonsimpleSupport (a : Nat) (xs : List Nat) :
    a ∈ nonsimpleSupport xs ↔ a ∈ xs ∧ 2 ≤ xs.count a := by
  rw [nonsimpleSupport, mem_canonicalSupport]
  simp only [List.mem_filter, decide_eq_true_eq]

theorem nonsimpleSupport_sorted (xs : List Nat) :
    List.Pairwise (fun a b : Nat => a < b) (nonsimpleSupport xs) :=
  canonicalSupport_sorted _

theorem single_iff_not_nonsimple (a : Nat) (xs : List Nat) (ha : a ∈ xs) :
    xs.count a = 1 ↔ a ∉ nonsimpleSupport xs := by
  have pos : 0 < xs.count a := Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) ha)
  rw [mem_nonsimpleSupport]
  constructor
  · intro one h; have many := h.2; omega
  · intro absent
    have small : ¬ 2 ≤ xs.count a := fun many => absent ⟨ha,many⟩
    omega

/-- Deterministic algebraic renderer; uniqueness from observation is a separate theorem. -/
def normalizeList (xs : List Nat) : List Nat :=
  let ns := nonsimpleSupport xs
  let cut := splitFront ns xs
  match cut.2 with
  | [] => cut.1
  | _ :: tail => cut.1 ++ (squares ns ++ renderSegments ns (splitGaps ns tail).2)

theorem normalizeList_rel (xs : List Nat) : Rel xs (normalizeList xs) := by
  let ns := nonsimpleSupport xs
  let front := (splitFront ns xs).1
  have split : front ++ (splitFront ns xs).2 = xs := splitFront_join ns xs
  have avoid : ∀ b ∈ ns, b ∉ front := by
    intro b hb hf
    exact splitFront_avoid ns xs b hf hb
  cases eq : (splitFront ns xs).2 with
  | nil =>
      have source : front = xs := by
        rw [eq, List.append_nil] at split
        exact split
      have target : normalizeList xs = front := by
        change (match (splitFront ns xs).2 with
          | [] => front
          | _ :: tail => front ++ (squares ns ++ renderSegments ns (splitGaps ns tail).2)) = front
        rw [eq]
      rw [target, source]
      exact Rel.refl xs
  | cons a tail =>
      let gap := (splitGaps ns tail).1
      let segs := (splitGaps ns tail).2
      have tailEq : gap ++ flattenSegments segs = tail := splitGaps_join ns tail
      have source : xs = front ++ a :: (gap ++ flattenSegments segs) := by
        rw [eq] at split
        exact split.symm.trans (congrArg (fun t => front ++ a :: t) tailEq.symm)
      have target : normalizeList xs = front ++ (squares ns ++ renderSegments ns segs) := by
        change (match (splitFront ns xs).2 with
          | [] => front
          | _ :: tail => front ++ (squares ns ++ renderSegments ns (splitGaps ns tail).2)) = _
        rw [eq]
      have repeated : ∀ b ∈ ns, 2 ≤ (front ++ a :: (gap ++ flattenSegments segs)).count b := by
        intro b hb
        have global : 2 ≤ xs.count b := ((mem_nonsimpleSupport b xs).mp hb).2
        exact source ▸ global
      have headCovered : a ∈ ns := splitFront_head ns xs a tail eq
      have firstCovered : ∀ b ∈ a :: gap, b ∈ ns := by
        intro b hb
        rcases List.mem_cons.mp hb with same | mem
        · subst b; exact headCovered
        · exact splitGaps_first_covered ns tail b mem
      have actual : Rel (front ++ a :: (gap ++ flattenSegments segs))
          (front ++ (squares ns ++ renderSegments ns segs)) :=
        reservoir_then_segments front a gap ns segs avoid repeated firstCovered
          (splitGaps_later_covered ns tail)
      rw [target,source]
      exact actual

theorem normalizeList_all_simple (xs : List Nat) (simple : ∀ a ∈ xs, xs.count a = 1) :
    normalizeList xs = xs := by
  have empty : nonsimpleSupport xs = [] := by
    cases eq : nonsimpleSupport xs with
    | nil => rfl
    | cons a tail =>
        have mem : a ∈ nonsimpleSupport xs := by rw [eq]; exact List.Mem.head _
        have data := (mem_nonsimpleSupport a xs).mp mem
        have one := simple a data.1
        have many := data.2
        omega
  have front : splitFront [] xs = (xs,[]) := by
    clear simple empty
    induction xs with
    | nil => rfl
    | cons a xs ih =>
        rw [splitFront, if_neg (List.not_mem_nil (a := a)), ih]
  unfold normalizeList
  rw [empty]
  change (match (splitFront [] xs).2 with
    | [] => (splitFront [] xs).1
    | _ :: tail => (splitFront [] xs).1 ++
        (squares [] ++ renderSegments [] (splitGaps [] tail).2)) = xs
  rw [front]

theorem normalizeList_nonempty (xs : List Nat) (nonempty : xs ≠ []) :
    normalizeList xs ≠ [] := by
  intro empty
  have relation := normalizeList_rel xs
  rw [empty] at relation
  cases xs with
  | nil => exact nonempty rfl
  | cons a tail => exact False.elim relation

def normalizeWord (u : Word Nat) : Word Nat :=
  match normalizeList u.toList with
  | [] => u
  | a :: tail => Word.mk a tail

theorem normalizeWord_toList (u : Word Nat) :
    (normalizeWord u).toList = normalizeList u.toList := by
  have nonempty : u.toList ≠ [] := by cases u; intro h; cases h
  cases eq : normalizeList u.toList with
  | nil => exact False.elim (normalizeList_nonempty u.toList nonempty eq)
  | cons a tail =>
      unfold normalizeWord
      rw [eq]
      rfl

/-- Unconditional arbitrary-word reach to the constructed R/G renderer. -/
theorem normalizeWord_derives (u : Word Nat) : Derives basis u (normalizeWord u) := by
  apply Rel.toDerives
  rw [normalizeWord_toList]
  exact normalizeList_rel u.toList

theorem derives_of_normalizeWord_eq (u v : Word Nat)
    (same : normalizeWord u = normalizeWord v) : Derives basis u v := by
  have left := normalizeWord_derives u
  have right := normalizeWord_derives v
  rw [same] at left
  exact left.trans right.symm

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

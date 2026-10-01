import SemigroupBasis.CoRoots.Order6Astra.C8Star
import SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus

namespace SemigroupBasis.CoRoots.Order6Astra.C8StarFrames

open Order6SporadicSection19.Published
open C8Star C8BranchAlgebra C8TailCuts C8CutCalculus C8SemanticKey

theorem chain_split (separator : Word Nat) (before after : List (Word Nat)) (branch : Word Nat) :
    (chain separator (before ++ branch :: after)).toList =
      (chain separator before).toList ++ branch.toList ++ (chain separator after).toList := by
  induction before with
  | nil => simp only [List.nil_append, chain, Word.toList_append]
  | cons first rest ih =>
    simp only [List.cons_append, chain, Word.toList_append, ih, List.append_assoc]

theorem chain_ends (separator : Word Nat) (branches : List (Word Nat)) :
    ∃ leading : List Nat, (chain separator branches).toList = leading ++ separator.toList := by
  induction branches with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨leading, literal⟩ := ih
    refine ⟨separator.toList ++ first.toList ++ leading, ?_⟩
    simp only [chain, Word.toList_append, literal, List.append_assoc]

theorem last_split (letters : List Nat) (nonempty : letters ≠ []) :
    ∃ leading : List Nat, ∃ last : Nat, letters = leading ++ [last] := by
  induction letters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    cases rest with
    | nil => exact ⟨[], first, rfl⟩
    | cons next rest =>
      obtain ⟨leading, last, equal⟩ := ih (List.cons_ne_nil next rest)
      exact ⟨first :: leading, last, congrArg (List.cons first) equal⟩

theorem pairwise_outside (branches before after : List (Word Nat)) (branch : Word Nat)
    (pairwise : branches.Pairwise (fun a b => Disjoint a.toList b.toList))
    (split : branches = before ++ branch :: after) :
    ∀ other ∈ before ++ after, Disjoint branch.toList other.toList := by
  induction before generalizing branches with
  | nil =>
    rw [split] at pairwise
    exact (List.pairwise_cons.mp pairwise).1
  | cons first rest ih =>
    cases branches with
    | nil => cases split
    | cons head tail =>
      obtain ⟨same, splitTail⟩ := List.cons.inj split
      subst head
      have both := List.pairwise_cons.mp pairwise
      have inTail : branch ∈ tail := by
        rw [splitTail]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      intro other member
      rcases List.mem_cons.mp member with equal | later
      · subst other
        exact disjoint_symm (both.1 branch inTail)
      · exact ih tail both.2 splitTail other later

theorem frame_isolated (star : Star) (before after : List (Word Nat)) (branch : Word Nat)
    (split : star.branches = before ++ branch :: after) :
    Disjoint branch.toList
      ((chain (star.root ++ star.root) before).toList ++
        (chain (star.root ++ star.root) after).toList) := by
  have member : branch ∈ star.branches := by
    rw [split]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have outside := pairwise_outside star.branches before after branch star.pairwise split
  intro x hx contrary
  rcases List.mem_append.mp contrary with inBefore | inAfter
  · rcases (mem_chain (star.root ++ star.root) before x).mp inBefore with inRoot | ⟨other, present, inside⟩
    · rw [Word.toList_append, List.mem_append] at inRoot
      exact star.apart branch member x hx (inRoot.elim id id)
    · exact outside other (List.mem_append.mpr (Or.inl present)) x hx inside
  · rcases (mem_chain (star.root ++ star.root) after x).mp inAfter with inRoot | ⟨other, present, inside⟩
    · rw [Word.toList_append, List.mem_append] at inRoot
      exact star.apart branch member x hx (inRoot.elim id id)
    · exact outside other (List.mem_append.mpr (Or.inr present)) x hx inside

theorem count_in_frame (left branch right : List Nat) (x : Nat)
    (inside : x ∈ branch) (isolated : Disjoint branch (left ++ right)) :
    (left ++ branch ++ right).count x = branch.count x := by
  have absentLeft : x ∉ left := fun member => isolated x inside (List.mem_append.mpr (Or.inl member))
  have absentRight : x ∉ right := fun member => isolated x inside (List.mem_append.mpr (Or.inr member))
  simp only [List.count_append, List.count_eq_zero.mpr absentLeft,
    List.count_eq_zero.mpr absentRight, Nat.zero_add, Nat.add_zero]

theorem branch_count (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (x : Nat) (inside : x ∈ branch.toList) : star.word.toList.count x = branch.toList.count x := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [Star.word, split, chain_split]
  exact count_in_frame _ _ _ x inside (frame_isolated star before after branch split)

theorem root_repeated (star : Star) (x : Nat) (inside : x ∈ star.root.toList) :
    2 ≤ star.word.toList.count x := by
  have positive : 1 ≤ star.root.toList.count x := List.one_le_count_iff.mpr inside
  cases branches : star.branches with
  | nil =>
    simp only [Star.word, branches, chain, Word.toList_append, List.count_append]
    omega
  | cons first rest =>
    simp only [Star.word, branches, chain, Word.toList_append, List.count_append]
    omega

theorem simple_in_branch (star : Star) (t : Nat) (simple : star.word.toList.count t = 1) :
    ∃ branch ∈ star.branches, t ∈ branch.toList ∧ branch.toList.count t = 1 := by
  have present : t ∈ star.word.toList := List.one_le_count_iff.mp (by omega)
  rcases (star.support t).mp present with inRoot | ⟨branch, member, inside⟩
  · have repeated := root_repeated star t inRoot
    omega
  · exact ⟨branch, member, inside, (branch_count star branch member t inside).symm.trans simple⟩

/-- Every simple marker's entire tail family lives inside its unique actual
branch. A recurring root letter rules out crossing either neighboring square. -/
theorem branch_tail (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (t : Nat) (inside : t ∈ branch.toList) (simple : branch.toList.count t = 1) (z : List Nat) :
    TailAt star.word.toList t z ↔ TailAt branch.toList t z := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  obtain ⟨p, s, branchSplit⟩ := List.mem_iff_append.mp inside
  let square := star.root ++ star.root
  obtain ⟨rootLeading, barrier, rootSplit⟩ := last_split square.toList
    (by cases square; simp [Word.toList])
  obtain ⟨outerLeading, leftSplit⟩ := chain_ends square before
  let left := outerLeading ++ rootLeading
  let right := (chain square after).toList
  have leftLiteral : (chain square before).toList = left ++ [barrier] := by
    rw [leftSplit, rootSplit, ← List.append_assoc]
  have recurs : barrier ∈ right := by
    apply (mem_chain square after barrier).mpr
    apply Or.inl
    rw [rootSplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have literal : star.word.toList = (left ++ barrier :: p) ++ t :: (s ++ right) := by
    rw [Star.word, split, chain_split]
    change (chain square before).toList ++ branch.toList ++ right = _
    rw [leftLiteral, branchSplit]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have globalSimple : star.word.toList.count t = 1 :=
    (branch_count star branch member t inside).trans simple
  have isolated : Disjoint (p ++ s) (left ++ barrier :: right) := by
    intro x hx contrary
    apply frame_isolated star before after branch split x
    · rw [branchSplit]
      rcases List.mem_append.mp hx with inP | inS
      · exact List.mem_append.mpr (Or.inl inP)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem t inS))
    · change x ∈ (chain square before).toList ++ right
      simpa only [leftLiteral, List.append_assoc, List.singleton_append] using contrary
  rw [tailAt_at_split _ t _ _ z literal globalSimple,
    tailAt_at_split _ t p s z branchSplit simple]
  exact tail_frame left right p s z barrier recurs isolated

end SemigroupBasis.CoRoots.Order6Astra.C8StarFrames

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarFrames.branch_count
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarFrames.simple_in_branch
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarFrames.branch_tail

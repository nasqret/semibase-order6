import SemigroupBasis.Equational
import SemigroupBasis.Nonfinite.GraphParity

/-! Reusable simple-pair syntax extracted unchanged from the already proved
Section15 adjacency development. The formerly private combinatorial lemmas
are public here for the independent transcription of Lee-Zhang Lemma2.10.
No Section15 table or detector law is imported or assumed. -/

namespace SemigroupBasis.CoRoots.SimplePairExclusion

open SemigroupBasis

/-- Send the distinguished letters to the supplied source and target states,
and every other letter to the supplied background state. -/
def directedSimpleAdjacencyValuation
    {S : Type u} {α : Type v} [DecidableEq α]
    (source target : α)
    (sourceState targetState otherState : S) : α → S :=
  fun letter =>
    if letter = source then sourceState
    else if letter = target then targetState
    else otherState

@[simp]
theorem directedSimpleAdjacencyValuation_source
    {S : Type u} {α : Type v} [DecidableEq α]
    (source target : α)
    (sourceState targetState otherState : S) :
    directedSimpleAdjacencyValuation source target
        sourceState targetState otherState source = sourceState := by
  simp [directedSimpleAdjacencyValuation]

theorem directedSimpleAdjacencyValuation_target
    {S : Type u} {α : Type v} [DecidableEq α]
    {source target : α} (different : source ≠ target)
    (sourceState targetState otherState : S) :
    directedSimpleAdjacencyValuation source target
        sourceState targetState otherState target = targetState := by
  simp [directedSimpleAdjacencyValuation, Ne.symm different]

def PairFree
    {α : Type v} (source target : α) (letters : List α) : Prop :=
  source ∉ letters ∧ target ∉ letters

theorem pairFree_symm
    {α : Type v} {source target : α} {letters : List α}
    (free : PairFree source target letters) :
    PairFree target source letters :=
  ⟨free.2, free.1⟩

theorem pairFree_tail
    {α : Type v} {source target first : α} {rest : List α}
    (free : PairFree source target (first :: rest)) :
    PairFree source target rest := by
  exact
    ⟨fun member => free.1 (List.Mem.tail first member),
      fun member => free.2 (List.Mem.tail first member)⟩

theorem directedSimpleAdjacencyValuation_eq_other
    {S : Type u} {α : Type v} [DecidableEq α]
    {source target letter : α} {letters : List α}
    (sourceState targetState otherState : S)
    (free : PairFree source target letters)
    (member : letter ∈ letters) :
    directedSimpleAdjacencyValuation source target
        sourceState targetState otherState letter = otherState := by
  have sourceNe : letter ≠ source := by
    intro equality
    subst letter
    exact free.1 member
  have targetNe : letter ≠ target := by
    intro equality
    subst letter
    exact free.2 member
  simp [directedSimpleAdjacencyValuation, sourceNe, targetNe]

theorem pairFree_parts_of_simple_split
    {α : Type v} [DecidableEq α]
    {first second : α} {before middle after : List α}
    (different : first ≠ second)
    (firstCount :
      (before ++ first :: (middle ++ second :: after)).count first = 1)
    (secondCount :
      (before ++ first :: (middle ++ second :: after)).count second = 1) :
    PairFree first second before ∧
      PairFree first second middle ∧
      PairFree first second after := by
  have firstEquation := firstCount
  simp only [List.count_append, List.count_cons] at firstEquation
  simp [Ne.symm different] at firstEquation
  have firstBeforeZero : before.count first = 0 := by omega
  have firstMiddleZero : middle.count first = 0 := by omega
  have firstAfterZero : after.count first = 0 := by omega
  have secondEquation := secondCount
  simp only [List.count_append, List.count_cons] at secondEquation
  simp [different] at secondEquation
  have secondBeforeZero : before.count second = 0 := by omega
  have secondMiddleZero : middle.count second = 0 := by omega
  have secondAfterZero : after.count second = 0 := by omega
  exact
    ⟨⟨List.count_eq_zero.mp firstBeforeZero,
        List.count_eq_zero.mp secondBeforeZero⟩,
      ⟨⟨List.count_eq_zero.mp firstMiddleZero,
          List.count_eq_zero.mp secondMiddleZero⟩,
        ⟨List.count_eq_zero.mp firstAfterZero,
          List.count_eq_zero.mp secondAfterZero⟩⟩⟩

theorem pairFree_ends_of_adjacent_split
    {α : Type v} [DecidableEq α]
    {source target : α} {before after : List α}
    (different : source ≠ target)
    (sourceCount :
      (before ++ source :: target :: after).count source = 1)
    (targetCount :
      (before ++ source :: target :: after).count target = 1) :
    PairFree source target before ∧ PairFree source target after := by
  have parts :=
    pairFree_parts_of_simple_split
      (before := before) (middle := []) (after := after)
      different (by simpa using sourceCount) (by simpa using targetCount)
  exact ⟨parts.1, parts.2.2⟩

def adjacentPairsList {α : Type v} : List α → List (α × α)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

theorem mem_adjacentPairsList_iff_exists_split
    {α : Type v} [DecidableEq α] (source target : α) :
    ∀ letters : List α,
      (source, target) ∈ adjacentPairsList letters ↔
        ∃ before after,
          letters = before ++ source :: target :: after
  | [] => by
      constructor
      · simp [adjacentPairsList]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | [first] => by
      constructor
      · simp [adjacentPairsList, Word.adjacentPairsFrom]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | first :: second :: rest => by
      change
        (source, target) ∈
              (first, second) :: adjacentPairsList (second :: rest) ↔
          ∃ before after,
            first :: second :: rest =
              before ++ source :: target :: after
      simp only [List.mem_cons, Prod.mk.injEq]
      constructor
      · intro member
        rcases member with firstEdge | laterEdge
        · exact
            ⟨[], rest, by
              rcases firstEdge with ⟨rfl, rfl⟩
              rfl⟩
        · obtain ⟨before, after, split⟩ :=
            (mem_adjacentPairsList_iff_exists_split
              source target (second :: rest)).mp laterEdge
          exact ⟨first :: before, after, by simp [split]⟩
      · rintro ⟨before, after, split⟩
        cases before with
        | nil =>
            simp only [List.nil_append] at split
            injection split with firstEq tailEq
            injection tailEq with secondEq _
            exact Or.inl ⟨firstEq.symm, secondEq.symm⟩
        | cons beforeHead beforeTail =>
            simp only [List.cons_append] at split
            injection split with _ tailSplit
            exact Or.inr <|
              (mem_adjacentPairsList_iff_exists_split
                source target (second :: rest)).mpr
                ⟨beforeTail, after, tailSplit⟩

theorem adjacentPairsList_toList
    {α : Type v} (word : Word α) :
    adjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

theorem mem_adjacentPairs_iff_exists_split
    {α : Type v} [DecidableEq α]
    (source target : α) (word : Word α) :
    (source, target) ∈ word.adjacentPairs ↔
      ∃ before after,
        word.toList = before ++ source :: target :: after := by
  rw [← adjacentPairsList_toList]
  exact
    mem_adjacentPairsList_iff_exists_split
      source target word.toList

theorem simplePair_order_cases
    {α : Type v} [DecidableEq α]
    {source target : α} {letters : List α}
    (different : source ≠ target)
    (sourceCount : letters.count source = 1)
    (targetCount : letters.count target = 1) :
    (∃ before middle after,
      letters = before ++ source :: (middle ++ target :: after)) ∨
    (∃ before middle after,
      letters = before ++ target :: (middle ++ source :: after)) := by
  have sourceMember : source ∈ letters :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨before, after, split⟩ :=
    List.mem_iff_append.mp sourceMember
  have targetMember : target ∈ letters :=
    List.count_pos_iff.mp (by omega)
  rw [split] at targetMember
  simp only [List.mem_append, List.mem_cons] at targetMember
  rcases targetMember with targetBefore | targetAtSource | targetAfter
  · obtain ⟨leading, middle, beforeSplit⟩ :=
      List.mem_iff_append.mp targetBefore
    exact Or.inr
      ⟨leading, middle, after, by
        rw [split, beforeSplit]
        simp [List.append_assoc]⟩
  · exact False.elim (different targetAtSource.symm)
  · obtain ⟨middle, suffix, afterSplit⟩ :=
      List.mem_iff_append.mp targetAfter
    exact Or.inl
      ⟨before, middle, suffix, by
        rw [split, afterSplit]⟩


#print axioms pairFree_parts_of_simple_split
#print axioms mem_adjacentPairs_iff_exists_split
#print axioms simplePair_order_cases

end SemigroupBasis.CoRoots.SimplePairExclusion

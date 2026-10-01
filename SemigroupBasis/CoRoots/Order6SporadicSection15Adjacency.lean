import SemigroupBasis.CoRoots.Order6SporadicSection15
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

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
private theorem directedSimpleAdjacencyValuation_source
    {S : Type u} {α : Type v} [DecidableEq α]
    (source target : α)
    (sourceState targetState otherState : S) :
    directedSimpleAdjacencyValuation source target
        sourceState targetState otherState source = sourceState := by
  simp [directedSimpleAdjacencyValuation]

private theorem directedSimpleAdjacencyValuation_target
    {S : Type u} {α : Type v} [DecidableEq α]
    {source target : α} (different : source ≠ target)
    (sourceState targetState otherState : S) :
    directedSimpleAdjacencyValuation source target
        sourceState targetState otherState target = targetState := by
  simp [directedSimpleAdjacencyValuation, Ne.symm different]

private def PairFree
    {α : Type v} (source target : α) (letters : List α) : Prop :=
  source ∉ letters ∧ target ∉ letters

private theorem pairFree_symm
    {α : Type v} {source target : α} {letters : List α}
    (free : PairFree source target letters) :
    PairFree target source letters :=
  ⟨free.2, free.1⟩

private theorem pairFree_tail
    {α : Type v} {source target first : α} {rest : List α}
    (free : PairFree source target (first :: rest)) :
    PairFree source target rest := by
  exact
    ⟨fun member => free.1 (List.Mem.tail first member),
      fun member => free.2 (List.Mem.tail first member)⟩

private theorem directedSimpleAdjacencyValuation_eq_other
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

private theorem pairFree_parts_of_simple_split
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

private theorem pairFree_ends_of_adjacent_split
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

private def adjacentPairsList {α : Type v} : List α → List (α × α)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

private theorem mem_adjacentPairsList_iff_exists_split
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

private theorem adjacentPairsList_toList
    {α : Type v} (word : Word α) :
    adjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

private theorem mem_adjacentPairs_iff_exists_split
    {α : Type v} [DecidableEq α]
    (source target : α) (word : Word α) :
    (source, target) ∈ word.adjacentPairs ↔
      ∃ before after,
        word.toList = before ++ source :: target :: after := by
  rw [← adjacentPairsList_toList]
  exact
    mem_adjacentPairsList_iff_exists_split
      source target word.toList

private theorem simplePair_order_cases
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

private def listEvalStep
    {S : Type u} (G : Semigroup S) : Option S → S → Option S
  | none, next => some next
  | some current, next => some (G.mul current next)

private def listEvalFrom
    {S : Type u} {α : Type v} (G : Semigroup S)
    (initial : Option S) (valuation : α → S)
    (letters : List α) : Option S :=
  letters.foldl
    (fun current letter =>
      listEvalStep G current (valuation letter))
    initial

@[simp]
private theorem listEvalFrom_nil
    {S : Type u} {α : Type v} (G : Semigroup S)
    (initial : Option S) (valuation : α → S) :
    listEvalFrom G initial valuation [] = initial :=
  rfl

@[simp]
private theorem listEvalFrom_cons
    {S : Type u} {α : Type v} (G : Semigroup S)
    (initial : Option S) (valuation : α → S)
    (first : α) (rest : List α) :
    listEvalFrom G initial valuation (first :: rest) =
      listEvalFrom G
        (listEvalStep G initial (valuation first)) valuation rest :=
  rfl

private theorem listEvalFrom_append
    {S : Type u} {α : Type v} (G : Semigroup S)
    (initial : Option S) (valuation : α → S)
    (left right : List α) :
    listEvalFrom G initial valuation (left ++ right) =
      listEvalFrom G
        (listEvalFrom G initial valuation left) valuation right := by
  simp [listEvalFrom, List.foldl_append]

private theorem listEvalFrom_some
    {S : Type u} {α : Type v} (G : Semigroup S)
    (initial : S) (valuation : α → S) (letters : List α) :
    listEvalFrom G (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter => G.mul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil =>
      rfl
  | cons first rest ih =>
      rw [listEvalFrom_cons]
      simp only [listEvalStep, List.foldl_cons]
      exact ih (G.mul initial (valuation first))

private theorem listEvalFrom_toList
    {S : Type u} {α : Type v} (G : Semigroup S)
    (valuation : α → S) (word : Word α) :
    listEvalFrom G none valuation word.toList =
      some (G.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, listEvalFrom_cons, listEvalStep,
        Semigroup.eval]
      exact listEvalFrom_some G (valuation head) valuation tail

private theorem listEvalFrom_pairFree_fixed
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S) {source target : α}
    {sourceState targetState otherState : S}
    (state : S) (fixed : G.mul state otherState = state)
    {letters : List α} (free : PairFree source target letters) :
    listEvalFrom G (some state)
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState) letters =
      some state := by
  induction letters with
  | nil =>
      rfl
  | cons first rest ih =>
      have firstValue :
          directedSimpleAdjacencyValuation source target
              sourceState targetState otherState first = otherState :=
        directedSimpleAdjacencyValuation_eq_other
          sourceState targetState otherState free (List.Mem.head rest)
      have tailFree : PairFree source target rest :=
        pairFree_tail free
      rw [listEvalFrom_cons, firstValue]
      simp only [listEvalStep, fixed]
      exact ih tailFree

private theorem listEvalFrom_none_pairFree_cons
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S) {source target first : α}
    {sourceState targetState otherState : S} {rest : List α}
    (otherOther : G.mul otherState otherState = otherState)
    (free : PairFree source target (first :: rest)) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState) (first :: rest) =
      some otherState := by
  have firstValue :
      directedSimpleAdjacencyValuation source target
          sourceState targetState otherState first = otherState :=
    directedSimpleAdjacencyValuation_eq_other
      sourceState targetState otherState free (List.Mem.head rest)
  rw [listEvalFrom_cons, firstValue]
  simp only [listEvalStep]
  exact
    listEvalFrom_pairFree_fixed
      G otherState otherOther (pairFree_tail free)

private theorem listEval_prefix_source
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    {source target : α} (leading rest : List α)
    (leadingFree : PairFree source target leading) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState)
        (leading ++ source :: rest) =
      listEvalFrom G (some sourceState)
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState) rest := by
  rw [listEvalFrom_append]
  cases leading with
  | nil =>
      simp [listEvalStep]
  | cons first tail =>
      rw [listEvalFrom_none_pairFree_cons
        G laws.other_other leadingFree]
      simp [listEvalStep, laws.other_source]

private theorem listEval_adjacent
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    {source target : α} (different : source ≠ target)
    (before after : List α)
    (beforeFree : PairFree source target before)
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState)
        (before ++ source :: target :: after) =
      some one := by
  rw [listEval_prefix_source G laws before (target :: after) beforeFree]
  rw [listEvalFrom_cons,
    directedSimpleAdjacencyValuation_target different]
  simp only [listEvalStep, laws.source_target]
  exact
    listEvalFrom_pairFree_fixed G one laws.one_other afterFree

private theorem listEval_forward_gap
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    {source target gapFirst : α} (different : source ≠ target)
    (before gapRest after : List α)
    (beforeFree : PairFree source target before)
    (gapFree : PairFree source target (gapFirst :: gapRest))
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState)
        (before ++
          source :: (gapFirst :: (gapRest ++ target :: after))) =
      some zero := by
  rw [listEval_prefix_source G laws before
    (gapFirst :: (gapRest ++ target :: after)) beforeFree]
  have gapFirstValue :
      directedSimpleAdjacencyValuation source target
          sourceState targetState otherState gapFirst = otherState :=
    directedSimpleAdjacencyValuation_eq_other
      sourceState targetState otherState gapFree (List.Mem.head gapRest)
  rw [listEvalFrom_cons, gapFirstValue]
  simp only [listEvalStep]
  rw [listEvalFrom_append]
  rw [listEvalFrom_pairFree_fixed
    G (G.mul sourceState otherState) laws.source_other_other
      (pairFree_tail gapFree)]
  rw [listEvalFrom_cons,
    directedSimpleAdjacencyValuation_target different]
  simp only [listEvalStep, laws.source_other_target]
  exact
    listEvalFrom_pairFree_fixed G zero laws.zero_other afterFree

private theorem listEval_reverse
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    {source target : α} (different : source ≠ target)
    (before middle after : List α)
    (beforeFree : PairFree source target before)
    (middleFree : PairFree source target middle)
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState)
        (before ++ target :: (middle ++ source :: after)) =
      some zero := by
  rw [listEvalFrom_append]
  cases before with
  | nil =>
      simp only [listEvalFrom_nil, listEvalFrom_cons,
        directedSimpleAdjacencyValuation_target different,
        listEvalStep]
      rw [listEvalFrom_append]
      rw [listEvalFrom_pairFree_fixed
        G targetState laws.target_other middleFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_source]
      simp only [listEvalStep, laws.target_source]
      exact
        listEvalFrom_pairFree_fixed G zero laws.zero_other afterFree
  | cons first tail =>
      rw [listEvalFrom_none_pairFree_cons
        G laws.other_other beforeFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_target different]
      simp only [listEvalStep]
      rw [listEvalFrom_append]
      rw [listEvalFrom_pairFree_fixed
        G (G.mul otherState targetState) laws.other_target_other
          middleFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_source]
      simp only [listEvalStep, laws.other_target_source]
      exact
        listEvalFrom_pairFree_fixed G zero laws.zero_other afterFree

/-- The five-state detector evaluates to `one` exactly on the requested
directed adjacent pair and to `zero` in both nonadjacent orders. -/
theorem eval_directedSimpleAdjacency
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    G.eval
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState) word =
      if (source, target) ∈ word.adjacentPairs then one else zero := by
  by_cases adjacent : (source, target) ∈ word.adjacentPairs
  · obtain ⟨before, after, split⟩ :=
      (mem_adjacentPairs_iff_exists_split source target word).mp adjacent
    have sourceCount :
        (before ++ source :: target :: after).count source = 1 := by
      rw [← split]
      exact sourceSimple
    have targetCount :
        (before ++ source :: target :: after).count target = 1 := by
      rw [← split]
      exact targetSimple
    have free :=
      pairFree_ends_of_adjacent_split
        different sourceCount targetCount
    have evaluated :
        listEvalFrom G none
            (directedSimpleAdjacencyValuation source target
              sourceState targetState otherState) word.toList =
          some one := by
      rw [split]
      exact
        listEval_adjacent G laws different
          before after free.1 free.2
    rw [listEvalFrom_toList] at evaluated
    simpa [adjacent] using evaluated
  · obtain forward | reverse :=
      simplePair_order_cases different sourceSimple targetSimple
    · obtain ⟨before, middle, after, split⟩ := forward
      have sourceCount :
          (before ++ source :: (middle ++ target :: after)).count
              source = 1 := by
        rw [← split]
        exact sourceSimple
      have targetCount :
          (before ++ source :: (middle ++ target :: after)).count
              target = 1 := by
        rw [← split]
        exact targetSimple
      have free :=
        pairFree_parts_of_simple_split
          different sourceCount targetCount
      cases middle with
      | nil =>
          have edge : (source, target) ∈ word.adjacentPairs :=
            (mem_adjacentPairs_iff_exists_split
              source target word).mpr
              ⟨before, after, by simpa using split⟩
          exact False.elim (adjacent edge)
      | cons gapFirst gapRest =>
          have evaluated :
              listEvalFrom G none
                  (directedSimpleAdjacencyValuation source target
                    sourceState targetState otherState) word.toList =
                some zero := by
            rw [split]
            exact
              listEval_forward_gap G laws different
                before gapRest after free.1 free.2.1 free.2.2
          rw [listEvalFrom_toList] at evaluated
          simpa [adjacent] using evaluated
    · obtain ⟨before, middle, after, split⟩ := reverse
      have targetCount :
          (before ++ target :: (middle ++ source :: after)).count
              target = 1 := by
        rw [← split]
        exact targetSimple
      have sourceCount :
          (before ++ target :: (middle ++ source :: after)).count
              source = 1 := by
        rw [← split]
        exact sourceSimple
      have reverseFree :=
        pairFree_parts_of_simple_split
          (Ne.symm different) targetCount sourceCount
      have evaluated :
          listEvalFrom G none
              (directedSimpleAdjacencyValuation source target
                sourceState targetState otherState) word.toList =
            some zero := by
        rw [split]
        exact
          listEval_reverse G laws different before middle after
            (pairFree_symm reverseFree.1)
            (pairFree_symm reverseFree.2.1)
            (pairFree_symm reverseFree.2.2)
      rw [listEvalFrom_toList] at evaluated
      simpa [adjacent] using evaluated

/-- Under the five supplied states, evaluation at `one` recognizes exactly
the requested directed adjacent pair of globally simple letters. -/
theorem eval_directedSimpleAdjacency_eq_one_iff
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    G.eval
        (directedSimpleAdjacencyValuation source target
          sourceState targetState otherState) word = one ↔
      (source, target) ∈ word.adjacentPairs := by
  rw [eval_directedSimpleAdjacency G laws source target word
    different sourceSimple targetSimple]
  by_cases adjacent : (source, target) ∈ word.adjacentPairs <;>
    simp [adjacent, laws.zero_ne_one]

/-- Every identity valid in a semigroup carrying the five detector states
preserves directed adjacency between variables simple on both sides. -/
theorem valid_directedSimpleAdjacency_iff
    {S : Type u} {α : Type v} [DecidableEq α]
    (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    (identity : Identity α) (valid : identity.SatisfiedBy G)
    (source target : α) (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    (source, target) ∈ identity.lhs.adjacentPairs ↔
      (source, target) ∈ identity.rhs.adjacentPairs := by
  have evaluated :=
    valid
      (directedSimpleAdjacencyValuation source target
        sourceState targetState otherState)
  constructor
  · intro lhsAdjacent
    have lhsOne :
        G.eval
            (directedSimpleAdjacencyValuation source target
              sourceState targetState otherState) identity.lhs = one :=
      (eval_directedSimpleAdjacency_eq_one_iff
        G laws source target identity.lhs different
        lhsSourceSimple lhsTargetSimple).mpr lhsAdjacent
    have rhsOne :
        G.eval
            (directedSimpleAdjacencyValuation source target
              sourceState targetState otherState) identity.rhs = one :=
      evaluated.symm.trans lhsOne
    exact
      (eval_directedSimpleAdjacency_eq_one_iff
        G laws source target identity.rhs different
        rhsSourceSimple rhsTargetSimple).mp rhsOne
  · intro rhsAdjacent
    have rhsOne :
        G.eval
            (directedSimpleAdjacencyValuation source target
              sourceState targetState otherState) identity.rhs = one :=
      (eval_directedSimpleAdjacency_eq_one_iff
        G laws source target identity.rhs different
        rhsSourceSimple rhsTargetSimple).mpr rhsAdjacent
    have lhsOne :
        G.eval
            (directedSimpleAdjacencyValuation source target
              sourceState targetState otherState) identity.lhs = one :=
      evaluated.trans rhsOne
    exact
      (eval_directedSimpleAdjacency_eq_one_iff
        G laws source target identity.lhs different
        lhsSourceSimple lhsTargetSimple).mp lhsOne

/-- `SimpleAdjacent` wrapper for the order-six completeness invariant. -/
theorem valid_simpleAdjacent_iff
    {S : Type u} (G : Semigroup S)
    {zero one targetState sourceState otherState : S}
    (laws : DirectedSimpleAdjacencyLaws G
      zero one targetState sourceState otherState)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (source target : Nat) (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    S5_107.SimpleAdjacent identity.lhs source target ↔
      S5_107.SimpleAdjacent identity.rhs source target := by
  change
    (identity.lhs.toList.count source = 1 ∧
      identity.lhs.toList.count target = 1 ∧
      (source, target) ∈ identity.lhs.adjacentPairs) ↔
    (identity.rhs.toList.count source = 1 ∧
      identity.rhs.toList.count target = 1 ∧
      (source, target) ∈ identity.rhs.adjacentPairs)
  have adjacent :=
    valid_directedSimpleAdjacency_iff G laws identity valid
      source target different lhsSourceSimple lhsTargetSimple
      rhsSourceSimple rhsTargetSimple
  constructor
  · rintro ⟨_, _, edge⟩
    exact ⟨rhsSourceSimple, rhsTargetSimple, adjacent.mp edge⟩
  · rintro ⟨_, _, edge⟩
    exact ⟨lhsSourceSimple, lhsTargetSimple, adjacent.mpr edge⟩

end SemigroupBasis.CoRoots.Order6SporadicSection15

import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_107AdjacencySemantics

open SemigroupBasis

/-- Send the directed source to zero-based state `3`, the directed target to
state `2`, and every other variable to state `4`. -/
def directedSimpleAdjacencyValuation
    {α : Type} [DecidableEq α] (source target : α) : α → Fin 5 :=
  fun letter =>
    if letter = source then 3
    else if letter = target then 2
    else 4

@[simp]
private theorem directedSimpleAdjacencyValuation_source
    {α : Type} [DecidableEq α] (source target : α) :
    directedSimpleAdjacencyValuation source target source = 3 := by
  simp [directedSimpleAdjacencyValuation]

private theorem directedSimpleAdjacencyValuation_target
    {α : Type} [DecidableEq α] {source target : α}
    (different : source ≠ target) :
    directedSimpleAdjacencyValuation source target target = 2 := by
  simp [directedSimpleAdjacencyValuation, Ne.symm different]

private def PairFree
    {α : Type} (source target : α) (letters : List α) : Prop :=
  source ∉ letters ∧ target ∉ letters

private theorem pairFree_symm
    {α : Type} {source target : α} {letters : List α}
    (free : PairFree source target letters) :
    PairFree target source letters :=
  ⟨free.2, free.1⟩

private theorem pairFree_tail
    {α : Type} {source target first : α} {rest : List α}
    (free : PairFree source target (first :: rest)) :
    PairFree source target rest := by
  exact
    ⟨fun member => free.1 (List.Mem.tail first member),
      fun member => free.2 (List.Mem.tail first member)⟩

private theorem directedSimpleAdjacencyValuation_eq_four
    {α : Type} [DecidableEq α] {source target letter : α}
    {letters : List α}
    (free : PairFree source target letters)
    (member : letter ∈ letters) :
    directedSimpleAdjacencyValuation source target letter = 4 := by
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
    {α : Type} [DecidableEq α]
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
    {α : Type} [DecidableEq α]
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

private def adjacentPairsList {α : Type} : List α → List (α × α)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

private theorem mem_adjacentPairsList_iff_exists_split
    {α : Type} [DecidableEq α] (source target : α) :
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
    {α : Type} (word : Word α) :
    adjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

private theorem mem_adjacentPairs_iff_exists_split
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α) :
    (source, target) ∈ word.adjacentPairs ↔
      ∃ before after,
        word.toList = before ++ source :: target :: after := by
  rw [← adjacentPairsList_toList]
  exact
    mem_adjacentPairsList_iff_exists_split
      source target word.toList

private theorem simplePair_order_cases
    {α : Type} [DecidableEq α]
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
    (G : Semigroup (Fin 5)) :
    Option (Fin 5) → Fin 5 → Option (Fin 5)
  | none, next => some next
  | some current, next => some (G.mul current next)

private def listEvalFrom
    {α : Type} (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : α → Fin 5)
    (letters : List α) : Option (Fin 5) :=
  letters.foldl
    (fun current letter =>
      listEvalStep G current (valuation letter))
    initial

@[simp]
private theorem listEvalFrom_nil
    {α : Type} (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : α → Fin 5) :
    listEvalFrom G initial valuation [] = initial :=
  rfl

@[simp]
private theorem listEvalFrom_cons
    {α : Type} (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : α → Fin 5)
    (first : α) (rest : List α) :
    listEvalFrom G initial valuation (first :: rest) =
      listEvalFrom G
        (listEvalStep G initial (valuation first)) valuation rest :=
  rfl

private theorem listEvalFrom_append
    {α : Type} (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : α → Fin 5)
    (left right : List α) :
    listEvalFrom G initial valuation (left ++ right) =
      listEvalFrom G
        (listEvalFrom G initial valuation left) valuation right := by
  simp [listEvalFrom, List.foldl_append]

private theorem listEvalFrom_some
    {α : Type} (G : Semigroup (Fin 5))
    (initial : Fin 5) (valuation : α → Fin 5)
    (letters : List α) :
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
    {α : Type} (G : Semigroup (Fin 5))
    (valuation : α → Fin 5) (word : Word α) :
    listEvalFrom G none valuation word.toList =
      some (G.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, listEvalFrom_cons, listEvalStep,
        Semigroup.eval]
      exact listEvalFrom_some G (valuation head) valuation tail

private theorem listEvalFrom_pairFree_fixed
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target : α}
    (state : Fin 5) (fixed : G.mul state 4 = state)
    {letters : List α} (free : PairFree source target letters) :
    listEvalFrom G (some state)
        (directedSimpleAdjacencyValuation source target) letters =
      some state := by
  induction letters with
  | nil =>
      rfl
  | cons first rest ih =>
      have firstValue :
          directedSimpleAdjacencyValuation source target first = 4 :=
        directedSimpleAdjacencyValuation_eq_four free
          (List.Mem.head rest)
      have tailFree : PairFree source target rest :=
        pairFree_tail free
      rw [listEvalFrom_cons, firstValue]
      simp only [listEvalStep, fixed]
      exact ih tailFree

private theorem listEvalFrom_none_pairFree_cons
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target first : α}
    {rest : List α}
    (fourFour : G.mul 4 4 = 4)
    (free : PairFree source target (first :: rest)) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target)
        (first :: rest) =
      some 4 := by
  have firstValue :
      directedSimpleAdjacencyValuation source target first = 4 :=
    directedSimpleAdjacencyValuation_eq_four free
      (List.Mem.head rest)
  rw [listEvalFrom_cons, firstValue]
  simp only [listEvalStep]
  exact
    listEvalFrom_pairFree_fixed
      G 4 fourFour (pairFree_tail free)

private theorem listEval_prefix_source
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target : α}
    (fourFour : G.mul 4 4 = 4)
    (fourSource : G.mul 4 3 = 3)
    (leading rest : List α)
    (leadingFree : PairFree source target leading) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target)
        (leading ++ source :: rest) =
      listEvalFrom G (some 3)
        (directedSimpleAdjacencyValuation source target) rest := by
  rw [listEvalFrom_append]
  cases leading with
  | nil =>
      simp [listEvalStep]
  | cons first tail =>
      rw [listEvalFrom_none_pairFree_cons
        G fourFour leadingFree]
      simp [listEvalStep, fourSource]

private theorem listEval_adjacent
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target : α}
    (different : source ≠ target)
    (fourFour : G.mul 4 4 = 4)
    (fourSource : G.mul 4 3 = 3)
    (sourceTarget : G.mul 3 2 = 1)
    (oneFour : G.mul 1 4 = 1)
    (before after : List α)
    (beforeFree : PairFree source target before)
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target)
        (before ++ source :: target :: after) =
      some 1 := by
  rw [listEval_prefix_source
    G fourFour fourSource before (target :: after) beforeFree]
  rw [listEvalFrom_cons,
    directedSimpleAdjacencyValuation_target different]
  simp only [listEvalStep, sourceTarget]
  exact
    listEvalFrom_pairFree_fixed G 1 oneFour afterFree

private theorem listEval_forward_gap
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target gapFirst : α}
    (different : source ≠ target)
    (fourFour : G.mul 4 4 = 4)
    (fourSource : G.mul 4 3 = 3)
    (gapFour :
      G.mul (G.mul 3 4) 4 = G.mul 3 4)
    (gapTarget : G.mul (G.mul 3 4) 2 = 0)
    (zeroFour : G.mul 0 4 = 0)
    (before gapRest after : List α)
    (beforeFree : PairFree source target before)
    (gapFree : PairFree source target (gapFirst :: gapRest))
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target)
        (before ++
          source :: (gapFirst :: (gapRest ++ target :: after))) =
      some 0 := by
  rw [listEval_prefix_source
    G fourFour fourSource before
      (gapFirst :: (gapRest ++ target :: after)) beforeFree]
  have gapFirstValue :
      directedSimpleAdjacencyValuation source target gapFirst = 4 :=
    directedSimpleAdjacencyValuation_eq_four gapFree
      (List.Mem.head gapRest)
  rw [listEvalFrom_cons, gapFirstValue]
  simp only [listEvalStep]
  rw [listEvalFrom_append]
  rw [listEvalFrom_pairFree_fixed
    G (G.mul 3 4) gapFour (pairFree_tail gapFree)]
  rw [listEvalFrom_cons,
    directedSimpleAdjacencyValuation_target different]
  simp only [listEvalStep, gapTarget]
  exact
    listEvalFrom_pairFree_fixed G 0 zeroFour afterFree

private theorem listEval_reverse
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5)) {source target : α}
    (different : source ≠ target)
    (fourFour : G.mul 4 4 = 4)
    (twoFour : G.mul 2 4 = 2)
    (twoSource : G.mul 2 3 = 0)
    (prefixedTargetFour :
      G.mul (G.mul 4 2) 4 = G.mul 4 2)
    (prefixedTargetSource : G.mul (G.mul 4 2) 3 = 0)
    (zeroFour : G.mul 0 4 = 0)
    (before middle after : List α)
    (beforeFree : PairFree source target before)
    (middleFree : PairFree source target middle)
    (afterFree : PairFree source target after) :
    listEvalFrom G none
        (directedSimpleAdjacencyValuation source target)
        (before ++ target :: (middle ++ source :: after)) =
      some 0 := by
  rw [listEvalFrom_append]
  cases before with
  | nil =>
      simp only [listEvalFrom_nil, listEvalFrom_cons,
        directedSimpleAdjacencyValuation_target different,
        listEvalStep]
      rw [listEvalFrom_append]
      rw [listEvalFrom_pairFree_fixed G 2 twoFour middleFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_source]
      simp only [listEvalStep, twoSource]
      exact
        listEvalFrom_pairFree_fixed G 0 zeroFour afterFree
  | cons first tail =>
      rw [listEvalFrom_none_pairFree_cons
        G fourFour beforeFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_target different]
      simp only [listEvalStep]
      rw [listEvalFrom_append]
      rw [listEvalFrom_pairFree_fixed
        G (G.mul 4 2) prefixedTargetFour middleFree]
      rw [listEvalFrom_cons,
        directedSimpleAdjacencyValuation_source]
      simp only [listEvalStep, prefixedTargetSource]
      exact
        listEvalFrom_pairFree_fixed G 0 zeroFour afterFree

private structure DirectedSimpleAdjacencyTableLaws
    (G : Semigroup (Fin 5)) : Prop where
  fourFour : G.mul 4 4 = 4
  fourSource : G.mul 4 3 = 3
  sourceTarget : G.mul 3 2 = 1
  oneFour : G.mul 1 4 = 1
  zeroFour : G.mul 0 4 = 0
  twoFour : G.mul 2 4 = 2
  twoSource : G.mul 2 3 = 0
  gapFour : G.mul (G.mul 3 4) 4 = G.mul 3 4
  gapTarget : G.mul (G.mul 3 4) 2 = 0
  prefixedTargetFour :
    G.mul (G.mul 4 2) 4 = G.mul 4 2
  prefixedTargetSource : G.mul (G.mul 4 2) 3 = 0

private theorem eval_directedSimpleAdjacency_eq_ite_of_table
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5))
    (laws : DirectedSimpleAdjacencyTableLaws G)
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    G.eval (directedSimpleAdjacencyValuation source target) word =
      if (source, target) ∈ word.adjacentPairs then 1 else 0 := by
  by_cases adjacent : (source, target) ∈ word.adjacentPairs
  · obtain ⟨before, after, split⟩ :=
      (mem_adjacentPairs_iff_exists_split
        source target word).mp adjacent
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
            (directedSimpleAdjacencyValuation source target)
            word.toList =
          some 1 := by
      rw [split]
      exact
        listEval_adjacent G different laws.fourFour
          laws.fourSource laws.sourceTarget laws.oneFour
          before after free.1 free.2
    rw [listEvalFrom_toList] at evaluated
    simpa [adjacent] using evaluated
  · obtain forward | reverse :=
      simplePair_order_cases
        different sourceSimple targetSimple
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
                  (directedSimpleAdjacencyValuation source target)
                  word.toList =
                some 0 := by
            rw [split]
            exact
              listEval_forward_gap G different
                laws.fourFour laws.fourSource
                laws.gapFour laws.gapTarget laws.zeroFour
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
              (directedSimpleAdjacencyValuation source target)
              word.toList =
            some 0 := by
        rw [split]
        exact
          listEval_reverse G different laws.fourFour
            laws.twoFour laws.twoSource
            laws.prefixedTargetFour laws.prefixedTargetSource
            laws.zeroFour before middle after
            (pairFree_symm reverseFree.1)
            (pairFree_symm reverseFree.2.1)
            (pairFree_symm reverseFree.2.2)
      rw [listEvalFrom_toList] at evaluated
      simpa [adjacent] using evaluated

private theorem eval_directedSimpleAdjacency_eq_one_iff_of_table
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5))
    (laws : DirectedSimpleAdjacencyTableLaws G)
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    G.eval (directedSimpleAdjacencyValuation source target) word = 1 ↔
      (source, target) ∈ word.adjacentPairs := by
  rw [eval_directedSimpleAdjacency_eq_ite_of_table
    G laws source target word different sourceSimple targetSimple]
  by_cases adjacent : (source, target) ∈ word.adjacentPairs <;>
    simp [adjacent]

private theorem valid_directedSimpleAdjacency_iff_of_table
    {α : Type} [DecidableEq α]
    (G : Semigroup (Fin 5))
    (laws : DirectedSimpleAdjacencyTableLaws G)
    (identity : Identity α)
    (valid : identity.SatisfiedBy G)
    (source target : α)
    (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    (source, target) ∈ identity.lhs.adjacentPairs ↔
      (source, target) ∈ identity.rhs.adjacentPairs := by
  have evaluated :=
    valid (directedSimpleAdjacencyValuation source target)
  constructor
  · intro lhsAdjacent
    have lhsOne :
        G.eval (directedSimpleAdjacencyValuation source target)
            identity.lhs = 1 :=
      (eval_directedSimpleAdjacency_eq_one_iff_of_table
        G laws source target identity.lhs different
        lhsSourceSimple lhsTargetSimple).mpr lhsAdjacent
    have rhsOne :
        G.eval (directedSimpleAdjacencyValuation source target)
            identity.rhs = 1 :=
      evaluated.symm.trans lhsOne
    exact
      (eval_directedSimpleAdjacency_eq_one_iff_of_table
        G laws source target identity.rhs different
        rhsSourceSimple rhsTargetSimple).mp rhsOne
  · intro rhsAdjacent
    have rhsOne :
        G.eval (directedSimpleAdjacencyValuation source target)
            identity.rhs = 1 :=
      (eval_directedSimpleAdjacency_eq_one_iff_of_table
        G laws source target identity.rhs different
        rhsSourceSimple rhsTargetSimple).mpr rhsAdjacent
    have lhsOne :
        G.eval (directedSimpleAdjacencyValuation source target)
            identity.lhs = 1 :=
      evaluated.trans rhsOne
    exact
      (eval_directedSimpleAdjacency_eq_one_iff_of_table
        G laws source target identity.lhs different
        lhsSourceSimple lhsTargetSimple).mp lhsOne

private theorem s5_107TableLaws :
    DirectedSimpleAdjacencyTableLaws
      Generated.Catalogue.S5_107.table.semigroup := by
  exact
    { fourFour := by decide
      fourSource := by decide
      sourceTarget := by decide
      oneFour := by decide
      zeroFour := by decide
      twoFour := by decide
      twoSource := by decide
      gapFour := by decide
      gapTarget := by decide
      prefixedTargetFour := by decide
      prefixedTargetSource := by decide }

private theorem s5_108TableLaws :
    DirectedSimpleAdjacencyTableLaws
      Generated.Catalogue.S5_108.table.semigroup := by
  exact
    { fourFour := by decide
      fourSource := by decide
      sourceTarget := by decide
      oneFour := by decide
      zeroFour := by decide
      twoFour := by decide
      twoSource := by decide
      gapFour := by decide
      gapTarget := by decide
      prefixedTargetFour := by decide
      prefixedTargetSource := by decide }

private theorem s5_109TableLaws :
    DirectedSimpleAdjacencyTableLaws
      Generated.Catalogue.S5_109.table.semigroup := by
  exact
    { fourFour := by decide
      fourSource := by decide
      sourceTarget := by decide
      oneFour := by decide
      zeroFour := by decide
      twoFour := by decide
      twoSource := by decide
      gapFour := by decide
      gapTarget := by decide
      prefixedTargetFour := by decide
      prefixedTargetSource := by decide }

namespace S5_107

/-- Exact simple-adjacency evaluation in the catalogue table `S5_107`. -/
theorem eval_directedSimpleAdjacency
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_107.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
      if (source, target) ∈ word.adjacentPairs then
        (1 : Fin 5)
      else
        (0 : Fin 5) :=
  eval_directedSimpleAdjacency_eq_ite_of_table
    Generated.Catalogue.S5_107.table.semigroup s5_107TableLaws
    source target word different sourceSimple targetSimple

/-- At the directed separator valuation, `S5_107` evaluates to state `1`
exactly when the two simple variables occur as the directed adjacent pair. -/
theorem eval_directedSimpleAdjacency_eq_one_iff
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_107.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
          (1 : Fin 5) ↔
      (source, target) ∈ word.adjacentPairs :=
  eval_directedSimpleAdjacency_eq_one_iff_of_table
    Generated.Catalogue.S5_107.table.semigroup s5_107TableLaws
    source target word different sourceSimple targetSimple

/-- Every identity valid in `S5_107` preserves directed adjacency between
variables that are simple on both sides. -/
theorem valid_directedSimpleAdjacency_iff
    {α : Type} [DecidableEq α]
    (identity : Identity α)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_107.table.semigroup)
    (source target : α)
    (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    (source, target) ∈ identity.lhs.adjacentPairs ↔
      (source, target) ∈ identity.rhs.adjacentPairs :=
  valid_directedSimpleAdjacency_iff_of_table
    Generated.Catalogue.S5_107.table.semigroup s5_107TableLaws
    identity valid source target different
    lhsSourceSimple lhsTargetSimple rhsSourceSimple rhsTargetSimple

end S5_107

namespace S5_108

/-- Exact simple-adjacency evaluation in the catalogue table `S5_108`. -/
theorem eval_directedSimpleAdjacency
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_108.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
      if (source, target) ∈ word.adjacentPairs then
        (1 : Fin 5)
      else
        (0 : Fin 5) :=
  eval_directedSimpleAdjacency_eq_ite_of_table
    Generated.Catalogue.S5_108.table.semigroup s5_108TableLaws
    source target word different sourceSimple targetSimple

/-- At the directed separator valuation, `S5_108` evaluates to state `1`
exactly when the two simple variables occur as the directed adjacent pair. -/
theorem eval_directedSimpleAdjacency_eq_one_iff
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_108.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
          (1 : Fin 5) ↔
      (source, target) ∈ word.adjacentPairs :=
  eval_directedSimpleAdjacency_eq_one_iff_of_table
    Generated.Catalogue.S5_108.table.semigroup s5_108TableLaws
    source target word different sourceSimple targetSimple

/-- Every identity valid in `S5_108` preserves directed adjacency between
variables that are simple on both sides. -/
theorem valid_directedSimpleAdjacency_iff
    {α : Type} [DecidableEq α]
    (identity : Identity α)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_108.table.semigroup)
    (source target : α)
    (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    (source, target) ∈ identity.lhs.adjacentPairs ↔
      (source, target) ∈ identity.rhs.adjacentPairs :=
  valid_directedSimpleAdjacency_iff_of_table
    Generated.Catalogue.S5_108.table.semigroup s5_108TableLaws
    identity valid source target different
    lhsSourceSimple lhsTargetSimple rhsSourceSimple rhsTargetSimple

end S5_108

namespace S5_109

/-- Exact simple-adjacency evaluation in the catalogue table `S5_109`. -/
theorem eval_directedSimpleAdjacency
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_109.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
      if (source, target) ∈ word.adjacentPairs then
        (1 : Fin 5)
      else
        (0 : Fin 5) :=
  eval_directedSimpleAdjacency_eq_ite_of_table
    Generated.Catalogue.S5_109.table.semigroup s5_109TableLaws
    source target word different sourceSimple targetSimple

/-- At the directed separator valuation, `S5_109` evaluates to state `1`
exactly when the two simple variables occur as the directed adjacent pair. -/
theorem eval_directedSimpleAdjacency_eq_one_iff
    {α : Type} [DecidableEq α]
    (source target : α) (word : Word α)
    (different : source ≠ target)
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    Generated.Catalogue.S5_109.table.semigroup.eval
        (directedSimpleAdjacencyValuation source target) word =
          (1 : Fin 5) ↔
      (source, target) ∈ word.adjacentPairs :=
  eval_directedSimpleAdjacency_eq_one_iff_of_table
    Generated.Catalogue.S5_109.table.semigroup s5_109TableLaws
    source target word different sourceSimple targetSimple

/-- Every identity valid in `S5_109` preserves directed adjacency between
variables that are simple on both sides. -/
theorem valid_directedSimpleAdjacency_iff
    {α : Type} [DecidableEq α]
    (identity : Identity α)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_109.table.semigroup)
    (source target : α)
    (different : source ≠ target)
    (lhsSourceSimple : identity.lhs.toList.count source = 1)
    (lhsTargetSimple : identity.lhs.toList.count target = 1)
    (rhsSourceSimple : identity.rhs.toList.count source = 1)
    (rhsTargetSimple : identity.rhs.toList.count target = 1) :
    (source, target) ∈ identity.lhs.adjacentPairs ↔
      (source, target) ∈ identity.rhs.adjacentPairs :=
  valid_directedSimpleAdjacency_iff_of_table
    Generated.Catalogue.S5_109.table.semigroup s5_109TableLaws
    identity valid source target different
    lhsSourceSimple lhsTargetSimple rhsSourceSimple rhsTargetSimple

end S5_109

end SemigroupBasis.CoRoots.S5_107AdjacencySemantics

import SemigroupBasis.CoRoots.S5_868SuffixContraction
import SemigroupBasis.Examples.ConnectedComponentFourComponents

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Words represented by nonempty factor lists -/

/-- Total conversion of a list to a word. All factorization theorems below
carry a proof that the input list is nonempty, so the fallback is never used. -/
def maximalFactorWord (letters : List Nat) : Word Nat :=
  completionWordOfList 0 letters

@[simp]
theorem maximalFactorWord_toList
    {letters : List Nat} (nonempty : letters ≠ []) :
    (maximalFactorWord letters).toList = letters :=
  completionWordOfList_toList 0 nonempty

theorem maximalFactorWord_eq_of_toList
    {word : Word Nat} {letters : List Nat}
    (shape : word.toList = letters) :
    maximalFactorWord letters = word := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by
    rw [← shape]
    simp [Word.toList])]
  exact shape.symm

private theorem maximal_getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem maximal_word_toList_getLastD
    (word : Word Nat) (fallback : Nat) :
    word.toList.getLastD fallback = word.final := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, Word.final, List.getLastD_cons]

private theorem maximal_dropLast_append_getLastD
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

theorem maximalFactorWord_head_of_prefix
    {stem suffix : List Nat} (prefixNonempty : stem ≠ []) :
    (maximalFactorWord (stem ++ suffix)).head =
      (maximalFactorWord stem).head := by
  cases stem with
  | nil => contradiction
  | cons head tail => rfl

theorem maximalFactorWord_final_of_suffix
    {stem suffix : List Nat} (suffixNonempty : suffix ≠ []) :
    (maximalFactorWord (stem ++ suffix)).final =
      (maximalFactorWord suffix).final := by
  cases suffix with
  | nil => contradiction
  | cons rightHead rightTail =>
      have combinedNonempty :
          stem ++ (rightHead :: rightTail) ≠ [] := by
        simp
      calc
        (maximalFactorWord
            (stem ++ (rightHead :: rightTail))).final =
            (maximalFactorWord
                (stem ++ (rightHead :: rightTail))).toList.getLastD 0 :=
          (maximal_word_toList_getLastD _ _).symm
        _ = (stem ++ (rightHead :: rightTail)).getLastD 0 := by
          rw [maximalFactorWord_toList combinedNonempty]
        _ = (rightHead :: rightTail).getLastD
              (stem.getLastD 0) :=
          maximal_getLastD_append stem (rightHead :: rightTail) 0
        _ = (maximalFactorWord
                (rightHead :: rightTail)).toList.getLastD
              (stem.getLastD 0) := by
          rw [maximalFactorWord_toList (by simp)]
        _ = (maximalFactorWord
                (rightHead :: rightTail)).final :=
          maximal_word_toList_getLastD _ _

theorem maximalFactorWord_final_append_singleton
    (stem : List Nat) (final : Nat) :
    (maximalFactorWord (stem ++ [final])).final = final := by
  cases stem with
  | nil => rfl
  | cons head tail =>
      simp [maximalFactorWord, completionWordOfList, Word.final,
        maximal_getLastD_append]

theorem maximalFactorWord_occurs
    {ambient : Word Nat} {factor before after : List Nat}
    (factorNonempty : factor ≠ [])
    (shape : ambient.toList = before ++ factor ++ after) :
    OccursAsFactor (maximalFactorWord factor) ambient := by
  refine ⟨before, after, ?_⟩
  rw [maximalFactorWord_toList factorNonempty]
  exact shape

theorem directedPathIn_of_occursAsFactor
    {factor ambient : Word Nat}
    (occurs : OccursAsFactor factor ambient) :
    DirectedPathIn ambient factor :=
  ⟨occursAsFactor_support occurs, occursAsFactor_edge occurs⟩

theorem reachableIn_refl_of_mem
    (ambient : Word Nat) {letter : Nat}
    (member : letter ∈ ambient.toList) :
    ReachableIn ambient letter letter := by
  refine ⟨Word.singleton letter, rfl, rfl, ?_⟩
  constructor
  · intro tested testedMember
    have testedEq : tested = letter := by
      simpa [Word.toList] using testedMember
    simpa [testedEq] using member
  · intro source target edge
    simp [Word.singleton, Word.adjacentPairs,
      Word.adjacentPairsFrom] at edge

theorem reachableIn_trans
    {ambient : Word Nat} {source middle target : Nat}
    (first : ReachableIn ambient source middle)
    (second : ReachableIn ambient middle target) :
    ReachableIn ambient source target := by
  rcases first with ⟨left, leftHead, leftFinal, leftIn⟩
  rcases second with ⟨right, rightHead, rightFinal, rightIn⟩
  have boundary : left.final = right.head :=
    leftFinal.trans rightHead.symm
  refine
    ⟨completionJoin left right,
      (completionJoin_head left right).trans leftHead,
      (completionJoin_final boundary).trans rightFinal,
      completionJoin_directedPathIn boundary leftIn rightIn⟩

theorem reachableIn_mono_of_occursAsFactor
    {factor ambient : Word Nat} {source target : Nat}
    (occurs : OccursAsFactor factor ambient)
    (reachable : ReachableIn factor source target) :
    ReachableIn ambient source target := by
  rcases reachable with ⟨path, pathHead, pathFinal, pathIn⟩
  refine ⟨path, pathHead, pathFinal, ?_⟩
  constructor
  · intro letter member
    exact occursAsFactor_support occurs letter (pathIn.1 letter member)
  · intro left right edge
    exact occursAsFactor_edge occurs left right
      (pathIn.2 left right edge)

/-! ## Support-connected words are precisely indecomposable words -/

private def maximalAdjacentPairsList :
    List Nat → List (Nat × Nat)
  | [] => []
  | head :: tail => Word.adjacentPairsFrom head tail

private theorem maximalAdjacentPairsList_word (word : Word Nat) :
    maximalAdjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

private theorem maximalAdjacentPair_support
    {letters : List Nat} {source target : Nat}
    (member :
      (source, target) ∈ maximalAdjacentPairsList letters) :
    source ∈ letters ∧ target ∈ letters := by
  cases letters with
  | nil => simp [maximalAdjacentPairsList] at member
  | cons head tail =>
      change
        (source, target) ∈ Word.adjacentPairsFrom head tail at member
      have represented :
          (source, target) ∈ (Word.mk head tail).adjacentPairs :=
        member
      rcases
          (adjacentPair_mem_iff_exists_toList_split
            source target (Word.mk head tail)).mp represented with
        ⟨before, after, shape⟩
      change head :: tail = before ++ source :: target :: after at shape
      rw [shape]
      simp

private theorem maximal_no_reverse_edge_across_cut
    (leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (disjoint :
      ConnectedComponentSupportsDisjoint
        (leftHead :: leftTail) (rightHead :: rightTail))
    {source target : Nat}
    (sourceRight : source ∈ rightHead :: rightTail)
    (targetLeft : target ∈ leftHead :: leftTail) :
    (source, target) ∉
      maximalAdjacentPairsList
        ((leftHead :: leftTail) ++ rightHead :: rightTail) := by
  intro edge
  change
    (source, target) ∈
      Word.adjacentPairsFrom leftHead
        (leftTail ++ rightHead :: rightTail) at edge
  rw [Word.adjacentPairsFrom_append] at edge
  simp only [List.mem_append, List.mem_cons] at edge
  rcases edge with leftEdge | boundary | rightEdge
  · have sourceLeft : source ∈ leftHead :: leftTail :=
      (maximalAdjacentPair_support
        (letters := leftHead :: leftTail) leftEdge).1
    exact disjoint source sourceLeft sourceRight
  · simp only [Prod.mk.injEq] at boundary
    rcases boundary with ⟨sourceEq, _⟩
    have finalLeft :
        leftTail.getLastD leftHead ∈ leftHead :: leftTail :=
      List.getLastD_mem_cons
    exact disjoint source (by simpa [sourceEq] using finalLeft)
      sourceRight
  · have targetRight : target ∈ rightHead :: rightTail :=
      (maximalAdjacentPair_support
        (letters := rightHead :: rightTail) rightEdge).2
    exact disjoint target targetLeft targetRight

private theorem maximal_exists_path_edge_crossing_cut
    (left right : List Nat)
    (disjoint : ConnectedComponentSupportsDisjoint left right) :
    ∀ (previous : Nat) (tail : List Nat),
      previous ∈ right →
        tail.getLastD previous ∈ left →
          (∀ letter,
            letter ∈ previous :: tail →
              letter ∈ left ∨ letter ∈ right) →
            ∃ source target,
              source ∈ right ∧
                target ∈ left ∧
                  (source, target) ∈
                    Word.adjacentPairsFrom previous tail
  | previous, [], previousRight, finalLeft, _ => by
      exact False.elim (disjoint previous finalLeft previousRight)
  | previous, next :: rest, previousRight, finalLeft, vertices => by
      by_cases nextLeft : next ∈ left
      · exact
          ⟨previous, next, previousRight, nextLeft, by
            simp [Word.adjacentPairsFrom]⟩
      · have nextRight : next ∈ right := by
          rcases vertices next (by simp) with inLeft | inRight
          · exact False.elim (nextLeft inLeft)
          · exact inRight
        have restFinalLeft : rest.getLastD next ∈ left := by
          simpa only [List.getLastD_cons] using finalLeft
        have restVertices :
            ∀ letter,
              letter ∈ next :: rest →
                letter ∈ left ∨ letter ∈ right := by
          intro letter member
          exact vertices letter (List.Mem.tail previous member)
        rcases maximal_exists_path_edge_crossing_cut
            left right disjoint next rest nextRight restFinalLeft
            restVertices with
          ⟨source, target, sourceRight, targetLeft, edge⟩
        exact
          ⟨source, target, sourceRight, targetLeft, by
            simp only [Word.adjacentPairsFrom, List.mem_cons]
            exact Or.inr edge⟩

theorem not_reachableIn_across_disjoint_cut
    (ambient : Word Nat)
    (leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (shape :
      ambient.toList =
        (leftHead :: leftTail) ++ rightHead :: rightTail)
    (disjoint :
      ConnectedComponentSupportsDisjoint
        (leftHead :: leftTail) (rightHead :: rightTail))
    {source target : Nat}
    (sourceRight : source ∈ rightHead :: rightTail)
    (targetLeft : target ∈ leftHead :: leftTail) :
    ¬ReachableIn ambient source target := by
  rintro ⟨path, pathHead, pathFinal, pathIn⟩
  have pathVertices :
      ∀ letter,
        letter ∈ path.toList →
          letter ∈ leftHead :: leftTail ∨
            letter ∈ rightHead :: rightTail := by
    intro letter member
    have ambientMember := pathIn.1 letter member
    rw [shape, List.mem_append] at ambientMember
    exact ambientMember
  have pathHeadRight : path.head ∈ rightHead :: rightTail := by
    rw [pathHead]
    exact sourceRight
  have pathFinalLeft :
      path.tail.getLastD path.head ∈ leftHead :: leftTail := by
    change path.final ∈ leftHead :: leftTail
    rw [pathFinal]
    exact targetLeft
  rcases maximal_exists_path_edge_crossing_cut
      (leftHead :: leftTail) (rightHead :: rightTail) disjoint
      path.head path.tail pathHeadRight pathFinalLeft pathVertices with
    ⟨edgeSource, edgeTarget, edgeSourceRight, edgeTargetLeft,
      pathEdge⟩
  have ambientEdge :
      (edgeSource, edgeTarget) ∈ ambient.adjacentPairs :=
    pathIn.2 edgeSource edgeTarget pathEdge
  have listEdge :
      (edgeSource, edgeTarget) ∈
        maximalAdjacentPairsList
          ((leftHead :: leftTail) ++ rightHead :: rightTail) := by
    rw [← shape, maximalAdjacentPairsList_word]
    exact ambientEdge
  exact maximal_no_reverse_edge_across_cut
    leftHead rightHead leftTail rightTail disjoint
      edgeSourceRight edgeTargetLeft listEdge

theorem reachableIn_reverse_across_supportConnected_cut
    (ambient : Word Nat)
    (leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (shape :
      ambient.toList =
        (leftHead :: leftTail) ++ rightHead :: rightTail)
    (connected :
      ConnectedComponentSupportConnected ambient.toList) :
    ReachableIn ambient rightHead (leftTail.getLastD leftHead) := by
  rcases connected (leftHead :: leftTail) (rightHead :: rightTail)
      shape (by simp) (by simp) with
    ⟨anchor, anchorLeft, anchorRight⟩
  rcases List.mem_iff_append.mp anchorLeft with
    ⟨leftBefore, leftAfter, leftShape⟩
  rcases List.mem_iff_append.mp anchorRight with
    ⟨rightBefore, rightAfter, rightShape⟩
  let rightPrefix := rightBefore ++ [anchor]
  let leftSuffix := anchor :: leftAfter
  have rightPrefixNonempty : rightPrefix ≠ [] := by
    simp [rightPrefix]
  have leftSuffixNonempty : leftSuffix ≠ [] := by
    simp [leftSuffix]
  have rightFactorShape :
      ambient.toList =
        (leftHead :: leftTail) ++ rightPrefix ++ rightAfter := by
    rw [shape, rightShape]
    simp [rightPrefix, List.append_assoc]
  have leftFactorShape :
      ambient.toList = leftBefore ++ leftSuffix ++
        (rightHead :: rightTail) := by
    rw [shape, leftShape]
  have rightPathIn :
      DirectedPathIn ambient (maximalFactorWord rightPrefix) :=
    directedPathIn_of_occursAsFactor <|
      maximalFactorWord_occurs
        (before := leftHead :: leftTail) (after := rightAfter)
        rightPrefixNonempty rightFactorShape
  have leftPathIn :
      DirectedPathIn ambient (maximalFactorWord leftSuffix) :=
    directedPathIn_of_occursAsFactor <|
      maximalFactorWord_occurs
        (before := leftBefore) (after := rightHead :: rightTail)
        leftSuffixNonempty leftFactorShape
  have rightPathHead :
      (maximalFactorWord rightPrefix).head = rightHead := by
    have rightCombined :
        rightPrefix ++ rightAfter = rightHead :: rightTail := by
      rw [rightShape]
      simp [rightPrefix, List.append_assoc]
    have prefixHead :=
      maximalFactorWord_head_of_prefix
        (stem := rightPrefix) (suffix := rightAfter)
        rightPrefixNonempty
    rw [rightCombined] at prefixHead
    simpa [maximalFactorWord, completionWordOfList] using prefixHead.symm
  have rightPathFinal :
      (maximalFactorWord rightPrefix).final = anchor := by
    simpa [rightPrefix] using
      maximalFactorWord_final_append_singleton rightBefore anchor
  have leftPathHead :
      (maximalFactorWord leftSuffix).head = anchor :=
    rfl
  have leftPathFinal :
      (maximalFactorWord leftSuffix).final =
        leftTail.getLastD leftHead := by
    have leftCombined :
        leftBefore ++ leftSuffix = leftHead :: leftTail := by
      rw [leftShape]
    have suffixFinal :=
      maximalFactorWord_final_of_suffix
        (stem := leftBefore) (suffix := leftSuffix)
        leftSuffixNonempty
    rw [leftCombined] at suffixFinal
    simpa [maximalFactorWord, completionWordOfList, Word.final] using
      suffixFinal.symm
  exact reachableIn_trans
    ⟨maximalFactorWord rightPrefix, rightPathHead,
      rightPathFinal, rightPathIn⟩
    ⟨maximalFactorWord leftSuffix, leftPathHead,
      leftPathFinal, leftPathIn⟩

theorem reachableIn_from_initial_of_mem
    (ambient : Word Nat) {target : Nat}
    (targetMember : target ∈ ambient.toList) :
    ReachableIn ambient ambient.head target := by
  rcases List.mem_iff_append.mp targetMember with
    ⟨before, after, shape⟩
  let stem := before ++ [target]
  have prefixNonempty : stem ≠ [] := by simp [stem]
  have factorShape : ambient.toList = [] ++ stem ++ after := by
    simpa [stem, List.append_assoc] using shape
  have pathIn : DirectedPathIn ambient (maximalFactorWord stem) :=
    directedPathIn_of_occursAsFactor <|
      maximalFactorWord_occurs
        (before := []) (after := after) prefixNonempty factorShape
  have pathHead : (maximalFactorWord stem).head = ambient.head := by
    have prefixCombined : stem ++ after = ambient.toList := by
      rw [shape]
      simp [stem, List.append_assoc]
    have prefixHead :=
      maximalFactorWord_head_of_prefix
        (stem := stem) (suffix := after) prefixNonempty
    rw [prefixCombined] at prefixHead
    simpa [maximalFactorWord, completionWordOfList,
      Word.toList] using prefixHead.symm
  have pathFinal : (maximalFactorWord stem).final = target := by
    simpa [stem] using
      maximalFactorWord_final_append_singleton before target
  exact ⟨maximalFactorWord stem, pathHead, pathFinal, pathIn⟩

private theorem supportConnected_position_reaches_initial
    (ambient : Word Nat)
    (connected :
      ConnectedComponentSupportConnected ambient.toList) :
    ∀ before current after,
      ambient.toList = before ++ current :: after →
        ReachableIn ambient current ambient.head := by
  let inductionStatement :
      ∀ length,
        (∀ smaller < length,
          ∀ before current after,
            before.length = smaller →
              ambient.toList = before ++ current :: after →
                ReachableIn ambient current ambient.head) →
          ∀ before current after,
            before.length = length →
              ambient.toList = before ++ current :: after →
                ReachableIn ambient current ambient.head := by
    intro length smaller before current after lengthEq shape
    by_cases beforeEmpty : before = []
    · subst before
      have initialEq : ambient.head = current := by
        have heads := congrArg List.head? shape
        simpa [Word.toList] using heads
      rw [← initialEq]
      exact reachableIn_refl_of_mem ambient (by simp [Word.toList])
    · cases before with
      | nil => contradiction
      | cons first rest =>
          let previous := rest.getLastD first
          let earlier := (first :: rest).dropLast
          have rebuild : earlier ++ [previous] = first :: rest := by
            exact maximal_dropLast_append_getLastD first rest
          have earlierLength : earlier.length < length := by
            have dropLength :
                earlier.length + 1 = (first :: rest).length := by
              have lengths := congrArg List.length rebuild
              simpa [earlier] using lengths
            simpa [lengthEq] using (show earlier.length <
              (first :: rest).length by omega)
          have recursiveShape :
              ambient.toList =
                earlier ++ previous :: current :: after := by
            calc
              ambient.toList =
                  (first :: rest) ++ current :: after := shape
              _ = (earlier ++ [previous]) ++ current :: after := by
                rw [rebuild]
              _ = earlier ++ previous :: current :: after := by
                simp [List.append_assoc]
          have currentPrevious :
              ReachableIn ambient current previous :=
            reachableIn_reverse_across_supportConnected_cut ambient
              first current rest after shape connected
          have previousInitial :
              ReachableIn ambient previous ambient.head :=
            smaller earlier.length earlierLength earlier previous
              (current :: after) rfl recursiveShape
          exact reachableIn_trans currentPrevious previousInitial
  intro before current after shape
  exact
    Nat.strongRecOn
      (motive := fun length =>
        ∀ before current after,
          before.length = length →
            ambient.toList = before ++ current :: after →
              ReachableIn ambient current ambient.head)
      before.length inductionStatement before current after rfl shape

/-- Every cut-overlap component is strongly connected in the directed
adjacency graph read from the word. -/
theorem trahtmanIndecomposable_of_supportConnected
    (word : Word Nat)
    (connected : ConnectedComponentSupportConnected word.toList) :
    TrahtmanIndecomposable word := by
  intro source sourceMember target targetMember
  rcases List.mem_iff_append.mp sourceMember with
    ⟨before, after, sourceShape⟩
  have sourceInitial : ReachableIn word source word.head :=
    supportConnected_position_reaches_initial word connected
      before source after sourceShape
  have initialTarget : ReachableIn word word.head target :=
    reachableIn_from_initial_of_mem word targetMember
  exact reachableIn_trans sourceInitial initialTarget

/-- Strong connectivity forces every nontrivial displayed cut to overlap. -/
theorem supportConnected_of_trahtmanIndecomposable
    (word : Word Nat)
    (indecomposable : TrahtmanIndecomposable word) :
    ConnectedComponentSupportConnected word.toList := by
  intro left right shape leftNonempty rightNonempty
  cases left with
  | nil => contradiction
  | cons leftHead leftTail =>
      cases right with
      | nil => contradiction
      | cons rightHead rightTail =>
          exact indecomposable_split_support_overlap word
            leftHead rightHead leftTail rightTail shape indecomposable

theorem supportConnected_iff_trahtmanIndecomposable
    (word : Word Nat) :
    ConnectedComponentSupportConnected word.toList ↔
      TrahtmanIndecomposable word :=
  ⟨trahtmanIndecomposable_of_supportConnected word,
    supportConnected_of_trahtmanIndecomposable word⟩

/-! ## Deterministic maximal indecomposable factorization -/

/-- A maximal factorization is a literal factor chain whose factors are
nonempty and indecomposable and whose supports are pairwise disjoint. For a
walk, disjointness is exactly maximality: two adjacent factors cannot merge
into one indecomposable factor. -/
structure MaximalIndecomposableFactorization
    (word : Word Nat) (factors : List (List Nat)) : Prop where
  flatten_eq : factors.flatten = word.toList
  nonempty : ∀ factor, factor ∈ factors → factor ≠ []
  pairwiseDisjoint :
    factors.Pairwise ConnectedComponentSupportsDisjoint
  indecomposable :
    ∀ factor, factor ∈ factors →
      TrahtmanIndecomposable (maximalFactorWord factor)

/-- The existing deterministic support scanner is the maximal
indecomposable factor chain required by Trahtman's argument. -/
theorem connectedComponentDecomposeWord_maximalFactorization
    (word : Word Nat) :
    MaximalIndecomposableFactorization word
      (connectedComponentDecomposeWord word) := by
  refine
    { flatten_eq := connectedComponentDecomposeWord_flatten word
      nonempty := connectedComponentDecomposeWord_nonempty_components word
      pairwiseDisjoint :=
        connectedComponentDecomposeWord_pairwiseDisjoint word
      indecomposable := ?_ }
  intro factor member
  have factorNonempty :=
    connectedComponentDecomposeWord_nonempty_components word
      factor member
  apply trahtmanIndecomposable_of_supportConnected
  rw [maximalFactorWord_toList factorNonempty]
  exact connectedComponentDecomposeWord_supportConnected word factor member

/-- Pairwise disjoint neighboring factors are genuinely maximal: their
concatenation is not indecomposable. -/
theorem MaximalIndecomposableFactorization.adjacent_maximal
    {word : Word Nat} {factors before after : List (List Nat)}
    {left right : List Nat}
    (factorization :
      MaximalIndecomposableFactorization word factors)
    (shape : factors = before ++ left :: right :: after) :
    ¬TrahtmanIndecomposable (maximalFactorWord (left ++ right)) := by
  intro indecomposable
  have supportConnected :
      ConnectedComponentSupportConnected (left ++ right) := by
    have converted :=
      supportConnected_of_trahtmanIndecomposable
        (maximalFactorWord (left ++ right)) indecomposable
    have leftNonempty : left ≠ [] :=
      factorization.nonempty left (by rw [shape]; simp)
    have rightNonempty : right ≠ [] :=
      factorization.nonempty right (by rw [shape]; simp)
    have joinedNonempty : left ++ right ≠ [] := by
      intro empty
      exact leftNonempty (List.append_eq_nil_iff.mp empty).1
    rw [maximalFactorWord_toList joinedNonempty] at converted
    exact converted
  have pairwise := factorization.pairwiseDisjoint
  rw [shape] at pairwise
  have tailPairwise :
      (left :: right :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have disjoint : ConnectedComponentSupportsDisjoint left right :=
    (List.pairwise_cons.mp tailPairwise).1 right (by simp)
  exact connectedComponentAppend_not_supportConnected
    (factorization.nonempty left (by rw [shape]; simp))
    (factorization.nonempty right (by rw [shape]; simp))
    disjoint supportConnected

/-! ## The strongly connected class carried by the first factor -/

/-- Mutual reachability in the directed adjacency graph. -/
def MutuallyReachableIn
    (ambient : Word Nat) (left right : Nat) : Prop :=
  ReachableIn ambient left right ∧ ReachableIn ambient right left

theorem mutuallyReachableIn_iff_of_sameMarkedDigraph
    {left right : Word Nat} {source target : Nat}
    (same : left.SameMarkedDigraph right) :
    MutuallyReachableIn left source target ↔
      MutuallyReachableIn right source target := by
  constructor
  · rintro ⟨forward, backward⟩
    exact
      ⟨(reachableIn_iff_of_sameMarkedDigraph same).mp forward,
        (reachableIn_iff_of_sameMarkedDigraph same).mp backward⟩
  · rintro ⟨forward, backward⟩
    exact
      ⟨(reachableIn_iff_of_sameMarkedDigraph same).mpr forward,
        (reachableIn_iff_of_sameMarkedDigraph same).mpr backward⟩

private theorem maximal_head_disjoint_flatten
    {head : List Nat} {tail : List (List Nat)}
    (disjoint :
      ∀ factor, factor ∈ tail →
        ConnectedComponentSupportsDisjoint head factor) :
    ConnectedComponentSupportsDisjoint head tail.flatten := by
  intro tested headMember tailMember
  rcases List.mem_flatten.mp tailMember with
    ⟨factor, factorMember, testedMember⟩
  exact (disjoint factor factorMember tested headMember) testedMember

private theorem maximal_factor_head_mem
    {factor : List Nat} (nonempty : factor ≠ []) :
    (maximalFactorWord factor).head ∈ factor := by
  have member :
      (maximalFactorWord factor).head ∈
        (maximalFactorWord factor).toList := by
    simp [Word.toList]
  rw [maximalFactorWord_toList nonempty] at member
  exact member

private theorem maximal_factor_final_mem
    {factor : List Nat} (nonempty : factor ≠ []) :
    (maximalFactorWord factor).final ∈ factor := by
  rw [← maximalFactorWord_toList nonempty]
  cases maximalFactorWord factor with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem maximal_firstFactor_occurs
    {ambient : Word Nat} {first : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: remaining)) :
    OccursAsFactor (maximalFactorWord first) ambient := by
  have firstNonempty := factorization.nonempty first (by simp)
  exact maximalFactorWord_occurs
    (before := []) (after := remaining.flatten)
    firstNonempty (by simpa using factorization.flatten_eq.symm)

private theorem maximal_firstFactor_head_eq
    {ambient : Word Nat} {first : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: remaining)) :
    (maximalFactorWord first).head = ambient.head := by
  have firstNonempty := factorization.nonempty first (by simp)
  have shape : ambient.toList = first ++ remaining.flatten := by
    simpa using factorization.flatten_eq.symm
  have factorHead :=
    maximalFactorWord_head_of_prefix
      (stem := first) (suffix := remaining.flatten) firstNonempty
  rw [← shape] at factorHead
  have ambientWord : maximalFactorWord ambient.toList = ambient :=
    completionWordOfList_path_toList 0 ambient
  rw [ambientWord] at factorHead
  exact factorHead.symm

/-- The support of the first maximal factor is exactly the strongly connected
class of the ambient marked initial vertex. This is the key fact making the
factor chain intrinsic to the marked graph. -/
theorem firstMaximalFactor_mem_iff_mutuallyReachable
    {ambient : Word Nat} {first : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: remaining))
    (tested : Nat) :
    tested ∈ first ↔
      tested ∈ ambient.toList ∧
        MutuallyReachableIn ambient ambient.head tested := by
  have firstNonempty := factorization.nonempty first (by simp)
  have ambientShape :
      ambient.toList = first ++ remaining.flatten := by
    simpa using factorization.flatten_eq.symm
  have firstOccurs := maximal_firstFactor_occurs factorization
  have firstHead := maximal_firstFactor_head_eq factorization
  have firstIndecomposable :=
    factorization.indecomposable first (by simp)
  have pairwise := factorization.pairwiseDisjoint
  rw [List.pairwise_cons] at pairwise
  have firstTailDisjoint :
      ConnectedComponentSupportsDisjoint first remaining.flatten :=
    maximal_head_disjoint_flatten pairwise.1
  constructor
  · intro testedFirst
    have testedAmbient : tested ∈ ambient.toList := by
      rw [ambientShape]
      exact List.mem_append_left _ testedFirst
    have factorHeadMember :
        (maximalFactorWord first).head ∈
          (maximalFactorWord first).toList := by
      simp [Word.toList]
    have testedFactor :
        tested ∈ (maximalFactorWord first).toList := by
      rwa [maximalFactorWord_toList firstNonempty]
    have forwardFactor :=
      firstIndecomposable
        (maximalFactorWord first).head factorHeadMember
        tested testedFactor
    have backwardFactor :=
      firstIndecomposable tested testedFactor
        (maximalFactorWord first).head factorHeadMember
    have forwardAmbient :=
      reachableIn_mono_of_occursAsFactor firstOccurs forwardFactor
    have backwardAmbient :=
      reachableIn_mono_of_occursAsFactor firstOccurs backwardFactor
    rw [firstHead] at forwardAmbient backwardAmbient
    exact ⟨testedAmbient, forwardAmbient, backwardAmbient⟩
  · rintro ⟨testedAmbient, _, testedInitial⟩
    rw [ambientShape, List.mem_append] at testedAmbient
    rcases testedAmbient with testedFirst | testedTail
    · exact testedFirst
    · cases tailShape : remaining.flatten with
      | nil =>
          rw [tailShape] at testedTail
          simp at testedTail
      | cons tailHead tailRest =>
          rw [tailShape] at testedTail
          have ambientCut :
              ambient.toList = first ++ tailHead :: tailRest := by
            rw [ambientShape, tailShape]
          have firstShape := List.exists_cons_of_ne_nil firstNonempty
          rcases firstShape with ⟨firstHeadLetter, firstTail, rfl⟩
          have ambientInitialFirst :
              ambient.head ∈ firstHeadLetter :: firstTail := by
            rw [← firstHead]
            exact maximal_factor_head_mem (by simp)
          have cutDisjoint :
              ConnectedComponentSupportsDisjoint
                (firstHeadLetter :: firstTail)
                (tailHead :: tailRest) := by
            simpa [tailShape] using firstTailDisjoint
          exact False.elim <|
            (not_reachableIn_across_disjoint_cut ambient
              firstHeadLetter tailHead firstTail tailRest ambientCut
              cutDisjoint testedTail ambientInitialFirst) testedInitial

/-- Equal marked graphs have first maximal factors with equal supports; no
factor correspondence is assumed. -/
theorem firstMaximalFactors_sameSupport
    {left right : Word Nat}
    {leftFirst rightFirst : List Nat}
    {leftRemaining rightRemaining : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left
        (leftFirst :: leftRemaining))
    (rightFactorization :
      MaximalIndecomposableFactorization right
        (rightFirst :: rightRemaining))
    (tested : Nat) :
    tested ∈ leftFirst ↔ tested ∈ rightFirst := by
  rw [firstMaximalFactor_mem_iff_mutuallyReachable
      leftFactorization tested,
    firstMaximalFactor_mem_iff_mutuallyReachable
      rightFactorization tested]
  constructor
  · rintro ⟨member, forward, backward⟩
    have rightMember := (same.support tested).mp member
    have rightForward : ReachableIn right right.head tested := by
      have transferred :=
        (reachableIn_iff_of_sameMarkedDigraph same).mp forward
      rwa [same.initial] at transferred
    have rightBackward : ReachableIn right tested right.head := by
      have transferred :=
        (reachableIn_iff_of_sameMarkedDigraph same).mp backward
      rwa [same.initial] at transferred
    exact ⟨rightMember, rightForward, rightBackward⟩
  · rintro ⟨member, forward, backward⟩
    have leftMember := (same.support tested).mpr member
    have leftForward : ReachableIn left left.head tested := by
      have transferred :=
        (reachableIn_iff_of_sameMarkedDigraph same).mpr forward
      rwa [← same.initial] at transferred
    have leftBackward : ReachableIn left tested left.head := by
      have transferred :=
        (reachableIn_iff_of_sameMarkedDigraph same).mpr backward
      rwa [← same.initial] at transferred
    exact ⟨leftMember, leftForward, leftBackward⟩

/-! ## Restricting the ambient graph to the first factor or its suffix -/

private theorem maximal_word_eq_factor_append
    {ambient : Word Nat} {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (shape : ambient.toList = left ++ right) :
    ambient = maximalFactorWord left ++ maximalFactorWord right := by
  apply Word.toList_injective
  rw [Word.toList_append,
    maximalFactorWord_toList leftNonempty,
    maximalFactorWord_toList rightNonempty]
  exact shape

private theorem maximal_adjacentPair_support_word
    {word : Word Nat} {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    source ∈ word.toList ∧ target ∈ word.toList := by
  rcases
      (adjacentPair_mem_iff_exists_toList_split
        source target word).mp edge with
    ⟨before, after, shape⟩
  rw [shape]
  simp

theorem edgeInFirstFactor_of_ambient
    {ambient : Word Nat} {first remaining : List Nat}
    (firstNonempty : first ≠ [])
    (shape : ambient.toList = first ++ remaining)
    (disjoint :
      ConnectedComponentSupportsDisjoint first remaining)
    {source target : Nat}
    (sourceFirst : source ∈ first)
    (targetFirst : target ∈ first)
    (edge : (source, target) ∈ ambient.adjacentPairs) :
    (source, target) ∈ (maximalFactorWord first).adjacentPairs := by
  cases remaining with
  | nil =>
      have ambientEq : ambient = maximalFactorWord first := by
        apply Word.toList_injective
        rw [maximalFactorWord_toList firstNonempty]
        simpa using shape
      rwa [ambientEq] at edge
  | cons rightHead rightTail =>
      have ambientEq :=
        maximal_word_eq_factor_append firstNonempty (by simp)
          shape
      rw [ambientEq, Word.adjacentPairs_append] at edge
      simp only [List.mem_append, List.mem_cons] at edge
      rcases edge with firstEdge | boundary | remainingEdge
      · exact firstEdge
      · simp only [Prod.mk.injEq] at boundary
        rcases boundary with ⟨_, targetEq⟩
        have targetRemaining : target ∈ rightHead :: rightTail := by
          rw [targetEq]
          simp [maximalFactorWord, completionWordOfList]
        exact False.elim (disjoint target targetFirst targetRemaining)
      · have sourceRemainingWord :=
          (maximal_adjacentPair_support_word remainingEdge).1
        have sourceRemaining : source ∈ rightHead :: rightTail := by
          rw [maximalFactorWord_toList (by simp)] at sourceRemainingWord
          exact sourceRemainingWord
        exact False.elim (disjoint source sourceFirst sourceRemaining)

theorem edgeInSuffixFactor_of_ambient
    {ambient : Word Nat} {first suffix : List Nat}
    (firstNonempty : first ≠ []) (suffixNonempty : suffix ≠ [])
    (shape : ambient.toList = first ++ suffix)
    (disjoint : ConnectedComponentSupportsDisjoint first suffix)
    {source target : Nat}
    (sourceSuffix : source ∈ suffix)
    (targetSuffix : target ∈ suffix)
    (edge : (source, target) ∈ ambient.adjacentPairs) :
    (source, target) ∈ (maximalFactorWord suffix).adjacentPairs := by
  have ambientEq :=
    maximal_word_eq_factor_append firstNonempty suffixNonempty shape
  rw [ambientEq, Word.adjacentPairs_append] at edge
  simp only [List.mem_append, List.mem_cons] at edge
  rcases edge with firstEdge | boundary | suffixEdge
  · have targetFirstWord :=
      (maximal_adjacentPair_support_word firstEdge).2
    have targetFirst : target ∈ first := by
      rw [maximalFactorWord_toList firstNonempty] at targetFirstWord
      exact targetFirstWord
    exact False.elim (disjoint target targetFirst targetSuffix)
  · simp only [Prod.mk.injEq] at boundary
    rcases boundary with ⟨sourceEq, _⟩
    have sourceFirst : source ∈ first := by
      rw [sourceEq]
      exact maximal_factor_final_mem firstNonempty
    exact False.elim (disjoint source sourceFirst sourceSuffix)
  · exact suffixEdge

theorem crossEdge_unique
    {ambient : Word Nat} {first suffix : List Nat}
    (firstNonempty : first ≠ []) (suffixNonempty : suffix ≠ [])
    (shape : ambient.toList = first ++ suffix)
    (disjoint : ConnectedComponentSupportsDisjoint first suffix)
    {source target : Nat}
    (sourceFirst : source ∈ first)
    (targetSuffix : target ∈ suffix)
    (edge : (source, target) ∈ ambient.adjacentPairs) :
    source = (maximalFactorWord first).final ∧
      target = (maximalFactorWord suffix).head := by
  have ambientEq :=
    maximal_word_eq_factor_append firstNonempty suffixNonempty shape
  rw [ambientEq, Word.adjacentPairs_append] at edge
  simp only [List.mem_append, List.mem_cons] at edge
  rcases edge with firstEdge | boundary | suffixEdge
  · have targetFirstWord :=
      (maximal_adjacentPair_support_word firstEdge).2
    have targetFirst : target ∈ first := by
      rw [maximalFactorWord_toList firstNonempty] at targetFirstWord
      exact targetFirstWord
    exact False.elim (disjoint target targetFirst targetSuffix)
  · simpa only [Prod.mk.injEq] using boundary
  · have sourceSuffixWord :=
      (maximal_adjacentPair_support_word suffixEdge).1
    have sourceSuffix : source ∈ suffix := by
      rw [maximalFactorWord_toList suffixNonempty] at sourceSuffixWord
      exact sourceSuffixWord
    exact False.elim (disjoint source sourceFirst sourceSuffix)

theorem boundaryEdge_mem_ambient
    {ambient : Word Nat} {first suffix : List Nat}
    (firstNonempty : first ≠ []) (suffixNonempty : suffix ≠ [])
    (shape : ambient.toList = first ++ suffix) :
    ((maximalFactorWord first).final,
        (maximalFactorWord suffix).head) ∈
      ambient.adjacentPairs := by
  have ambientEq :=
    maximal_word_eq_factor_append firstNonempty suffixNonempty shape
  rw [ambientEq, Word.adjacentPairs_append]
  simp

/-! ## Ordered factor-chain correspondence -/

private theorem maximal_tailFlatten_nonempty
    {ambient : Word Nat} {first second : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: second :: remaining)) :
    (second :: remaining).flatten ≠ [] := by
  intro flattenedEmpty
  have secondEmpty : second = [] :=
    (List.append_eq_nil_iff.mp (by
      simpa only [List.flatten_cons] using flattenedEmpty)).1
  exact
    (factorization.nonempty second (by simp)) secondEmpty

private theorem maximal_firstTail_disjoint
    {ambient : Word Nat} {first : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: remaining)) :
    ConnectedComponentSupportsDisjoint first remaining.flatten := by
  have pairwise := factorization.pairwiseDisjoint
  rw [List.pairwise_cons] at pairwise
  exact maximal_head_disjoint_flatten pairwise.1

private theorem maximal_factorization_shape
    {ambient : Word Nat} {first : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: remaining)) :
    ambient.toList = first ++ remaining.flatten := by
  simpa using factorization.flatten_eq.symm

private theorem maximal_tailFactorization
    {ambient : Word Nat} {first second : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: second :: remaining)) :
    MaximalIndecomposableFactorization
      (maximalFactorWord (second :: remaining).flatten)
      (second :: remaining) := by
  have tailNonempty := maximal_tailFlatten_nonempty factorization
  refine
    { flatten_eq := (maximalFactorWord_toList tailNonempty).symm
      nonempty := ?_
      pairwiseDisjoint := ?_
      indecomposable := ?_ }
  · intro factor member
    exact factorization.nonempty factor (by simp [member])
  · exact (List.pairwise_cons.mp factorization.pairwiseDisjoint).2
  · intro factor member
    exact factorization.indecomposable factor (by simp [member])

private theorem maximal_firstFinal_eq_ambient_of_singletonChain
    {ambient : Word Nat} {first : List Nat}
    (factorization :
      MaximalIndecomposableFactorization ambient [first]) :
    (maximalFactorWord first).final = ambient.final := by
  have wordEq : maximalFactorWord first = ambient := by
    apply maximalFactorWord_eq_of_toList
    simpa using factorization.flatten_eq.symm
  rw [wordEq]

private theorem maximal_tailFinal_eq_ambient
    {ambient : Word Nat} {first second : List Nat}
    {remaining : List (List Nat)}
    (factorization :
      MaximalIndecomposableFactorization ambient
        (first :: second :: remaining)) :
    (maximalFactorWord (second :: remaining).flatten).final =
      ambient.final := by
  have firstNonempty := factorization.nonempty first (by simp)
  have tailNonempty := maximal_tailFlatten_nonempty factorization
  have ambientEq :=
    maximal_word_eq_factor_append firstNonempty tailNonempty
      (maximal_factorization_shape factorization)
  rw [ambientEq, Word.final_append]

private theorem maximal_suffixSupport_iff
    {left right : Word Nat}
    {leftFirst rightFirst : List Nat}
    {leftSecond rightSecond : List Nat}
    {leftRemaining rightRemaining : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left
        (leftFirst :: leftSecond :: leftRemaining))
    (rightFactorization :
      MaximalIndecomposableFactorization right
        (rightFirst :: rightSecond :: rightRemaining))
    (firstSupport :
      ∀ tested, tested ∈ leftFirst ↔ tested ∈ rightFirst)
    (tested : Nat) :
    tested ∈ (leftSecond :: leftRemaining).flatten ↔
      tested ∈ (rightSecond :: rightRemaining).flatten := by
  have leftShape := maximal_factorization_shape leftFactorization
  have rightShape := maximal_factorization_shape rightFactorization
  have leftDisjoint := maximal_firstTail_disjoint leftFactorization
  have rightDisjoint := maximal_firstTail_disjoint rightFactorization
  constructor
  · intro leftTail
    have leftWhole : tested ∈ left.toList := by
      rw [leftShape]
      exact List.mem_append_right leftFirst leftTail
    have rightWhole := (same.support tested).mp leftWhole
    rw [rightShape, List.mem_append] at rightWhole
    rcases rightWhole with rightFirstMember | rightTail
    · have leftFirstMember := (firstSupport tested).mpr rightFirstMember
      exact False.elim (leftDisjoint tested leftFirstMember leftTail)
    · exact rightTail
  · intro rightTail
    have rightWhole : tested ∈ right.toList := by
      rw [rightShape]
      exact List.mem_append_right rightFirst rightTail
    have leftWhole := (same.support tested).mpr rightWhole
    rw [leftShape, List.mem_append] at leftWhole
    rcases leftWhole with leftFirstMember | leftTail
    · have rightFirstMember := (firstSupport tested).mp leftFirstMember
      exact False.elim (rightDisjoint tested rightFirstMember rightTail)
    · exact leftTail

private theorem maximal_boundaryAlignment
    {left right : Word Nat}
    {leftFirst rightFirst : List Nat}
    {leftSecond rightSecond : List Nat}
    {leftRemaining rightRemaining : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left
        (leftFirst :: leftSecond :: leftRemaining))
    (rightFactorization :
      MaximalIndecomposableFactorization right
        (rightFirst :: rightSecond :: rightRemaining))
    (firstSupport :
      ∀ tested, tested ∈ leftFirst ↔ tested ∈ rightFirst) :
    (maximalFactorWord leftFirst).final =
        (maximalFactorWord rightFirst).final ∧
      (maximalFactorWord (leftSecond :: leftRemaining).flatten).head =
        (maximalFactorWord
          (rightSecond :: rightRemaining).flatten).head := by
  have leftFirstNonempty := leftFactorization.nonempty leftFirst (by simp)
  have rightFirstNonempty := rightFactorization.nonempty rightFirst (by simp)
  have leftTailNonempty := maximal_tailFlatten_nonempty leftFactorization
  have rightTailNonempty := maximal_tailFlatten_nonempty rightFactorization
  have leftShape := maximal_factorization_shape leftFactorization
  have rightShape := maximal_factorization_shape rightFactorization
  have leftDisjoint := maximal_firstTail_disjoint leftFactorization
  have rightDisjoint := maximal_firstTail_disjoint rightFactorization
  let source := (maximalFactorWord leftFirst).final
  let target :=
    (maximalFactorWord (leftSecond :: leftRemaining).flatten).head
  have sourceLeft : source ∈ leftFirst :=
    maximal_factor_final_mem leftFirstNonempty
  have targetLeftTail :
      target ∈ (leftSecond :: leftRemaining).flatten :=
    maximal_factor_head_mem leftTailNonempty
  have leftBoundary : (source, target) ∈ left.adjacentPairs :=
    boundaryEdge_mem_ambient leftFirstNonempty leftTailNonempty
      leftShape
  have rightBoundary : (source, target) ∈ right.adjacentPairs :=
    (same.edge source target).mp leftBoundary
  have sourceRight : source ∈ rightFirst :=
    (firstSupport source).mp sourceLeft
  have targetRightWhole : target ∈ right.toList :=
    (same.support target).mp <| by
      rw [leftShape]
      exact List.mem_append_right leftFirst targetLeftTail
  have targetRightTail :
      target ∈ (rightSecond :: rightRemaining).flatten := by
    rw [rightShape, List.mem_append] at targetRightWhole
    rcases targetRightWhole with targetRightFirst | targetRightTail
    · have targetLeftFirst :=
        (firstSupport target).mpr targetRightFirst
      exact False.elim
        (leftDisjoint target targetLeftFirst targetLeftTail)
    · exact targetRightTail
  exact crossEdge_unique rightFirstNonempty rightTailNonempty
    rightShape rightDisjoint sourceRight targetRightTail rightBoundary

private theorem maximal_firstFactors_sameMarkedDigraph
    {left right : Word Nat}
    {leftFirst rightFirst : List Nat}
    {leftRemaining rightRemaining : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left
        (leftFirst :: leftRemaining))
    (rightFactorization :
      MaximalIndecomposableFactorization right
        (rightFirst :: rightRemaining))
    (firstSupport :
      ∀ tested, tested ∈ leftFirst ↔ tested ∈ rightFirst)
    (finalEq :
      (maximalFactorWord leftFirst).final =
        (maximalFactorWord rightFirst).final) :
    (maximalFactorWord leftFirst).SameMarkedDigraph
      (maximalFactorWord rightFirst) := by
  have leftFirstNonempty := leftFactorization.nonempty leftFirst (by simp)
  have rightFirstNonempty := rightFactorization.nonempty rightFirst (by simp)
  have leftShape := maximal_factorization_shape leftFactorization
  have rightShape := maximal_factorization_shape rightFactorization
  have leftDisjoint := maximal_firstTail_disjoint leftFactorization
  have rightDisjoint := maximal_firstTail_disjoint rightFactorization
  have initialEq :
      (maximalFactorWord leftFirst).head =
        (maximalFactorWord rightFirst).head :=
    (maximal_firstFactor_head_eq leftFactorization).trans <|
      same.initial.trans
        (maximal_firstFactor_head_eq rightFactorization).symm
  refine ⟨initialEq, finalEq, ?_, ?_⟩
  · intro tested
    rw [maximalFactorWord_toList leftFirstNonempty,
      maximalFactorWord_toList rightFirstNonempty]
    exact firstSupport tested
  · intro source target
    constructor
    · intro leftEdge
      have leftAmbient : (source, target) ∈ left.adjacentPairs :=
        occursAsFactor_edge
          (maximal_firstFactor_occurs leftFactorization)
          source target leftEdge
      have rightAmbient := (same.edge source target).mp leftAmbient
      have sourceLeftWord :=
        (maximal_adjacentPair_support_word leftEdge).1
      have targetLeftWord :=
        (maximal_adjacentPair_support_word leftEdge).2
      have sourceLeft : source ∈ leftFirst := by
        rw [maximalFactorWord_toList leftFirstNonempty] at sourceLeftWord
        exact sourceLeftWord
      have targetLeft : target ∈ leftFirst := by
        rw [maximalFactorWord_toList leftFirstNonempty] at targetLeftWord
        exact targetLeftWord
      exact edgeInFirstFactor_of_ambient rightFirstNonempty rightShape
        rightDisjoint ((firstSupport source).mp sourceLeft)
        ((firstSupport target).mp targetLeft) rightAmbient
    · intro rightEdge
      have rightAmbient : (source, target) ∈ right.adjacentPairs :=
        occursAsFactor_edge
          (maximal_firstFactor_occurs rightFactorization)
          source target rightEdge
      have leftAmbient := (same.edge source target).mpr rightAmbient
      have sourceRightWord :=
        (maximal_adjacentPair_support_word rightEdge).1
      have targetRightWord :=
        (maximal_adjacentPair_support_word rightEdge).2
      have sourceRight : source ∈ rightFirst := by
        rw [maximalFactorWord_toList rightFirstNonempty] at sourceRightWord
        exact sourceRightWord
      have targetRight : target ∈ rightFirst := by
        rw [maximalFactorWord_toList rightFirstNonempty] at targetRightWord
        exact targetRightWord
      exact edgeInFirstFactor_of_ambient leftFirstNonempty leftShape
        leftDisjoint ((firstSupport source).mpr sourceRight)
        ((firstSupport target).mpr targetRight) leftAmbient

private theorem maximal_suffixes_sameMarkedDigraph
    {left right : Word Nat}
    {leftFirst rightFirst : List Nat}
    {leftSecond rightSecond : List Nat}
    {leftRemaining rightRemaining : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left
        (leftFirst :: leftSecond :: leftRemaining))
    (rightFactorization :
      MaximalIndecomposableFactorization right
        (rightFirst :: rightSecond :: rightRemaining))
    (firstSupport :
      ∀ tested, tested ∈ leftFirst ↔ tested ∈ rightFirst)
    (initialEq :
      (maximalFactorWord (leftSecond :: leftRemaining).flatten).head =
        (maximalFactorWord
          (rightSecond :: rightRemaining).flatten).head) :
    (maximalFactorWord
      (leftSecond :: leftRemaining).flatten).SameMarkedDigraph
      (maximalFactorWord
        (rightSecond :: rightRemaining).flatten) := by
  have leftFirstNonempty := leftFactorization.nonempty leftFirst (by simp)
  have rightFirstNonempty := rightFactorization.nonempty rightFirst (by simp)
  have leftTailNonempty := maximal_tailFlatten_nonempty leftFactorization
  have rightTailNonempty := maximal_tailFlatten_nonempty rightFactorization
  have leftShape := maximal_factorization_shape leftFactorization
  have rightShape := maximal_factorization_shape rightFactorization
  have leftDisjoint := maximal_firstTail_disjoint leftFactorization
  have rightDisjoint := maximal_firstTail_disjoint rightFactorization
  have tailSupport := maximal_suffixSupport_iff same leftFactorization
    rightFactorization firstSupport
  have finalEq :
      (maximalFactorWord (leftSecond :: leftRemaining).flatten).final =
        (maximalFactorWord
          (rightSecond :: rightRemaining).flatten).final :=
    (maximal_tailFinal_eq_ambient leftFactorization).trans <|
      same.final.trans
        (maximal_tailFinal_eq_ambient rightFactorization).symm
  refine ⟨initialEq, finalEq, ?_, ?_⟩
  · intro tested
    rw [maximalFactorWord_toList leftTailNonempty,
      maximalFactorWord_toList rightTailNonempty]
    exact tailSupport tested
  · intro source target
    constructor
    · intro leftEdge
      have leftOccurs :
          OccursAsFactor
            (maximalFactorWord
              (leftSecond :: leftRemaining).flatten) left :=
        maximalFactorWord_occurs
          (before := leftFirst) (after := [])
          leftTailNonempty <| by
            simpa using leftShape
      have leftAmbient : (source, target) ∈ left.adjacentPairs :=
        occursAsFactor_edge leftOccurs source target leftEdge
      have rightAmbient := (same.edge source target).mp leftAmbient
      have sourceLeftWord :=
        (maximal_adjacentPair_support_word leftEdge).1
      have targetLeftWord :=
        (maximal_adjacentPair_support_word leftEdge).2
      have sourceLeftTail :
          source ∈ (leftSecond :: leftRemaining).flatten := by
        rw [maximalFactorWord_toList leftTailNonempty] at sourceLeftWord
        exact sourceLeftWord
      have targetLeftTail :
          target ∈ (leftSecond :: leftRemaining).flatten := by
        rw [maximalFactorWord_toList leftTailNonempty] at targetLeftWord
        exact targetLeftWord
      exact edgeInSuffixFactor_of_ambient
        rightFirstNonempty rightTailNonempty rightShape rightDisjoint
        ((tailSupport source).mp sourceLeftTail)
        ((tailSupport target).mp targetLeftTail) rightAmbient
    · intro rightEdge
      have rightOccurs :
          OccursAsFactor
            (maximalFactorWord
              (rightSecond :: rightRemaining).flatten) right :=
        maximalFactorWord_occurs
          (before := rightFirst) (after := [])
          rightTailNonempty <| by
            simpa using rightShape
      have rightAmbient : (source, target) ∈ right.adjacentPairs :=
        occursAsFactor_edge rightOccurs source target rightEdge
      have leftAmbient := (same.edge source target).mpr rightAmbient
      have sourceRightWord :=
        (maximal_adjacentPair_support_word rightEdge).1
      have targetRightWord :=
        (maximal_adjacentPair_support_word rightEdge).2
      have sourceRightTail :
          source ∈ (rightSecond :: rightRemaining).flatten := by
        rw [maximalFactorWord_toList rightTailNonempty] at sourceRightWord
        exact sourceRightWord
      have targetRightTail :
          target ∈ (rightSecond :: rightRemaining).flatten := by
        rw [maximalFactorWord_toList rightTailNonempty] at targetRightWord
        exact targetRightWord
      exact edgeInSuffixFactor_of_ambient
        leftFirstNonempty leftTailNonempty leftShape leftDisjoint
        ((tailSupport source).mpr sourceRightTail)
        ((tailSupport target).mpr targetRightTail) leftAmbient

/-- Componentwise equality of the marked graphs in two ordered factor
chains. -/
def SameMarkedFactorChains :
    List (List Nat) → List (List Nat) → Prop
  | [], [] => True
  | left :: leftRemaining, right :: rightRemaining =>
      (maximalFactorWord left).SameMarkedDigraph
          (maximalFactorWord right) ∧
        SameMarkedFactorChains leftRemaining rightRemaining
  | _, _ => False

/-- The maximal-factor correspondence asserted in Trahtman's paper. It is
derived from marked-graph equality: first supports are SCC classes, the unique
cross-component edge fixes both boundary vertices, and the argument recurses
on the restricted suffix marked graph. -/
theorem sameMarkedFactorChains_of_sameMarkedDigraph
    {left right : Word Nat}
    {leftFactors rightFactors : List (List Nat)}
    (same : left.SameMarkedDigraph right)
    (leftFactorization :
      MaximalIndecomposableFactorization left leftFactors)
    (rightFactorization :
      MaximalIndecomposableFactorization right rightFactors) :
    SameMarkedFactorChains leftFactors rightFactors := by
  induction leftFactors generalizing left right rightFactors with
  | nil =>
      have impossible : left.toList = [] := by
        simpa using leftFactorization.flatten_eq.symm
      have nonempty : left.toList ≠ [] := by simp [Word.toList]
      exact False.elim (nonempty impossible)
  | cons leftFirst leftRemaining induction =>
      cases rightFactors with
      | nil =>
          have impossible : right.toList = [] := by
            simpa using rightFactorization.flatten_eq.symm
          have nonempty : right.toList ≠ [] := by simp [Word.toList]
          exact False.elim (nonempty impossible)
      | cons rightFirst rightRemaining =>
          have firstSupport :=
            firstMaximalFactors_sameSupport same leftFactorization
              rightFactorization
          cases leftRemaining with
          | nil =>
              cases rightRemaining with
              | nil =>
                  have finalEq :
                      (maximalFactorWord leftFirst).final =
                        (maximalFactorWord rightFirst).final :=
                    (maximal_firstFinal_eq_ambient_of_singletonChain
                      leftFactorization).trans <|
                      same.final.trans
                        (maximal_firstFinal_eq_ambient_of_singletonChain
                          rightFactorization).symm
                  exact
                    ⟨maximal_firstFactors_sameMarkedDigraph same
                        leftFactorization rightFactorization
                        firstSupport finalEq,
                      trivial⟩
              | cons rightSecond rightRest =>
                  have rightTailNonempty :=
                    maximal_tailFlatten_nonempty rightFactorization
                  have rightTailHead :
                      (maximalFactorWord
                        (rightSecond :: rightRest).flatten).head ∈
                        (rightSecond :: rightRest).flatten :=
                    maximal_factor_head_mem rightTailNonempty
                  have rightShape :=
                    maximal_factorization_shape rightFactorization
                  have rightWhole :
                      (maximalFactorWord
                        (rightSecond :: rightRest).flatten).head ∈
                        right.toList := by
                    rw [rightShape]
                    exact List.mem_append_right rightFirst rightTailHead
                  have leftWhole :=
                    (same.support
                      (maximalFactorWord
                        (rightSecond :: rightRest).flatten).head).mpr
                      rightWhole
                  have leftOnly :
                      (maximalFactorWord
                        (rightSecond :: rightRest).flatten).head ∈
                        leftFirst := by
                    have leftShape :=
                      maximal_factorization_shape leftFactorization
                    simpa [leftShape] using leftWhole
                  have rightFirstMember :=
                    (firstSupport _).mp leftOnly
                  have rightDisjoint :=
                    maximal_firstTail_disjoint rightFactorization
                  exact False.elim
                    (rightDisjoint _ rightFirstMember rightTailHead)
          | cons leftSecond leftRest =>
              cases rightRemaining with
              | nil =>
                  have leftTailNonempty :=
                    maximal_tailFlatten_nonempty leftFactorization
                  have leftTailHead :
                      (maximalFactorWord
                        (leftSecond :: leftRest).flatten).head ∈
                        (leftSecond :: leftRest).flatten :=
                    maximal_factor_head_mem leftTailNonempty
                  have leftShape :=
                    maximal_factorization_shape leftFactorization
                  have leftWhole :
                      (maximalFactorWord
                        (leftSecond :: leftRest).flatten).head ∈
                        left.toList := by
                    rw [leftShape]
                    exact List.mem_append_right leftFirst leftTailHead
                  have rightWhole :=
                    (same.support
                      (maximalFactorWord
                        (leftSecond :: leftRest).flatten).head).mp
                      leftWhole
                  have rightOnly :
                      (maximalFactorWord
                        (leftSecond :: leftRest).flatten).head ∈
                        rightFirst := by
                    have rightShape :=
                      maximal_factorization_shape rightFactorization
                    simpa [rightShape] using rightWhole
                  have leftFirstMember :=
                    (firstSupport _).mpr rightOnly
                  have leftDisjoint :=
                    maximal_firstTail_disjoint leftFactorization
                  exact False.elim
                    (leftDisjoint _ leftFirstMember leftTailHead)
              | cons rightSecond rightRest =>
                  have boundary :=
                    maximal_boundaryAlignment same leftFactorization
                      rightFactorization firstSupport
                  have firstGraph :=
                    maximal_firstFactors_sameMarkedDigraph same
                      leftFactorization rightFactorization firstSupport
                      boundary.1
                  have tailGraph :=
                    maximal_suffixes_sameMarkedDigraph same
                      leftFactorization rightFactorization firstSupport
                      boundary.2
                  have leftTailFactorization :=
                    maximal_tailFactorization leftFactorization
                  have rightTailFactorization :=
                    maximal_tailFactorization rightFactorization
                  have tailCorrespondence :=
                    induction tailGraph leftTailFactorization
                      rightTailFactorization
                  exact ⟨firstGraph, tailCorrespondence⟩

/-- Specialization of the correspondence theorem to the deterministic
maximal-factor scanner used by the normalization proof. -/
theorem connectedComponentDecompositions_sameMarkedDigraph
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    SameMarkedFactorChains
      (connectedComponentDecomposeWord left)
      (connectedComponentDecomposeWord right) :=
  sameMarkedFactorChains_of_sameMarkedDigraph same
    (connectedComponentDecomposeWord_maximalFactorization left)
    (connectedComponentDecomposeWord_maximalFactorization right)

/-! ## Contextual assembly of the component derivations -/

private theorem derives_of_sameMarkedFactorChains
    (normalize : IndecomposableMarkedDigraphDerivationalCompleteness)
    {left right : Word Nat}
    {leftFactors rightFactors : List (List Nat)}
    (leftFactorization :
      MaximalIndecomposableFactorization left leftFactors)
    (rightFactorization :
      MaximalIndecomposableFactorization right rightFactors)
    (aligned : SameMarkedFactorChains leftFactors rightFactors) :
    Derives basis left right := by
  induction leftFactors generalizing left right rightFactors with
  | nil =>
      have impossible : left.toList = [] := by
        simpa using leftFactorization.flatten_eq.symm
      exact False.elim ((by simp [Word.toList] : left.toList ≠ [])
        impossible)
  | cons leftFirst leftRemaining induction =>
      cases rightFactors with
      | nil =>
          simp [SameMarkedFactorChains] at aligned
      | cons rightFirst rightRemaining =>
          have headGraph := aligned.1
          have headIndecomposable :=
            leftFactorization.indecomposable leftFirst (by simp)
          have headDerivation :
              Derives basis (maximalFactorWord leftFirst)
                (maximalFactorWord rightFirst) :=
            normalize (maximalFactorWord leftFirst)
              (maximalFactorWord rightFirst)
              headIndecomposable headGraph
          cases leftRemaining with
          | nil =>
              cases rightRemaining with
              | nil =>
                  have leftEq : maximalFactorWord leftFirst = left := by
                    apply maximalFactorWord_eq_of_toList
                    simpa using leftFactorization.flatten_eq.symm
                  have rightEq : maximalFactorWord rightFirst = right := by
                    apply maximalFactorWord_eq_of_toList
                    simpa using rightFactorization.flatten_eq.symm
                  simpa [leftEq, rightEq] using headDerivation
              | cons rightSecond rightRest =>
                  simp [SameMarkedFactorChains] at aligned
          | cons leftSecond leftRest =>
              cases rightRemaining with
              | nil =>
                  simp [SameMarkedFactorChains] at aligned
              | cons rightSecond rightRest =>
                  have leftFirstNonempty :=
                    leftFactorization.nonempty leftFirst (by simp)
                  have rightFirstNonempty :=
                    rightFactorization.nonempty rightFirst (by simp)
                  have leftTailNonempty :=
                    maximal_tailFlatten_nonempty leftFactorization
                  have rightTailNonempty :=
                    maximal_tailFlatten_nonempty rightFactorization
                  have leftTailFactorization :=
                    maximal_tailFactorization leftFactorization
                  have rightTailFactorization :=
                    maximal_tailFactorization rightFactorization
                  have tailDerivation :
                      Derives basis
                        (maximalFactorWord
                          (leftSecond :: leftRest).flatten)
                        (maximalFactorWord
                          (rightSecond :: rightRest).flatten) :=
                    induction leftTailFactorization rightTailFactorization
                      aligned.2
                  have replaceHead :=
                    Derives.appendRight headDerivation
                      (maximalFactorWord
                        (leftSecond :: leftRest).flatten)
                  have replaceTail :=
                    Derives.prepend (maximalFactorWord rightFirst)
                      tailDerivation
                  have combined := replaceHead.trans replaceTail
                  have leftEq :
                      left =
                        maximalFactorWord leftFirst ++
                          maximalFactorWord
                            (leftSecond :: leftRest).flatten :=
                    maximal_word_eq_factor_append leftFirstNonempty
                      leftTailNonempty
                      (maximal_factorization_shape
                        leftFactorization)
                  have rightEq :
                      right =
                        maximalFactorWord rightFirst ++
                          maximalFactorWord
                            (rightSecond :: rightRest).flatten :=
                    maximal_word_eq_factor_append rightFirstNonempty
                      rightTailNonempty
                      (maximal_factorization_shape
                        rightFactorization)
                  rw [leftEq, rightEq]
                  exact combined

/-- Public audit surface for contextual append/prepend assembly of an aligned
chain of indecomposable component derivations. -/
theorem derives_of_alignedMaximalFactorChains
    (normalize : IndecomposableMarkedDigraphDerivationalCompleteness)
    {left right : Word Nat}
    {leftFactors rightFactors : List (List Nat)}
    (leftFactorization :
      MaximalIndecomposableFactorization left leftFactors)
    (rightFactorization :
      MaximalIndecomposableFactorization right rightFactors)
    (aligned : SameMarkedFactorChains leftFactors rightFactors) :
    Derives basis left right :=
  derives_of_sameMarkedFactorChains normalize leftFactorization
    rightFactorization aligned

/-- Trahtman's maximal-factor assembly, now proved rather than supplied as
an assumption. The deterministic decompositions correspond componentwise,
and each component derivation is lifted under its left and right contexts. -/
theorem maximalIndecomposableFactorReduction :
    MaximalIndecomposableFactorReduction := by
  intro normalize left right same
  let leftFactors := connectedComponentDecomposeWord left
  let rightFactors := connectedComponentDecomposeWord right
  have leftFactorization :
      MaximalIndecomposableFactorization left leftFactors := by
    exact connectedComponentDecomposeWord_maximalFactorization left
  have rightFactorization :
      MaximalIndecomposableFactorization right rightFactors := by
    exact connectedComponentDecomposeWord_maximalFactorization right
  have aligned : SameMarkedFactorChains leftFactors rightFactors := by
    exact connectedComponentDecompositions_sameMarkedDigraph same
  exact derives_of_alignedMaximalFactorChains normalize
    leftFactorization rightFactorization aligned

/-! ## Unconditional family endpoints -/

/-- Full marked-digraph derivational completeness for `S5_868`. -/
theorem markedDigraphDerivationalCompleteness :
    MarkedDigraphDerivationalCompleteness :=
  markedDigraphDerivationalCompleteness_of_maximalFactorReduction
    maximalIndecomposableFactorReduction

/-- The three published identities form a basis for the direct catalogue
representative. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis :=
  basis_complete_of_markedDigraphDerivationalCompleteness
    markedDigraphDerivationalCompleteness

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis :=
  basis_complete

/-- Reversal transports the completed direct proof to the opposite
semigroup and the reversed published basis. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_868.table.semigroup.opposite
      oppositeBasis :=
  opposite_basis_complete_of_markedDigraphDerivationalCompleteness
    markedDigraphDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_868

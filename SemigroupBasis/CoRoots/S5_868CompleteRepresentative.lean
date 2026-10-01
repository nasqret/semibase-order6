import SemigroupBasis.CoRoots.S5_868Completeness

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

/-! ## Finite enumeration of simple directed paths -/

/-- Keep the final occurrence of each letter. The resulting list is a
duplicate-free presentation of the same finite support. -/
def completionDeduplicate : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then
        completionDeduplicate rest
      else
        letter :: completionDeduplicate rest

theorem mem_completionDeduplicate (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ completionDeduplicate letters ↔ tested ∈ letters
  | [] => by simp [completionDeduplicate]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · rw [completionDeduplicate, if_pos present,
          mem_completionDeduplicate tested rest]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with rfl | member
          · exact present
          · exact member
      · simpa [completionDeduplicate, present,
          mem_completionDeduplicate tested rest]

theorem completionDeduplicate_nodup :
    ∀ letters : List Nat, (completionDeduplicate letters).Nodup
  | [] => by simp [completionDeduplicate]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · simpa [completionDeduplicate, present] using
          completionDeduplicate_nodup rest
      · have absent : letter ∉ completionDeduplicate rest := by
          rw [mem_completionDeduplicate]
          exact present
        simp [completionDeduplicate, present, absent,
          completionDeduplicate_nodup rest]

private theorem completion_nodup_length_le_of_subset
    {source target : List Nat}
    (nodup : source.Nodup)
    (subset : ∀ value, value ∈ source → value ∈ target) :
    source.length ≤ target.length := by
  induction source generalizing target with
  | nil => simp
  | cons head tail ih =>
      have nodupParts := List.pairwise_cons.mp nodup
      have headNotTail : head ∉ tail := by
        intro member
        exact (nodupParts.1 head member) rfl
      have tailNodup : tail.Nodup := nodupParts.2
      have headTarget : head ∈ target :=
        subset head (List.Mem.head tail)
      have tailSubset :
          ∀ value, value ∈ tail → value ∈ target.erase head := by
        intro value member
        have different : value ≠ head := by
          intro equality
          subst value
          exact headNotTail member
        exact (List.mem_erase_of_ne different).mpr
          (subset value (List.Mem.tail head member))
      have lengthBound := ih tailNodup tailSubset
      rw [List.length_erase_of_mem headTarget] at lengthBound
      have targetPositive : 1 ≤ target.length := by
        apply List.length_pos_iff.mpr
        intro empty
        subst target
        simp at headTarget
      simp only [List.length_cons]
      omega

/-- All lists of one fixed length over a finite alphabet. -/
def completionListsOfLength (alphabet : List Nat) :
    Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      alphabet.flatMap fun head =>
        (completionListsOfLength alphabet length).map
          fun tail => head :: tail

private theorem mem_completionListsOfLength
    (alphabet : List Nat) {letters : List Nat} :
    ∀ length : Nat,
      letters.length = length →
        (∀ letter, letter ∈ letters → letter ∈ alphabet) →
          letters ∈ completionListsOfLength alphabet length
  | 0, lengthEq, _ => by
      have empty : letters = [] :=
        List.eq_nil_of_length_eq_zero lengthEq
      subst letters
      simp [completionListsOfLength]
  | length + 1, lengthEq, subset => by
      cases letters with
      | nil => simp at lengthEq
      | cons head tail =>
          have headMember : head ∈ alphabet :=
            subset head (List.Mem.head tail)
          have tailLength : tail.length = length := by
            simpa using lengthEq
          have tailSubset :
              ∀ letter, letter ∈ tail → letter ∈ alphabet := by
            intro letter member
            exact subset letter (List.Mem.tail head member)
          have tailMember :=
            mem_completionListsOfLength alphabet length
              tailLength tailSubset
          apply List.mem_flatMap.mpr
          refine ⟨head, headMember, ?_⟩
          exact List.mem_map.mpr ⟨tail, tailMember, rfl⟩

/-- All positive-length lists over an alphabet whose length is at most the
given bound. -/
def completionListsUpTo (alphabet : List Nat) :
    Nat → List (List Nat)
  | 0 => []
  | bound + 1 =>
      completionListsUpTo alphabet bound ++
        completionListsOfLength alphabet (bound + 1)

private theorem mem_completionListsUpTo
    (alphabet : List Nat) {letters : List Nat}
    (nonempty : letters ≠ [])
    (subset : ∀ letter, letter ∈ letters → letter ∈ alphabet) :
    ∀ bound : Nat,
      letters.length ≤ bound →
        letters ∈ completionListsUpTo alphabet bound
  | 0, lengthBound => by
      have lengthZero : letters.length = 0 := by omega
      exact False.elim
        (nonempty (List.eq_nil_of_length_eq_zero lengthZero))
  | bound + 1, lengthBound => by
      rw [completionListsUpTo, List.mem_append]
      by_cases fullLength : letters.length = bound + 1
      · exact Or.inr <|
          mem_completionListsOfLength alphabet (bound + 1)
            fullLength subset
      · apply Or.inl
        apply mem_completionListsUpTo alphabet nonempty subset bound
        omega

/-- Check the tail of a directed path, retaining both vertex membership and
every directed adjacency edge. -/
def completionPathTailCheck
    (ambient : Word Nat) (previous : Nat) : List Nat → Bool
  | [] => true
  | next :: rest =>
      decide (next ∈ ambient.toList) &&
        (decide ((previous, next) ∈ ambient.adjacentPairs) &&
          completionPathTailCheck ambient next rest)

/-- Executable check that a nonempty list is a directed path in the ambient
word's graph. -/
def completionPathListCheck
    (ambient : Word Nat) : List Nat → Bool
  | [] => false
  | head :: tail =>
      decide (head ∈ ambient.toList) &&
        completionPathTailCheck ambient head tail

/-- Interpret a list as a nonempty word, using the fallback only for the
empty input excluded by `completionPathListCheck`. -/
def completionWordOfList (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

@[simp]
theorem completionWordOfList_toList
    (fallback : Nat) {letters : List Nat}
    (nonempty : letters ≠ []) :
    (completionWordOfList fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

theorem completionWordOfList_path_toList
    (fallback : Nat) (path : Word Nat) :
    completionWordOfList fallback path.toList = path := by
  have nonempty : path.toList ≠ [] := by
    cases path
    simp [Word.toList]
  apply Word.toList_injective
  rw [completionWordOfList_toList fallback nonempty]

private theorem completionPathTailCheck_support
    (ambient : Word Nat) :
    ∀ (previous : Nat) (tail : List Nat),
      completionPathTailCheck ambient previous tail = true →
        ∀ letter, letter ∈ tail → letter ∈ ambient.toList
  | _, [], _, _, member => by simp at member
  | previous, next :: rest, checked, letter, member => by
      simp only [completionPathTailCheck, Bool.and_eq_true,
        decide_eq_true_eq] at checked
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact checked.1
      · exact completionPathTailCheck_support ambient next rest
          checked.2.2 letter later

private theorem completionPathTailCheck_edges
    (ambient : Word Nat) :
    ∀ (previous : Nat) (tail : List Nat),
      completionPathTailCheck ambient previous tail = true →
        ∀ source target,
          (source, target) ∈ Word.adjacentPairsFrom previous tail →
            (source, target) ∈ ambient.adjacentPairs
  | _, [], _, source, target, member => by
      simp [Word.adjacentPairsFrom] at member
  | previous, next :: rest, checked, source, target, member => by
      simp only [completionPathTailCheck, Bool.and_eq_true,
        decide_eq_true_eq] at checked
      simp only [Word.adjacentPairsFrom, List.mem_cons] at member
      rcases member with first | later
      · simp only [Prod.mk.injEq] at first
        rcases first with ⟨rfl, rfl⟩
        exact checked.2.1
      · exact completionPathTailCheck_edges ambient next rest
          checked.2.2 source target later

private theorem completionPathTailCheck_true
    (ambient : Word Nat) :
    ∀ (previous : Nat) (tail : List Nat),
      (∀ letter, letter ∈ tail → letter ∈ ambient.toList) →
        (∀ source target,
          (source, target) ∈ Word.adjacentPairsFrom previous tail →
            (source, target) ∈ ambient.adjacentPairs) →
          completionPathTailCheck ambient previous tail = true
  | _, [], _, _ => rfl
  | previous, next :: rest, vertices, edges => by
      have nextMember : next ∈ ambient.toList :=
        vertices next (List.Mem.head rest)
      have firstEdge :
          (previous, next) ∈ ambient.adjacentPairs := by
        apply edges previous next
        simp [Word.adjacentPairsFrom]
      have restVertices :
          ∀ letter, letter ∈ rest → letter ∈ ambient.toList := by
        intro letter member
        exact vertices letter (List.Mem.tail next member)
      have restEdges :
          ∀ source target,
            (source, target) ∈ Word.adjacentPairsFrom next rest →
              (source, target) ∈ ambient.adjacentPairs := by
        intro source target member
        apply edges source target
        simp only [Word.adjacentPairsFrom, List.mem_cons]
        exact Or.inr member
      have restCheck :=
        completionPathTailCheck_true ambient next rest
          restVertices restEdges
      simp [completionPathTailCheck, nextMember, firstEdge, restCheck]

theorem directedPathIn_completionWordOfList_of_check
    (ambient : Word Nat) (fallback : Nat) {letters : List Nat}
    (checked : completionPathListCheck ambient letters = true) :
    DirectedPathIn ambient (completionWordOfList fallback letters) := by
  cases letters with
  | nil => simp [completionPathListCheck] at checked
  | cons head tail =>
      simp only [completionPathListCheck, Bool.and_eq_true,
        decide_eq_true_eq] at checked
      constructor
      · intro letter member
        simp only [completionWordOfList, Word.toList,
          List.mem_cons] at member
        rcases member with rfl | later
        · exact checked.1
        · exact completionPathTailCheck_support ambient head tail
            checked.2 letter later
      · intro source target member
        exact completionPathTailCheck_edges ambient head tail
          checked.2 source target member

theorem completionPathListCheck_true_of_directedPathIn
    (ambient : Word Nat) (fallback : Nat) {letters : List Nat}
    (nonempty : letters ≠ [])
    (pathIn :
      DirectedPathIn ambient (completionWordOfList fallback letters)) :
    completionPathListCheck ambient letters = true := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      have headMember : head ∈ ambient.toList :=
        pathIn.1 head (by simp [completionWordOfList, Word.toList])
      have tailVertices :
          ∀ letter, letter ∈ tail → letter ∈ ambient.toList := by
        intro letter member
        exact pathIn.1 letter <| by
          simp [completionWordOfList, Word.toList, member]
      have tailEdges :
          ∀ source target,
            (source, target) ∈ Word.adjacentPairsFrom head tail →
              (source, target) ∈ ambient.adjacentPairs := by
        intro source target member
        exact pathIn.2 source target member
      have tailCheck :=
        completionPathTailCheck_true ambient head tail
          tailVertices tailEdges
      simp [completionPathListCheck, headMember, tailCheck]

def completionPathListEligible
    (ambient : Word Nat) (letters : List Nat) : Bool :=
  decide letters.Nodup && completionPathListCheck ambient letters

def completionPathLists (ambient : Word Nat) : List (List Nat) :=
  let support := completionDeduplicate ambient.toList
  (completionListsUpTo support support.length).filter
    (completionPathListEligible ambient)

def completionPathWords (ambient : Word Nat) : List (Word Nat) :=
  (completionPathLists ambient).map
    (completionWordOfList ambient.head)

/-- Every enumerated path word really is a directed path in the ambient
marked graph. -/
theorem completionPathWords_directed
    (ambient path : Word Nat)
    (member : path ∈ completionPathWords ambient) :
    DirectedPathIn ambient path := by
  rcases List.mem_map.mp member with
    ⟨letters, listMember, rfl⟩
  have filtered := List.mem_filter.mp listMember
  have eligible := filtered.2
  simp only [completionPathListEligible, Bool.and_eq_true,
    decide_eq_true_eq] at eligible
  exact directedPathIn_completionWordOfList_of_check
    ambient ambient.head eligible.2

/-- The finite enumeration contains every simple directed path in the
ambient graph. -/
theorem completionPathWords_covers
    (ambient path : Word Nat)
    (nodup : path.toList.Nodup)
    (pathIn : DirectedPathIn ambient path) :
    path ∈ completionPathWords ambient := by
  let support := completionDeduplicate ambient.toList
  have nonempty : path.toList ≠ [] := by
    cases path
    simp [Word.toList]
  have supportSubset :
      ∀ letter, letter ∈ path.toList → letter ∈ support := by
    intro letter member
    change letter ∈ completionDeduplicate ambient.toList
    exact (mem_completionDeduplicate letter ambient.toList).2
      (pathIn.1 letter member)
  have lengthBound : path.toList.length ≤ support.length :=
    completion_nodup_length_le_of_subset nodup supportSubset
  have generated :
      path.toList ∈ completionListsUpTo support support.length :=
    mem_completionListsUpTo support nonempty supportSubset
      support.length lengthBound
  have pathCheck :
      completionPathListCheck ambient path.toList = true := by
    have converted :
        DirectedPathIn ambient
          (completionWordOfList ambient.head path.toList) := by
      simpa only [completionWordOfList_path_toList] using pathIn
    exact completionPathListCheck_true_of_directedPathIn
      ambient ambient.head nonempty converted
  have eligible :
      completionPathListEligible ambient path.toList = true := by
    simp [completionPathListEligible, nodup, pathCheck]
  have filtered : path.toList ∈ completionPathLists ambient := by
    change
      path.toList ∈
        (completionListsUpTo support support.length).filter
          (completionPathListEligible ambient)
    exact List.mem_filter.mpr ⟨generated, eligible⟩
  apply List.mem_map.mpr
  exact
    ⟨path.toList, filtered,
      completionWordOfList_path_toList ambient.head path⟩

/-! ## Splicing directed paths without introducing new edges -/

/-- Concatenate two path words while identifying the final vertex of the
left path with the initial vertex of the right path. -/
def completionJoin (left right : Word Nat) : Word Nat :=
  ⟨left.head, left.tail ++ right.tail⟩

@[simp]
theorem completionJoin_head (left right : Word Nat) :
    (completionJoin left right).head = left.head :=
  rfl

@[simp]
theorem completionJoin_toList (left right : Word Nat) :
    (completionJoin left right).toList =
      left.toList ++ right.tail := by
  simp [completionJoin, Word.toList]

private theorem completion_getLastD_append_nonempty
    (left : List Nat) (head fallback : Nat) (tail : List Nat) :
    (left ++ head :: tail).getLastD fallback =
      tail.getLastD head := by
  induction left generalizing fallback with
  | nil => simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih letter

theorem completionJoin_final
    {left right : Word Nat}
    (boundary : left.final = right.head) :
    (completionJoin left right).final = right.final := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases rightTail with
          | nil =>
              simpa [completionJoin, Word.final] using boundary
          | cons next rest =>
              simp only [completionJoin, Word.final]
              rw [completion_getLastD_append_nonempty]
              simp only [List.getLastD_cons]

theorem completionJoin_adjacentPairs
    {left right : Word Nat}
    (boundary : left.final = right.head) :
    (completionJoin left right).adjacentPairs =
      left.adjacentPairs ++ right.adjacentPairs := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases rightTail with
          | nil =>
              simp [completionJoin, Word.adjacentPairs,
                Word.adjacentPairsFrom]
          | cons next rest =>
              simp only [Word.final] at boundary
              have boundary' :
                  leftTail.getLast?.getD leftHead = rightHead := by
                simpa only [List.getLastD_eq_getLast?] using boundary
              simp only [completionJoin, Word.adjacentPairs]
              rw [Word.adjacentPairsFrom_append]
              simp [Word.adjacentPairsFrom, boundary']

private theorem completion_head_mem_toList (word : Word Nat) :
    word.head ∈ word.toList := by
  cases word
  simp [Word.toList]

private theorem completion_final_mem_toList (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

theorem completionJoin_directedPathIn
    {ambient left right : Word Nat}
    (boundary : left.final = right.head)
    (leftIn : DirectedPathIn ambient left)
    (rightIn : DirectedPathIn ambient right) :
    DirectedPathIn ambient (completionJoin left right) := by
  constructor
  · intro letter member
    rw [completionJoin_toList] at member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact leftIn.1 letter leftMember
    · exact rightIn.1 letter <| by
        simp [Word.toList, rightMember]
  · intro source target member
    rw [completionJoin_adjacentPairs boundary] at member
    rcases List.mem_append.mp member with leftEdge | rightEdge
    · exact leftIn.2 source target leftEdge
    · exact rightIn.2 source target rightEdge

private theorem completion_word_toList_eq_prefix_final
    (word : Word Nat) :
    ∃ stem, word.toList = stem ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruction :=
        (List.dropLast_concat_getLast
          (l := head :: tail) (by simp)).symm
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa [Word.toList, Word.final] using reconstruction

theorem completionJoin_occurs_left
    (left right : Word Nat) :
    OccursAsFactor left (completionJoin left right) := by
  refine ⟨[], right.tail, ?_⟩
  simp [completionJoin_toList]

theorem completionJoin_occurs_right
    {left right : Word Nat}
    (boundary : left.final = right.head) :
    OccursAsFactor right (completionJoin left right) := by
  rcases completion_word_toList_eq_prefix_final left with
    ⟨stem, leftShape⟩
  refine ⟨stem, [], ?_⟩
  rw [completionJoin_toList, leftShape, boundary]
  simp [Word.toList, List.append_assoc]

theorem occursAsFactor_trans
    {factor middle ambient : Word Nat}
    (factorMiddle : OccursAsFactor factor middle)
    (middleAmbient : OccursAsFactor middle ambient) :
    OccursAsFactor factor ambient := by
  rcases factorMiddle with ⟨innerPrefix, innerSuffix, innerShape⟩
  rcases middleAmbient with ⟨outerPrefix, outerSuffix, outerShape⟩
  refine
    ⟨outerPrefix ++ innerPrefix, innerSuffix ++ outerSuffix, ?_⟩
  rw [outerShape, innerShape]
  simp [List.append_assoc]

private def completionAdjacentPairsList :
    List Nat → List (Nat × Nat)
  | [] => []
  | head :: tail => Word.adjacentPairsFrom head tail

private theorem completionAdjacentPairsList_word (word : Word Nat) :
    completionAdjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

private theorem completionAdjacentPairsList_append_left
    (right : List Nat) {left : List Nat} {edge : Nat × Nat}
    (member : edge ∈ completionAdjacentPairsList left) :
    edge ∈ completionAdjacentPairsList (left ++ right) := by
  cases left with
  | nil => simp [completionAdjacentPairsList] at member
  | cons first rest =>
      cases right with
      | nil => simpa using member
      | cons next tail =>
          change
            edge ∈ Word.adjacentPairsFrom first rest at member
          change
            edge ∈
              Word.adjacentPairsFrom first
                (rest ++ next :: tail)
          rw [Word.adjacentPairsFrom_append]
          simp [member]

private theorem completionAdjacentPairsList_append_right
    (left : List Nat) {right : List Nat} {edge : Nat × Nat}
    (member : edge ∈ completionAdjacentPairsList right) :
    edge ∈ completionAdjacentPairsList (left ++ right) := by
  cases left with
  | nil => simpa using member
  | cons first rest =>
      cases right with
      | nil => simp [completionAdjacentPairsList] at member
      | cons next tail =>
          change
            edge ∈ Word.adjacentPairsFrom next tail at member
          change
            edge ∈
              Word.adjacentPairsFrom first
                (rest ++ next :: tail)
          rw [Word.adjacentPairsFrom_append]
          simp [member]

theorem occursAsFactor_support
    {factor ambient : Word Nat}
    (occurs : OccursAsFactor factor ambient) :
    ∀ letter, letter ∈ factor.toList → letter ∈ ambient.toList := by
  intro letter member
  rcases occurs with ⟨stem, suffix, shape⟩
  rw [shape]
  simp [member]

theorem occursAsFactor_edge
    {factor ambient : Word Nat}
    (occurs : OccursAsFactor factor ambient) :
    ∀ source target,
      (source, target) ∈ factor.adjacentPairs →
        (source, target) ∈ ambient.adjacentPairs := by
  intro source target member
  rcases occurs with ⟨stem, suffix, shape⟩
  rw [← completionAdjacentPairsList_word] at member ⊢
  rw [shape]
  apply completionAdjacentPairsList_append_left suffix
  apply completionAdjacentPairsList_append_right stem
  exact member

theorem directedPathIn_refl (word : Word Nat) :
    DirectedPathIn word word :=
  ⟨fun _ => id, fun _ _ => id⟩

/-! ## Constructing one walk containing the finite path enumeration -/

/-- Starting from any path in an indecomposable graph, splice in a finite
list of further directed paths. The result contains the start and every
requested path as contiguous factors. -/
theorem existsCompletionPathFold
    (ambient : Word Nat)
    (indecomposable : TrahtmanIndecomposable ambient) :
    ∀ paths : List (Word Nat),
      (∀ path, path ∈ paths → DirectedPathIn ambient path) →
        ∀ start : Word Nat,
          DirectedPathIn ambient start →
            ∃ finished : Word Nat,
              finished.head = start.head ∧
                DirectedPathIn ambient finished ∧
                OccursAsFactor start finished ∧
                ∀ path, path ∈ paths →
                  OccursAsFactor path finished
  | [], _, start, startIn => by
      refine ⟨start, rfl, startIn, ?_, ?_⟩
      · refine ⟨[], [], ?_⟩
        simp
      · intro path member
        simp at member
  | path :: rest, pathsIn, start, startIn => by
      have pathIn : DirectedPathIn ambient path :=
        pathsIn path (List.Mem.head rest)
      have restIn :
          ∀ candidate, candidate ∈ rest →
            DirectedPathIn ambient candidate := by
        intro candidate member
        exact pathsIn candidate (List.Mem.tail path member)
      have startFinalMember : start.final ∈ ambient.toList :=
        startIn.1 start.final (completion_final_mem_toList start)
      have pathHeadMember : path.head ∈ ambient.toList :=
        pathIn.1 path.head (completion_head_mem_toList path)
      rcases indecomposable start.final startFinalMember
          path.head pathHeadMember with
        ⟨connector, connectorHead, connectorFinal, connectorIn⟩
      have firstBoundary : start.final = connector.head :=
        connectorHead.symm
      let withConnector := completionJoin start connector
      have withConnectorIn : DirectedPathIn ambient withConnector :=
        completionJoin_directedPathIn firstBoundary startIn connectorIn
      have secondBoundary : withConnector.final = path.head := by
        rw [completionJoin_final firstBoundary]
        exact connectorFinal
      let extended := completionJoin withConnector path
      have extendedIn : DirectedPathIn ambient extended :=
        completionJoin_directedPathIn secondBoundary
          withConnectorIn pathIn
      have startExtended : OccursAsFactor start extended :=
        occursAsFactor_trans
          (completionJoin_occurs_left start connector)
          (completionJoin_occurs_left withConnector path)
      have pathExtended : OccursAsFactor path extended :=
        completionJoin_occurs_right secondBoundary
      rcases existsCompletionPathFold ambient indecomposable rest restIn
          extended extendedIn with
        ⟨finished, finishedHead, extendedFinished, extendedOccurs,
          restOccurs⟩
      have extendedHead : extended.head = start.head := rfl
      refine
        ⟨finished, finishedHead.trans extendedHead, extendedFinished,
          occursAsFactor_trans startExtended extendedOccurs, ?_⟩
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact occursAsFactor_trans pathExtended extendedOccurs
      · exact restOccurs candidate later

/-- Close the finite path-containing walk back at the original final vertex.
The output has the same marked graph and contains every enumerated simple
path. -/
theorem existsCompletionWalk
    (ambient : Word Nat)
    (indecomposable : TrahtmanIndecomposable ambient) :
    ∃ complete : Word Nat,
      ambient.SameMarkedDigraph complete ∧
        ∀ path, path ∈ completionPathWords ambient →
          OccursAsFactor path complete := by
  have candidatesIn :
      ∀ path, path ∈ completionPathWords ambient →
        DirectedPathIn ambient path :=
    completionPathWords_directed ambient
  rcases existsCompletionPathFold ambient indecomposable
      (completionPathWords ambient) candidatesIn ambient
      (directedPathIn_refl ambient) with
    ⟨walk, walkHead, walkIn, ambientOccurs, candidatesOccur⟩
  have walkFinalMember : walk.final ∈ ambient.toList :=
    walkIn.1 walk.final (completion_final_mem_toList walk)
  have ambientFinalMember : ambient.final ∈ ambient.toList :=
    completion_final_mem_toList ambient
  rcases indecomposable walk.final walkFinalMember
      ambient.final ambientFinalMember with
    ⟨closing, closingHead, closingFinal, closingIn⟩
  have closingBoundary : walk.final = closing.head :=
    closingHead.symm
  let complete := completionJoin walk closing
  have completeIn : DirectedPathIn ambient complete :=
    completionJoin_directedPathIn closingBoundary walkIn closingIn
  have walkOccurs : OccursAsFactor walk complete :=
    completionJoin_occurs_left walk closing
  have ambientComplete : OccursAsFactor ambient complete :=
    occursAsFactor_trans ambientOccurs walkOccurs
  have completeHead : complete.head = ambient.head :=
    (completionJoin_head walk closing).trans walkHead
  have completeFinal : complete.final = ambient.final :=
    (completionJoin_final closingBoundary).trans closingFinal
  have sameGraph : ambient.SameMarkedDigraph complete := by
    refine ⟨completeHead.symm, completeFinal.symm, ?_, ?_⟩
    · intro letter
      constructor
      · exact occursAsFactor_support ambientComplete letter
      · exact completeIn.1 letter
    · intro source target
      constructor
      · exact occursAsFactor_edge ambientComplete source target
      · exact completeIn.2 source target
  refine ⟨complete, sameGraph, ?_⟩
  intro path member
  exact occursAsFactor_trans (candidatesOccur path member) walkOccurs

/-- Constructive finite-graph completion of an indecomposable word. The
construction enumerates all simple paths over the finite support, splices
them with reachability witnesses, and closes the resulting walk at the
original final vertex. -/
theorem completeRepresentativeExistence :
    CompleteRepresentativeExistence := by
  intro ambient indecomposable
  rcases existsCompletionWalk ambient indecomposable with
    ⟨complete, sameGraph, candidatesOccur⟩
  refine ⟨complete, sameGraph, ?_⟩
  intro path nodup pathInComplete
  have pathInAmbient : DirectedPathIn ambient path :=
    (directedPathIn_iff_of_sameMarkedDigraph sameGraph).mpr
      pathInComplete
  exact candidatesOccur path <|
    completionPathWords_covers ambient path nodup pathInAmbient

end SemigroupBasis.CoRoots.S5_868

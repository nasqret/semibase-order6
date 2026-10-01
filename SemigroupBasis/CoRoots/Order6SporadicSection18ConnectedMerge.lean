import SemigroupBasis.CoRoots.Order6SporadicSection18MatchingEndpoints

/-! C7 connectedization of arbitrary products. Cut geometry and append-factor
recursion are copied from pinned generic Section12 proofs. Algebraic bridge
steps are authored here from C7 boundary duplication and square commutation. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization
open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6SporadicSection12

def closedEnvelopeList (endpoint : Nat) (interior : List Nat) : List Nat :=
  endpoint :: interior ++ [endpoint]

def bridgeList
    (leftEndpoint rightEndpoint : Nat)
    (leftInterior rightInterior : List Nat) : List Nat :=
  leftEndpoint ::
    leftInterior ++
      rightEndpoint :: leftEndpoint :: rightInterior ++ [rightEndpoint]

def bridgeWord
    (leftEndpoint rightEndpoint : Nat)
    (leftInterior rightInterior : List Nat) : Word Nat :=
  ⟨leftEndpoint,
    leftInterior ++
      rightEndpoint :: leftEndpoint :: rightInterior ++ [rightEndpoint]⟩

@[simp]
theorem bridgeWord_toList
    (leftEndpoint rightEndpoint : Nat)
    (leftInterior rightInterior : List Nat) :
    (bridgeWord leftEndpoint rightEndpoint
      leftInterior rightInterior).toList =
        bridgeList leftEndpoint rightEndpoint
          leftInterior rightInterior :=
  rfl

private theorem first_mem_left
    {first : Nat} {tail left right : List Nat}
    (shape : first :: tail = left ++ right)
    (leftNonempty : left ≠ []) :
    first ∈ left := by
  cases left with
  | nil => contradiction
  | cons leftHead leftTail =>
      change first :: tail = leftHead :: (leftTail ++ right) at shape
      cases shape
      exact List.Mem.head _

private theorem last_mem_right
    {last : Nat} {body left right : List Nat}
    (shape : body ++ [last] = left ++ right)
    (rightNonempty : right ≠ []) :
    last ∈ right := by
  have reversed :
      last :: body.reverse = right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have rightReverseNonempty : right.reverse ≠ [] := by
    simpa using rightNonempty
  have member := first_mem_left reversed rightReverseNonempty
  simpa using member

private theorem adjacent_pair_mem_left_or_right
    (y x : Nat) (after right : List Nat) :
    ∀ (before left : List Nat),
      before ++ y :: x :: after = left ++ right →
      y ∈ left ∨ x ∈ right
  | [], [], shape => by
      right
      have rightShape : right = y :: x :: after := by
        simpa using shape.symm
      rw [rightShape]
      simp
  | [], leftHead :: leftTail, shape => by
      left
      have headEq : y = leftHead := by
        change y :: x :: after = leftHead :: (leftTail ++ right) at shape
        exact (List.cons.inj shape).1
      subst leftHead
      simp
  | beforeHead :: beforeTail, [], shape => by
      right
      have rightShape :
          right = beforeHead :: (beforeTail ++ y :: x :: after) := by
        simpa using shape.symm
      rw [rightShape]
      simp
  | beforeHead :: beforeTail, leftHead :: leftTail, shape => by
      have tailShape :
          beforeTail ++ y :: x :: after = leftTail ++ right := by
        change
          beforeHead :: (beforeTail ++ y :: x :: after) =
            leftHead :: (leftTail ++ right) at shape
        exact (List.cons.inj shape).2
      rcases adjacent_pair_mem_left_or_right
          y x after right beforeTail leftTail tailShape with
        inLeft | inRight
      · exact Or.inl (List.Mem.tail leftHead inLeft)
      · exact Or.inr inRight

/-- The (12.4) target is connected: the first/second `x` crosses every cut
up to the central pair, and the first/final `y` crosses every later cut. -/
theorem bridgeList_supportConnected
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    ConnectedComponentSupportConnected
      (bridgeList x y leftInterior rightInterior) := by
  intro left right shape leftNonempty rightNonempty
  have xInLeft : x ∈ left :=
    first_mem_left
      (by simpa [bridgeList, List.append_assoc] using shape)
      leftNonempty
  have finalShape :
      (x :: leftInterior ++ y :: x :: rightInterior) ++ [y] =
        left ++ right := by
    simpa [bridgeList, List.append_assoc] using shape
  have yInRight : y ∈ right :=
    last_mem_right finalShape rightNonempty
  have middleShape :
      (x :: leftInterior) ++ y :: x :: (rightInterior ++ [y]) =
        left ++ right := by
    simpa [bridgeList, List.append_assoc] using shape
  have crossing :=
    adjacent_pair_mem_left_or_right y x
      (rightInterior ++ [y]) right
      (x :: leftInterior) left middleShape
  rcases crossing with yInLeft | xInRight
  · exact ⟨y, yInLeft, yInRight⟩
  · exact ⟨x, xInLeft, xInRight⟩

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word
  simp [Word.toList]

private theorem connected_of_supportConnected
    (word : Word Nat)
    (lengthAtLeastTwo : 2 ≤ word.toList.length)
    (supportConnected :
      ConnectedComponentSupportConnected word.toList) :
    Connected word := by
  refine ⟨lengthAtLeastTwo, ?_⟩
  rintro ⟨left, right, shape, disjoint⟩
  have listShape :
      word.toList = left.toList ++ right.toList := by
    rw [shape, Word.toList_append]
  rcases supportConnected left.toList right.toList listShape
      (word_toList_ne_nil left) (word_toList_ne_nil right) with
    ⟨letter, leftMember, rightMember⟩
  exact disjoint letter leftMember rightMember

theorem bridgeWord_connected
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    Connected (bridgeWord x y leftInterior rightInterior) := by
  apply connected_of_supportConnected
  · simp [bridgeWord, Word.toList]
    omega
  · simpa using
      bridgeList_supportConnected x y leftInterior rightInterior

/-- A closed envelope is connected, since its endpoint crosses every cut. -/
def closedEnvelopeWord (endpoint : Nat) (interior : List Nat) : Word Nat :=
  ⟨endpoint, interior ++ [endpoint]⟩

theorem closedEnvelopeWord_connected (endpoint : Nat) (interior : List Nat) :
    Connected (closedEnvelopeWord endpoint interior) := by
  apply connected_of_supportConnected
  · simp [closedEnvelopeWord, Word.toList]
  · intro left right shape leftNonempty rightNonempty
    have first : endpoint ∈ left :=
      first_mem_left (by simpa [closedEnvelopeWord, Word.toList, List.append_assoc] using shape) leftNonempty
    have finalShape : (endpoint :: interior) ++ [endpoint] = left ++ right := by
      simpa [closedEnvelopeWord, Word.toList, List.append_assoc] using shape
    have last : endpoint ∈ right :=
      last_mem_right (body := endpoint :: interior) (left := left) finalShape rightNonempty
    exact ⟨endpoint, first, last⟩

theorem doubleClosedEnvelope (endpoint : Nat) (interior : List Nat) :
    ListDerives (closedEnvelopeList endpoint interior)
      ([endpoint, endpoint] ++ interior ++ [endpoint, endpoint]) := by
  have first : ListDerives (closedEnvelopeList endpoint interior)
      ([endpoint, endpoint] ++ interior ++ [endpoint]) := by
    simpa [closedEnvelopeList, List.append_assoc] using duplicateFirst endpoint interior
  have last : ListDerives ([endpoint, endpoint] ++ interior ++ [endpoint])
      ([endpoint, endpoint] ++ interior ++ [endpoint, endpoint]) := by
    simpa [List.append_assoc] using duplicateLast endpoint (endpoint :: interior)
  exact first.trans last

/-- C7's square commutation crosses adjacent closed envelopes. This uses
(18.1a,b), not the B7-specific unsquared adjacent-envelope identity. -/
theorem listDerivesAdjacentEnvelopeBridge
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    ListDerives
      (closedEnvelopeList x leftInterior ++ closedEnvelopeList y rightInterior)
      (bridgeList x y ([x] ++ leftInterior ++ [y]) ([x] ++ rightInterior ++ [y])) := by
  let squaredLeft := [x, x] ++ leftInterior ++ [x, x]
  let squaredRight := [y, y] ++ rightInterior ++ [y, y]
  have leftStep : ListDerives
      (closedEnvelopeList x leftInterior ++ closedEnvelopeList y rightInterior)
      (squaredLeft ++ closedEnvelopeList y rightInterior) :=
    (doubleClosedEnvelope x leftInterior).append (closedEnvelopeList y rightInterior)
  have rightStep : ListDerives
      (squaredLeft ++ closedEnvelopeList y rightInterior) (squaredLeft ++ squaredRight) :=
    (doubleClosedEnvelope y rightInterior).prepend squaredLeft
  have crossing : ListDerives (squaredLeft ++ squaredRight)
      (bridgeList x y ([x] ++ leftInterior ++ [y]) ([x] ++ rightInterior ++ [y])) := by
    simpa [squaredLeft, squaredRight, bridgeList, List.append_assoc] using
      (swapSquares x y).context ([x, x] ++ leftInterior) (rightInterior ++ [y, y])
  exact leftStep.trans (rightStep.trans crossing)

/-- Any two connected words derive, in the actual C7 basis, to one connected
word. Generic cut geometry is reused; every algebraic step is a C7 derivation. -/
theorem mergeConnectedWords (left right : Word Nat)
    (leftConnected : Connected left) (rightConnected : Connected right) :
    ∃ target, Connected target ∧ Derives basis (left ++ right) target := by
  obtain ⟨leftInterior, leftDerivation⟩ := connected_matching_endpoints left leftConnected
  obtain ⟨rightInterior, rightDerivation⟩ := connected_matching_endpoints right rightConnected
  have normalizeLeft := leftDerivation.append right.toList
  have normalizeRight := rightDerivation.prepend (closedEnvelopeList left.head leftInterior)
  have bridge := listDerivesAdjacentEnvelopeBridge left.head right.head leftInterior rightInterior
  let leftMiddle := [left.head] ++ leftInterior ++ [right.head]
  let rightMiddle := [left.head] ++ rightInterior ++ [right.head]
  have combined : ListDerives (left.toList ++ right.toList)
      (bridgeList left.head right.head leftMiddle rightMiddle) :=
    normalizeLeft.trans (normalizeRight.trans bridge)
  let target := bridgeWord left.head right.head leftMiddle rightMiddle
  have listProof : ListDerives (left ++ right).toList target.toList := by
    simpa only [Word.toList_append, target, bridgeWord_toList] using combined
  exact ⟨target, bridgeWord_connected _ _ _ _, S5_107.ListDerives.toWord listProof⟩

private theorem appendFactors_congr
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    ∀ rest : List (Word Nat),
      Derives basis
        (appendFactors left rest) (appendFactors right rest)
  | [] => by simpa [appendFactors] using derivation
  | next :: remaining => by
      change
        Derives basis
          (appendFactors (left ++ next) remaining)
          (appendFactors (right ++ next) remaining)
      exact appendFactors_congr
        (Derives.appendRight derivation next) remaining

private theorem existsConnectedDerivative_of_factors
    (first : Word Nat) :
    ∀ rest : List (Word Nat),
      Connected first →
      (∀ factor, factor ∈ rest → Connected factor) →
      ∃ target,
        Connected target ∧
          Derives basis (appendFactors first rest) target
  | [], firstConnected, _ =>
      ⟨first, firstConnected, by
        simpa [appendFactors] using
          (Derives.refl (basis := basis) first)⟩
  | next :: remaining, firstConnected, restConnected => by
      have nextConnected :=
        restConnected next (List.Mem.head remaining)
      rcases mergeConnectedWords first next
          firstConnected nextConnected with
        ⟨merged, mergedConnected, firstMerge⟩
      rcases existsConnectedDerivative_of_factors merged remaining
          mergedConnected
          (fun factor member =>
            restConnected factor (List.Mem.tail next member)) with
        ⟨target, targetConnected, remainingDerivation⟩
      refine ⟨target, targetConnected, ?_⟩
      exact
        (appendFactors_congr firstMerge remaining).trans
          remainingDerivation

theorem existsConnectedDerivative
    (word : Word Nat)
    (domain : PairwiseDisjointConnectedProduct word) :
    ∃ target,
      Connected target ∧ Derives basis word target := by
  rcases domain with
    ⟨first, rest, factorsConnected, _, wordShape⟩
  have firstConnected :=
    factorsConnected first (List.Mem.head rest)
  have restConnected :
      ∀ factor, factor ∈ rest → Connected factor := by
    intro factor member
    exact factorsConnected factor (List.Mem.tail first member)
  rcases existsConnectedDerivative_of_factors first rest
      firstConnected restConnected with
    ⟨target, targetConnected, derivation⟩
  exact ⟨target, targetConnected, by simpa [wordShape] using derivation⟩

/-- Every product in the unrestricted reduction domain has a C7-derivable
connected representative with matching first and last letters. Canonical
outer-block equality remains a separate obligation. -/
theorem existsMatchingConnectedDerivative (word : Word Nat)
    (domain : PairwiseDisjointConnectedProduct word) :
    ∃ endpoint interior,
      Connected (closedEnvelopeWord endpoint interior) ∧
      Derives basis word (closedEnvelopeWord endpoint interior) := by
  obtain ⟨connectedWord, connected, first⟩ := existsConnectedDerivative word domain
  obtain ⟨interior, matching⟩ := connected_matching_endpoints connectedWord connected
  have lastList : ListDerives connectedWord.toList
      (closedEnvelopeWord connectedWord.head interior).toList := matching
  have last : Derives basis connectedWord (closedEnvelopeWord connectedWord.head interior) :=
    S5_107.ListDerives.toWord lastList
  exact ⟨connectedWord.head, interior, closedEnvelopeWord_connected _ _, first.trans last⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.bridgeWord_connected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.closedEnvelopeWord_connected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.doubleClosedEnvelope
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.listDerivesAdjacentEnvelopeBridge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.mergeConnectedWords
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.existsConnectedDerivative
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.existsMatchingConnectedDerivative

end SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization

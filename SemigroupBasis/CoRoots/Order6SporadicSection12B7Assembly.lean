import SemigroupBasis.CoRoots.Order6SporadicSection12B7Reduction
import SemigroupBasis.CoRoots.Order6SporadicSection12B8Assembly

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

namespace B7Assembly

private abbrev ListDerives :=
  S5_107.ListDerives b7Basis

private theorem b7Basis_eq_b8_append :
    b7Basis =
      b8Basis ++
        [law_12_4_empty, law_12_4_H, law_12_4_K, law_12_4_HK] := by
  rfl

private theorem b8Basis_member_b7
    (identity : Identity Nat) (member : identity ∈ b8Basis) :
    identity ∈ b7Basis := by
  rw [b7Basis_eq_b8_append]
  exact List.mem_append.mpr (Or.inl member)

private theorem liftB8Derives
    {left right : Word Nat}
    (derivation : Derives b8Basis left right) :
    Derives b7Basis left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (b8Basis_member_b7 identity member)

private theorem liftB8ListDerives
    {left right : List Nat}
    (derivation : S5_107.ListDerives b8Basis left right) :
    ListDerives left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words wordDerivation =>
      exact S5_107.ListDerives.words (liftB8Derives wordDerivation)

private def instantiateFiveWords
    (x y z h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => h
  | 4 => k
  | n + 5 => Word.singleton (n + 5)

private theorem basisBridgeEmpty :
    Derives b7Basis word_12_4_empty_left word_12_4_empty_right :=
  Derives.fromBasis (e := law_12_4_empty) <| by
    simp [b7Basis]

private theorem basisBridgeH :
    Derives b7Basis word_12_4_H_left word_12_4_H_right :=
  Derives.fromBasis (e := law_12_4_H) <| by
    simp [b7Basis]

private theorem basisBridgeK :
    Derives b7Basis word_12_4_K_left word_12_4_K_right :=
  Derives.fromBasis (e := law_12_4_K) <| by
    simp [b7Basis]

private theorem basisBridgeHK :
    Derives b7Basis word_12_4_HK_left word_12_4_HK_right :=
  Derives.fromBasis (e := law_12_4_HK) <| by
    simp [b7Basis]

private theorem derivesBridgeEmpty
    (x y : Word Nat) :
    Derives b7Basis
      (((x ++ x) ++ y) ++ y)
      (((x ++ y) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisBridgeEmpty
      (instantiateFiveWords x y y x y)
  simpa [word_12_4_empty_left_shape, word_12_4_empty_right_shape,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesBridgeH
    (x y leftInterior : Word Nat) :
    Derives b7Basis
      ((((x ++ leftInterior) ++ x) ++ y) ++ y)
      ((((x ++ leftInterior) ++ y) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisBridgeH
      (instantiateFiveWords x y y leftInterior y)
  simpa [word_12_4_H_left_shape, word_12_4_H_right_shape,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesBridgeK
    (x y rightInterior : Word Nat) :
    Derives b7Basis
      (((((x ++ x) ++ y) ++ rightInterior) ++ y))
      (((((x ++ y) ++ x) ++ rightInterior) ++ y)) := by
  have substituted :=
    Derives.subst basisBridgeK
      (instantiateFiveWords x y y x rightInterior)
  simpa [word_12_4_K_left_shape, word_12_4_K_right_shape,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesBridgeHK
    (x y leftInterior rightInterior : Word Nat) :
    Derives b7Basis
      (((((x ++ leftInterior) ++ x) ++ y) ++ rightInterior) ++ y)
      (((((x ++ leftInterior) ++ y) ++ x) ++ rightInterior) ++ y) := by
  have substituted :=
    Derives.subst basisBridgeHK
      (instantiateFiveWords x y y leftInterior rightInterior)
  simpa [word_12_4_HK_left_shape, word_12_4_HK_right_shape,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

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

/-- The four recorded boundary variants of (12.4), assembled into the exact
adjacent-envelope rewrite used in Lemma 12.9. -/
theorem listDerivesAdjacentEnvelopeBridge
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    ListDerives
      (closedEnvelopeList x leftInterior ++
        closedEnvelopeList y rightInterior)
      (bridgeList x y leftInterior rightInterior) := by
  cases leftInterior with
  | nil =>
      cases rightInterior with
      | nil =>
          simpa [closedEnvelopeList, bridgeList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesBridgeEmpty
                  (Word.singleton x) (Word.singleton y)))
      | cons rightHead rightTail =>
          let rightWord :=
            S5_107.listWordOfCons rightHead rightTail
          simpa [closedEnvelopeList, bridgeList, rightWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesBridgeK
                  (Word.singleton x) (Word.singleton y) rightWord))
  | cons leftHead leftTail =>
      let leftWord :=
        S5_107.listWordOfCons leftHead leftTail
      cases rightInterior with
      | nil =>
          simpa [closedEnvelopeList, bridgeList, leftWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesBridgeH
                  (Word.singleton x) (Word.singleton y) leftWord))
      | cons rightHead rightTail =>
          let rightWord :=
            S5_107.listWordOfCons rightHead rightTail
          simpa [closedEnvelopeList, bridgeList, leftWord, rightWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesBridgeHK
                  (Word.singleton x) (Word.singleton y)
                  leftWord rightWord))

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

/-- Two connected factors derive to one connected word: normalize each to a
closed B8 envelope and apply the appropriate boundary instance of (12.4). -/
theorem mergeConnectedWords
    (left right : Word Nat)
    (leftConnected : Connected left)
    (rightConnected : Connected right) :
    ∃ target,
      Connected target ∧ Derives b7Basis (left ++ right) target := by
  rcases B8Normalization.listDerivesConnectedToMatchingEndpoints
      left leftConnected with
    ⟨leftInterior, leftDerivation⟩
  rcases B8Normalization.listDerivesConnectedToMatchingEndpoints
      right rightConnected with
    ⟨rightInterior, rightDerivation⟩
  have normalizeLeft :=
    (liftB8ListDerives leftDerivation).append right.toList
  have normalizeRight :=
    (liftB8ListDerives rightDerivation).prepend
      (closedEnvelopeList left.head leftInterior)
  have bridge :=
    listDerivesAdjacentEnvelopeBridge
      left.head right.head leftInterior rightInterior
  have combined :
      ListDerives
        (left.toList ++ right.toList)
        (bridgeList left.head right.head
          leftInterior rightInterior) :=
    normalizeLeft.trans (normalizeRight.trans bridge)
  let target :=
    bridgeWord left.head right.head leftInterior rightInterior
  refine ⟨target, bridgeWord_connected _ _ _ _, ?_⟩
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have wordDerivation :=
            S5_107.ListDerives.toWord <| by
              simpa [Word.toList, bridgeList, List.append_assoc] using
                combined
          simpa [target, bridgeWord, S5_107.listWordOfCons,
            Word.append] using wordDerivation

private theorem appendFactors_congr
    {left right : Word Nat}
    (derivation : Derives b7Basis left right) :
    ∀ rest : List (Word Nat),
      Derives b7Basis
        (appendFactors left rest) (appendFactors right rest)
  | [] => by simpa [appendFactors] using derivation
  | next :: remaining => by
      change
        Derives b7Basis
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
          Derives b7Basis (appendFactors first rest) target
  | [], firstConnected, _ =>
      ⟨first, firstConnected, by
        simpa [appendFactors] using
          (Derives.refl (basis := b7Basis) first)⟩
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
      Connected target ∧ Derives b7Basis word target := by
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

theorem canonical_eq_of_valid
    {left right : Word Nat}
    (leftCanonical : B8Canonical.Canonical left)
    (rightCanonical : B8Canonical.Canonical right)
    (valid :
      (Identity.mk left right).SatisfiedBy S6_5625.table.semigroup) :
    left = right := by
  have n31Valid :=
    S6_5625.valid_n_3_1 (Identity.mk left right) valid
  have cappedEq :
      ∀ letter,
        min (left.toList.count letter) 3 =
          min (right.toList.count letter) 3 := by
    simpa [Generated.S4_40.table] using
      exponentFourValid_capped_count_eq (Identity.mk left right) n31Valid
  have countEq :
      ∀ letter, left.toList.count letter = right.toList.count letter := by
    intro letter
    have leftBound := leftCanonical.count_le_three letter
    have rightBound := rightCanonical.count_le_three letter
    simpa [Nat.min_eq_left leftBound,
      Nat.min_eq_left rightBound] using cappedEq letter
  have canonicalEq :=
    B8Canonical.canonicalList_eq_of_count_eq countEq
  apply Word.toList_injective
  exact leftCanonical.fixed.symm.trans <|
    canonicalEq.trans rightCanonical.fixed

theorem normalize
    (word : Word Nat)
    (domain : PairwiseDisjointConnectedProduct word) :
    ∃ target,
      B8Canonical.Canonical target ∧
        Derives b7Basis word target := by
  rcases existsConnectedDerivative word domain with
    ⟨connectedWord, connected, toConnected⟩
  let target := B8Assembly.canonicalWord connectedWord
  have targetCanonical :=
    B8Assembly.canonicalWord_canonical connectedWord connected
  have toCanonical :=
    liftB8Derives
      (B8Assembly.derivesCanonical connectedWord connected)
  exact
    ⟨target, targetCanonical,
      toConnected.trans (by simpa [target] using toCanonical)⟩

def canonicalProof :
    RestrictedCanonicalProof S6_5625.table b7Basis
      PairwiseDisjointConnectedProduct where
  canonical := B8Canonical.Canonical
  normalize := normalize
  uniqueOfValid := fun left right leftCanonical rightCanonical valid =>
    canonical_eq_of_valid leftCanonical rightCanonical valid

theorem basisFor : BasisFor S6_5625.table.semigroup b7Basis :=
  S6_5625.basisFor_of_canonicalProof
    S6_5625.restrictedBasisReduction canonicalProof

theorem oppositeBasisFor :
    BasisFor S6_5625.table.semigroup.opposite b7OppositeBasis :=
  S6_5625.oppositeBasisFor_of_canonicalProof
    S6_5625.restrictedBasisReduction canonicalProof

end B7Assembly

end SemigroupBasis.CoRoots.Order6SporadicSection12

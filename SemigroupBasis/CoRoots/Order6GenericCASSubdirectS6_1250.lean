import SemigroupBasis.Examples.CommutativeParityThresholdFive
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_1250
import SemigroupBasis.Generated.S2_3
import SemigroupBasis.CoRoots.S5_17Family

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_1250

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup
private abbrev rightTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_17.table

/-! ## Root derivations -/

private theorem rootLaw0Derives :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0.rhs :=
  Derives.fromBasis
    (basis :=
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis)
    (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0)
    (List.Mem.head _)

private theorem rootLaw1Derives :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1.rhs :=
  Derives.fromBasis
    (basis :=
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis)
    (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1)
    (List.Mem.tail _ (List.Mem.head _))

private theorem rootLaw2Derives :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2.rhs :=
  Derives.fromBasis
    (basis :=
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis)
    (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem rootLaw3Derives :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3.rhs :=
  Derives.fromBasis
    (basis :=
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis)
    (e := SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3)
    (List.Mem.tail _ <| List.Mem.tail _ <|
      List.Mem.tail _ <| List.Mem.head _)

private def instantiateOneWord (word : Word Nat) : Nat → Word Nat
  | 0 => word
  | n + 1 => Word.singleton (n + 1)

private theorem derivesFourExpansion (word : Word Nat) :
    Derives rootBasis
      (word ++ word) (((word ++ word) ++ word) ++ word) := by
  have substituted :=
    Derives.subst rootLaw0Derives (instantiateOneWord word)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0,
    instantiateOneWord, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem parityThresholdAxiomsDerive
    (identity : Identity Nat)
    (member : identity ∈ commutativeParityThresholdFiveBasis) :
    Derives rootBasis identity.lhs identity.rhs := by
  simp only [commutativeParityThresholdFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · simpa [parityThresholdCommutativityLaw, parityThresholdXY,
      parityThresholdYX,
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1]
      using rootLaw1Derives
  · have expanded :=
      Derives.appendRight
        (derivesFourExpansion (Word.singleton 0)) (Word.singleton 0)
    simpa [parityThresholdUnaryLaw, parityThresholdXXX,
      parityThresholdXXXXX, Word.singleton, Word.append,
      Word.append_assoc] using expanded
  · have expanded :=
      Derives.appendRight
        (derivesFourExpansion (Word.singleton 0)) (Word.singleton 1)
    simpa [parityThresholdLeftHeavyLaw, parityThresholdXXY,
      parityThresholdXXXXY, Word.singleton, Word.append,
      Word.append_assoc] using expanded
  · simpa [parityThresholdRightHeavyLaw, parityThresholdXXY,
      parityThresholdXXYYY,
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2]
      using rootLaw2Derives
  · simpa [parityThresholdLongLaw, parityThresholdXYZ,
      parityThresholdXXXYZ,
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3]
      using rootLaw3Derives

private theorem derivesParityThreshold {left right : Word Nat}
    (derivation :
      Derives commutativeParityThresholdFiveBasis left right) :
    Derives rootBasis left right :=
  derivation.transport parityThresholdAxiomsDerive

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right :=
  derivesParityThreshold
    (parityThresholdDerivesPermutation left right permutation)

private theorem derivesLongSupportParity
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (support :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (parity :
      ∀ letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2) :
    Derives rootBasis left right :=
  derivesParityThreshold <|
    parityThresholdDerivesLongSupportParity
      left right leftLong rightLong support parity

private theorem word_length_positive (word : Word Nat) :
    1 ≤ word.toList.length := by
  cases word
  simp [Word.toList]

private theorem length_eq_twice_of_square
    {word squareRoot : Word Nat}
    (wordEq : word = squareRoot ++ squareRoot) :
    word.toList.length =
      squareRoot.toList.length + squareRoot.toList.length := by
  rw [wordEq, Word.toList_append, List.length_append]

private def hasParityDecoration (word : Word Nat) : Bool :=
  match word.tail with
  | [] => false
  | [second] => decide (word.head = second)
  | _ :: _ :: _ => true

private theorem hasParityDecoration_eq_true_iff (word : Word Nat) :
    hasParityDecoration word = true ↔
      SemigroupBasis.CoRoots.S5_16.InParityStratum word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          constructor
          · simp [hasParityDecoration]
          · intro shape
            rcases shape with ⟨squareRoot, wordEq⟩ | long
            · have lengths :=
                length_eq_twice_of_square wordEq
              simp [Word.toList] at lengths
              have positive := word_length_positive squareRoot
              omega
            · simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil =>
              constructor
              · intro decorated
                have same : head = second := by
                  simpa [hasParityDecoration] using decorated
                subst second
                exact Or.inl ⟨Word.singleton head, rfl⟩
              · intro shape
                rcases shape with ⟨squareRoot, wordEq⟩ | long
                · have lengths := length_eq_twice_of_square wordEq
                  cases squareRoot with
                  | mk squareHead squareTail =>
                      cases squareTail with
                      | nil =>
                          have lists := congrArg Word.toList wordEq
                          have listEq :
                              [head, second] = [squareHead, squareHead] := by
                            simpa [Word.toList] using lists
                          injection listEq with headEq tailEq
                          injection tailEq with secondEq
                          have same : head = second :=
                            headEq.trans secondEq.symm
                          simpa [hasParityDecoration, same]
                      | cons next more =>
                          simp [Word.toList] at lengths
                          omega
                · simp [Word.toList] at long
          | cons third more =>
              constructor
              · intro _
                exact Or.inr <| by simp [Word.toList]
              · intro _
                rfl

private instance inParityStratumDecidable (word : Word Nat) :
    Decidable
      (SemigroupBasis.CoRoots.S5_16.InParityStratum word) :=
  if decorated : hasParityDecoration word = true then
    isTrue ((hasParityDecoration_eq_true_iff word).mp decorated)
  else
    isFalse (fun shape =>
      decorated ((hasParityDecoration_eq_true_iff word).mpr shape))

private theorem short_perm_of_support_parity
    {left right : List Nat}
    (leftBound : left.length ≤ 2)
    (rightBound : right.length ≤ 2)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (parity :
      ∀ letter, left.count letter % 2 = right.count letter % 2) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  have leftCountBound := List.count_le_length (a := letter) (l := left)
  have rightCountBound := List.count_le_length (a := letter) (l := right)
  have positiveEq : 0 < left.count letter ↔ 0 < right.count letter := by
    rw [List.count_pos_iff, List.count_pos_iff]
    exact support letter
  have coordinate := parity letter
  omega

/-- Root derivability is complete for support, coordinate parity, and the
`S5_17` square-or-long decoration. -/
private theorem derivesOfSupportParityStratum
    (left right : Word Nat)
    (support :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (parity :
      ∀ letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2)
    (stratum :
      SemigroupBasis.CoRoots.S5_16.InParityStratum left ↔
        SemigroupBasis.CoRoots.S5_16.InParityStratum right) :
    Derives rootBasis left right := by
  by_cases leftLong : 3 ≤ left.toList.length
  · by_cases rightLong : 3 ≤ right.toList.length
    · exact derivesLongSupportParity
        left right leftLong rightLong support parity
    · have rightShape := stratum.mp (Or.inr leftLong)
      rcases rightShape with ⟨squareRoot, rfl⟩ | rightLong'
      · let expanded :=
          ((squareRoot ++ squareRoot) ++ squareRoot) ++ squareRoot
        have expand :
            Derives rootBasis (squareRoot ++ squareRoot) expanded := by
          simpa [expanded] using derivesFourExpansion squareRoot
        have expandedLong : 3 ≤ expanded.toList.length := by
          simp only [expanded, Word.toList_append, List.length_append]
          have positive := word_length_positive squareRoot
          omega
        have expandedSupport :
            ∀ letter,
              letter ∈ left.toList ↔ letter ∈ expanded.toList := by
          intro letter
          have coordinate := support letter
          simpa [expanded, Word.toList_append] using coordinate
        have expandedParity :
            ∀ letter,
              left.toList.count letter % 2 =
                expanded.toList.count letter % 2 := by
          intro letter
          have coordinate := parity letter
          simp only [expanded, Word.toList_append,
            List.count_append] at coordinate ⊢
          omega
        exact Derives.trans
          (derivesLongSupportParity left expanded
            leftLong expandedLong expandedSupport expandedParity)
          (Derives.symm expand)
      · exact False.elim (rightLong rightLong')
  · by_cases rightLong : 3 ≤ right.toList.length
    · have leftShape := stratum.mpr (Or.inr rightLong)
      rcases leftShape with ⟨squareRoot, rfl⟩ | leftLong'
      · let expanded :=
          ((squareRoot ++ squareRoot) ++ squareRoot) ++ squareRoot
        have expand :
            Derives rootBasis (squareRoot ++ squareRoot) expanded := by
          simpa [expanded] using derivesFourExpansion squareRoot
        have expandedLong : 3 ≤ expanded.toList.length := by
          simp only [expanded, Word.toList_append, List.length_append]
          have positive := word_length_positive squareRoot
          omega
        have expandedSupport :
            ∀ letter,
              letter ∈ expanded.toList ↔ letter ∈ right.toList := by
          intro letter
          have coordinate := support letter
          simpa [expanded, Word.toList_append] using coordinate
        have expandedParity :
            ∀ letter,
              expanded.toList.count letter % 2 =
                right.toList.count letter % 2 := by
          intro letter
          have coordinate := parity letter
          simp only [expanded, Word.toList_append,
            List.count_append] at coordinate ⊢
          omega
        exact Derives.trans expand <|
          derivesLongSupportParity expanded right
            expandedLong rightLong expandedSupport expandedParity
      · exact False.elim (leftLong leftLong')
    · have leftBound : left.toList.length ≤ 2 := by omega
      have rightBound : right.toList.length ≤ 2 := by omega
      exact derivesPermutation left right <|
        short_perm_of_support_parity
          leftBound rightBound support parity

/-! ## The `S5_17` decoration -/

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def tripleThen (first second : Nat) : Word Nat :=
  ⟨first, [first, first, second]⟩

private theorem pair_tripleThen_sameParity (first second : Nat) :
    SemigroupBasis.CoRoots.S5_58.SameParity
      (wordOfCons first [second]) (tripleThen first second) := by
  intro letter
  simp only [wordOfCons, tripleThen, Word.toList]
  by_cases letterFirst : letter = first
  · subst letter
    by_cases same : first = second
    · subst second
      simp
    · simp [Ne.symm same]
  · simp [Ne.symm letterFirst]

private theorem validDistinctPair_not_long
    (table : FiniteTable)
    (modelsTable :
      Models table.semigroup SemigroupBasis.CoRoots.S5_17.basis)
    (leftValue rightValue : Fin table.order)
    (shortLongNe :
      table.mul leftValue rightValue ≠
        table.mul
          (table.mul (table.mul leftValue leftValue) leftValue)
          rightValue)
    {first second : Nat} (different : first ≠ second)
    (word : Word Nat) (wordLong : 3 ≤ word.toList.length)
    (valid :
      (Identity.mk (wordOfCons first [second]) word).SatisfiedBy
        table.semigroup)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity
        (wordOfCons first [second]) word) :
    False := by
  have canonicalParity :
      SemigroupBasis.CoRoots.S5_58.SameParity
        word (tripleThen first second) := by
    intro letter
    exact (parity letter).symm.trans
      (pair_tripleThen_sameParity first second letter)
  have canonicalLong :
      3 ≤ (tripleThen first second).toList.length := by
    simp [tripleThen, Word.toList]
  have normalize :=
    SemigroupBasis.CoRoots.S5_17.derivesLongOfParityEq
      word (tripleThen first second)
      wordLong canonicalLong canonicalParity
  have normalizedValid :
      (Identity.mk
        (wordOfCons first [second])
        (tripleThen first second)).SatisfiedBy table.semigroup := by
    intro valuation
    exact (valid valuation).trans
      (normalize.sound modelsTable valuation)
  let valuation : Nat → Fin table.order :=
    fun letter => if letter = first then leftValue else rightValue
  have evaluated := normalizedValid valuation
  have valueFirst : valuation first = leftValue := by
    simp [valuation]
  have valueSecond : valuation second = rightValue := by
    simp [valuation, Ne.symm different]
  change
    table.mul (valuation first) (valuation second) =
      table.mul
        (table.mul
          (table.mul (valuation first) (valuation first))
          (valuation first))
        (valuation second) at evaluated
  rw [valueFirst, valueSecond] at evaluated
  exact shortLongNe evaluated

private theorem validDistinctPair_not_stratum
    {first second : Nat} (different : first ≠ second)
    (word : Word Nat)
    (wordShape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum word)
    (valid :
      (Identity.mk (wordOfCons first [second]) word).SatisfiedBy
        rightTable.semigroup)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity
        (wordOfCons first [second]) word) :
    False := by
  rcases wordShape with ⟨squareRoot, rfl⟩ | wordLong
  · have coordinate := parity first
    have leftCount :
        (wordOfCons first [second]).toList.count first = 1 := by
      simp [wordOfCons, Word.toList, different, Ne.symm different]
    rw [leftCount] at coordinate
    simp only [Word.toList_append, List.count_append] at coordinate
    omega
  · exact
      validDistinctPair_not_long rightTable
        SemigroupBasis.CoRoots.S5_17Family.S5_17.models
        (⟨2, by decide⟩ : Fin rightTable.order)
        (⟨3, by decide⟩ : Fin rightTable.order)
        (by decide) different word wordLong valid parity

private theorem pair_of_length_two
    (word : Word Nat) (lengthTwo : word.toList.length = 2) :
    ∃ first second, word = wordOfCons first [second] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at lengthTwo
      | cons next rest =>
          cases rest with
          | nil =>
              exact ⟨head, next, rfl⟩
          | cons third more =>
              simp [Word.toList] at lengthTwo

private theorem inParityStratum_length_two
    {word : Word Nat}
    (shape : SemigroupBasis.CoRoots.S5_16.InParityStratum word) :
    2 ≤ word.toList.length := by
  rcases shape with ⟨squareRoot, rfl⟩ | long
  · simp only [Word.toList_append, List.length_append]
    have positive := word_length_positive squareRoot
    omega
  · omega

private theorem s5_17_shape_forward
    (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity left right)
    (singleton :
      left.toList.length = 1 ↔ right.toList.length = 1)
    (leftShape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum left) :
    SemigroupBasis.CoRoots.S5_16.InParityStratum right := by
  apply Decidable.byContradiction
  intro rightNotShape
  have leftTwo := inParityStratum_length_two leftShape
  have leftNotOne : left.toList.length ≠ 1 := by omega
  have rightNotOne : right.toList.length ≠ 1 := by
    intro rightOne
    exact leftNotOne (singleton.mpr rightOne)
  have rightNotLong : ¬3 ≤ right.toList.length := by
    intro rightLong
    exact rightNotShape (Or.inr rightLong)
  have rightPositive := word_length_positive right
  have rightTwo : right.toList.length = 2 := by omega
  obtain ⟨first, second, rightEq⟩ :=
    pair_of_length_two right rightTwo
  rw [rightEq] at valid parity rightNotShape
  have different : first ≠ second := by
    intro same
    subst second
    apply rightNotShape
    exact Or.inl ⟨Word.singleton first, rfl⟩
  have validSymm :
      (Identity.mk (wordOfCons first [second]) left).SatisfiedBy
        rightTable.semigroup := by
    intro valuation
    exact (valid valuation).symm
  have paritySymm :
      SemigroupBasis.CoRoots.S5_58.SameParity
        (wordOfCons first [second]) left :=
    fun letter => (parity letter).symm
  exact validDistinctPair_not_stratum
    different left leftShape validSymm paritySymm

private theorem s5_17_valid_inParityStratum_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_16.InParityStratum identity.lhs ↔
      SemigroupBasis.CoRoots.S5_16.InParityStratum identity.rhs := by
  have parity :=
    SemigroupBasis.CoRoots.S5_17Family.S5_17.valid_parity
      identity valid
  have singleton :=
    SemigroupBasis.CoRoots.S5_17Family.S5_17.valid_length_one
      identity valid
  constructor
  · exact s5_17_shape_forward
      identity.lhs identity.rhs valid parity singleton
  · exact s5_17_shape_forward
      identity.rhs identity.lhs
      (fun valuation => (valid valuation).symm)
      (fun letter => (parity letter).symm)
      singleton.symm

/-! ## Canonical decorated parity lists -/

private def wordOfList (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => wordOfCons head tail

private theorem wordOfList_toList
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfList fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

private def sortLetters (letters : List Nat) : List Nat :=
  letters.mergeSort (fun left right : Nat => decide (left ≤ right))

private theorem sortLetters_perm (letters : List Nat) :
    (sortLetters letters).Perm letters := by
  exact List.mergeSort_perm _ _

private theorem sortLetters_pairwise (letters : List Nat) :
    (sortLetters letters).Pairwise (fun left right => left ≤ right) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted := List.pairwise_mergeSort transitive total letters
  simpa [sortLetters] using
    (sorted.imp fun relation => of_decide_eq_true relation)

private theorem sortLetters_eq_of_perm
    {left right : List Nat} (permutation : left.Perm right) :
    sortLetters left = sortLetters right := by
  have sortedPermutation :
      (sortLetters left).Perm (sortLetters right) :=
    (sortLetters_perm left).trans <|
      permutation.trans (sortLetters_perm right).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (sortLetters_pairwise left) (sortLetters_pairwise right)
    sortedPermutation

private def parityList (word : Word Nat) : List Nat :=
  sortLetters (positiveParityReduce word.toList)

/-- Add the unique square decoration when the positive parity list is too
short to record membership in the `S5_17` square-or-long stratum. -/
private def decorate : List Nat → List Nat
  | [] => []
  | [first] => [first, first, first]
  | [first, second] =>
      if first = second then [first, second]
      else [first, first, first, second]
  | first :: second :: third :: rest => first :: second :: third :: rest

private theorem decorate_mem_iff (letters : List Nat) (tested : Nat) :
    tested ∈ decorate letters ↔ tested ∈ letters := by
  cases letters with
  | nil =>
      simp [decorate]
  | cons first tail =>
      cases tail with
      | nil =>
          simp [decorate]
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases same : first = second
              · simp [decorate, same]
              · simp [decorate, same]
          | cons third more =>
              simp [decorate]

private theorem decorate_count_mod_two
    (letters : List Nat) (tested : Nat) :
    (decorate letters).count tested % 2 =
      letters.count tested % 2 := by
  cases letters with
  | nil =>
      simp [decorate]
  | cons first tail =>
      cases tail with
      | nil =>
          by_cases testedFirst : tested = first
          · subst tested
            simp [decorate]
          · simp [decorate, testedFirst, Ne.symm testedFirst]
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases same : first = second
              · subst second
                simp [decorate]
              · by_cases testedFirst : tested = first
                · subst tested
                  simp [decorate, same, Ne.symm same]
                · by_cases testedSecond : tested = second
                  · subst tested
                    simp [decorate, same, testedFirst, Ne.symm same]
                  · simp [decorate, same, testedFirst, testedSecond,
                      Ne.symm testedFirst, Ne.symm testedSecond]
          | cons third more =>
              simp [decorate]

private theorem positiveParityReduce_word_ne_nil (word : Word Nat) :
    positiveParityReduce word.toList ≠ [] := by
  intro empty
  have present : word.head ∈ positiveParityReduce word.toList :=
    (mem_positiveParityReduce_iff _ _).mpr (by simp [Word.toList])
  rw [empty] at present
  simp at present

private theorem sortLetters_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    sortLetters letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      intro sortedEmpty
      have permutation := sortLetters_perm (head :: tail)
      rw [sortedEmpty] at permutation
      exact List.not_perm_cons_nil permutation.symm

private theorem parityList_ne_nil (word : Word Nat) :
    parityList word ≠ [] := by
  exact sortLetters_ne_nil (positiveParityReduce_word_ne_nil word)

private theorem parityList_mem_iff (word : Word Nat) (tested : Nat) :
    tested ∈ parityList word ↔ tested ∈ word.toList := by
  exact (sortLetters_perm (positiveParityReduce word.toList)).mem_iff.trans
    (mem_positiveParityReduce_iff tested word.toList)

private theorem parityList_count_mod_two
    (word : Word Nat) (tested : Nat) :
    (parityList word).count tested % 2 =
      word.toList.count tested % 2 := by
  have countEq :=
    List.perm_iff_count.mp
      (sortLetters_perm (positiveParityReduce word.toList)) tested
  change
    (sortLetters (positiveParityReduce word.toList)).count tested % 2 =
      word.toList.count tested % 2
  rw [countEq, positiveParityReduce_count_mod_two]

private theorem decorate_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    decorate letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons first tail =>
      cases tail with
      | nil => simp [decorate]
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases same : first = second <;> simp [decorate, same]
          | cons third more => simp [decorate]

private def normalList (word : Word Nat) : List Nat :=
  if SemigroupBasis.CoRoots.S5_16.InParityStratum word then
    decorate (parityList word)
  else
    parityList word

private def normal (word : Word Nat) : Word Nat :=
  wordOfList word.head (normalList word)

private theorem normalList_ne_nil (word : Word Nat) :
    normalList word ≠ [] := by
  by_cases shape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum word
  · simpa [normalList, shape] using
      decorate_ne_nil (parityList_ne_nil word)
  · simpa [normalList, shape] using parityList_ne_nil word

private theorem normal_toList (word : Word Nat) :
    (normal word).toList = normalList word := by
  exact wordOfList_toList word.head (normalList_ne_nil word)

private theorem normal_support (word : Word Nat) (tested : Nat) :
    tested ∈ (normal word).toList ↔ tested ∈ word.toList := by
  rw [normal_toList]
  by_cases shape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum word
  · rw [normalList, if_pos shape, decorate_mem_iff,
      parityList_mem_iff]
  · rw [normalList, if_neg shape, parityList_mem_iff]

private theorem normal_parity (word : Word Nat) (tested : Nat) :
    (normal word).toList.count tested % 2 =
      word.toList.count tested % 2 := by
  rw [normal_toList]
  by_cases shape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum word
  · rw [normalList, if_pos shape, decorate_count_mod_two,
      parityList_count_mod_two]
  · rw [normalList, if_neg shape, parityList_count_mod_two]

private theorem wordOfList_decorate_inParityStratum
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    SemigroupBasis.CoRoots.S5_16.InParityStratum
      (wordOfList fallback (decorate letters)) := by
  cases letters with
  | nil => contradiction
  | cons first tail =>
      cases tail with
      | nil =>
          exact Or.inr <| by
            simp [decorate, wordOfList, wordOfCons, Word.toList]
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases same : first = second
              · subst second
                exact Or.inl ⟨Word.singleton first, by
                  simpa [decorate, wordOfList, wordOfCons] using
                    (Word.singleton_append first
                      (Word.singleton first)).symm⟩
              · exact Or.inr <| by
                  simp [decorate, same, wordOfList, wordOfCons,
                    Word.toList]
          | cons third more =>
              exact Or.inr <| by
                simp [decorate, wordOfList, wordOfCons, Word.toList]

private theorem normal_inParityStratum_of
    (word : Word Nat)
    (shape : SemigroupBasis.CoRoots.S5_16.InParityStratum word) :
    SemigroupBasis.CoRoots.S5_16.InParityStratum (normal word) := by
  simpa [normal, normalList, shape] using
    wordOfList_decorate_inParityStratum word.head
      (parityList_ne_nil word)

private theorem positiveParityReduce_eq_self_of_length_le_two
    {letters : List Nat} (bound : letters.length ≤ 2) :
    positiveParityReduce letters = letters := by
  cases letters with
  | nil =>
      rfl
  | cons first tail =>
      cases tail with
      | nil =>
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              have singletonReduce :
                  positiveParityReduce [second] = [second] := rfl
              change
                (if (positiveParityReduce [second]).count first < 2 then
                  first :: positiveParityReduce [second]
                else
                  (positiveParityReduce [second]).erase first) =
                  [first, second]
              have countBound :=
                List.count_le_length (a := first) (l := [second])
              have countShort : [second].count first < 2 := by
                simpa using Nat.lt_succ_of_le countBound
              rw [singletonReduce, if_pos countShort]
          | cons third more =>
              simp at bound

private theorem normalizes (word : Word Nat) :
    Derives rootBasis word (normal word) := by
  by_cases shape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum word
  · exact derivesOfSupportParityStratum word (normal word)
      (fun tested => (normal_support word tested).symm)
      (fun tested => (normal_parity word tested).symm)
      ⟨fun _ => normal_inParityStratum_of word shape,
        fun _ => shape⟩
  · have notLong : ¬3 ≤ word.toList.length := by
      intro long
      exact shape (Or.inr long)
    have short : word.toList.length ≤ 2 := by omega
    have reducedEq :=
      positiveParityReduce_eq_self_of_length_le_two short
    apply derivesPermutation word (normal word)
    rw [normal_toList, normalList, if_neg shape, parityList, reducedEq]
    exact (sortLetters_perm word.toList).symm

private theorem normal_eq_of_invariants
    (left right : Word Nat)
    (support :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (parity :
      ∀ letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2)
    (stratum :
      SemigroupBasis.CoRoots.S5_16.InParityStratum left ↔
        SemigroupBasis.CoRoots.S5_16.InParityStratum right) :
    normal left = normal right := by
  have reducedPermutation := positiveParityReduce_perm support parity
  have sortedEq := sortLetters_eq_of_perm reducedPermutation
  apply Word.toList_injective
  rw [normal_toList, normal_toList]
  by_cases leftShape :
      SemigroupBasis.CoRoots.S5_16.InParityStratum left
  · have rightShape := stratum.mp leftShape
    simpa [normalList, leftShape, rightShape, parityList] using
      congrArg decorate sortedEq
  · have rightShape :
        ¬SemigroupBasis.CoRoots.S5_16.InParityStratum right := by
      intro shape
      exact leftShape (stratum.mpr shape)
    simpa [normalList, leftShape, rightShape, parityList] using sortedEq

/-! ## Factor separation -/

private theorem s2_3_table_eq_canonical_catalogue :
    SemigroupBasis.Generated.S2_3.table =
      SemigroupBasis.Generated.Catalogue.S2_3.table := by
  unfold SemigroupBasis.Generated.S2_3.table
    SemigroupBasis.Generated.Catalogue.S2_3.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

private theorem catalogueS2_3_table_eq_semilatticeTwo :
    SemigroupBasis.Generated.Catalogue.S2_3.table = semilatticeTwo := by
  calc
    SemigroupBasis.Generated.Catalogue.S2_3.table =
        SemigroupBasis.Generated.S2_3.table :=
      s2_3_table_eq_canonical_catalogue.symm
    _ = semilatticeTwo :=
      SemigroupBasis.Generated.S2_3.table_eq_catalogue_model

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem separates
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S2_3.table.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    normal identity.lhs = normal identity.rhs := by
  have leftValid' :
      identity.SatisfiedBy semilatticeTwo.semigroup :=
    satisfiedBy_of_table_eq
      catalogueS2_3_table_eq_semilatticeTwo identity leftValid
  exact normal_eq_of_invariants identity.lhs identity.rhs
    (semilatticeValid_support_eq identity leftValid')
    (SemigroupBasis.CoRoots.S5_17Family.S5_17.valid_parity
      identity rightValid)
    (s5_17_valid_inParityStratum_iff identity rightValid)

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_1250`. -/
theorem basisFor :
    BasisFor rootSemigroup rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_1250.subdirectPair.basisFor_of_normalForm
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.models
      normalizes separates

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_1250

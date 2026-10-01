import SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20Prelude
import SemigroupBasis.CoRoots.Order6FactorPairS2S594Normal
import SemigroupBasis.CoRoots.S5_1000DualTransport
import SemigroupBasis.CoRoots.S5_1155Completeness
import SemigroupBasis.FiniteCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20

open SemigroupBasis
open SemigroupBasis.Examples

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateTwoWords
    (x y : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def instantiateFourWords
    (x y z t : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat -> Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (value : Word Nat)
    (first second : Nat -> Word Nat) :
    (value.bind first).bind second =
      value.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (value : Word Nat) :
    value.bind Word.singleton = value := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem basisPower :
    Derives basis (word 0 [0]) (word 0 [0, 0, 0, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0]) (word 0 [0, 0, 0, 0])) (by decide)

private theorem basisHeadMovement :
    Derives basis
      (word 0 [0, 0, 1, 0])
      (word 1 [0, 1, 1, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 0, 1, 0])
    (word 1 [0, 1, 1, 1])) (by decide)

private theorem basisSquareInterleave :
    Derives basis (word 0 [0, 1, 1]) (word 0 [1, 0, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1]) (word 0 [1, 0, 1])) (by decide)

private theorem basisSquareFinalSwitch :
    Derives basis (word 0 [0, 1, 1]) (word 0 [1, 1, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1]) (word 0 [1, 1, 0])) (by decide)

private theorem basisSquareInitialSwitch :
    Derives basis (word 0 [0, 1, 1]) (word 1 [0, 0, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1]) (word 1 [0, 0, 1])) (by decide)

private theorem basisAttachmentFinal :
    Derives basis
      (word 0 [0, 1, 2, 1])
      (word 0 [1, 1, 2, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 2, 1])
    (word 0 [1, 1, 2, 0])) (by decide)

private theorem basisAttachmentInitial :
    Derives basis
      (word 0 [0, 1, 2, 1])
      (word 1 [0, 0, 2, 1]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 2, 1])
    (word 1 [0, 0, 2, 1])) (by decide)

private theorem basisOpenInteriorSwap :
    Derives basis
      (word 0 [1, 2, 3]) (word 0 [2, 1, 3]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [1, 2, 3]) (word 0 [2, 1, 3])) (by decide)

private theorem basisContextualPeriod :
    Derives basis
      (word 0 [1, 2]) (word 0 [1, 1, 1, 1, 2]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [1, 2]) (word 0 [1, 1, 1, 1, 2])) (by decide)

private theorem derivesPowerExpansion (block : Word Nat) :
    Derives basis
      (block ++ block)
      ((((block ++ block) ++ block) ++ block) ++ block) := by
  have substituted :=
    Derives.subst basisPower
      (instantiateTwoWords block block)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInterleave (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareFinalSwitch (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInitialSwitch (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisSquareInitialSwitch
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentFinal
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisAttachmentFinal
      (instantiateThreeWords x y z)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentInitial
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have substituted :=
    Derives.subst basisAttachmentInitial
      (instantiateThreeWords x y z)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesOpenInteriorSwap
    (x y z t : Word Nat) :
    Derives basis
      (((x ++ y) ++ z) ++ t)
      (((x ++ z) ++ y) ++ t) := by
  have substituted :=
    Derives.subst basisOpenInteriorSwap
      (instantiateFourWords x y z t)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesContextualPeriodExpansion
    (pre block suf : Word Nat) :
    Derives basis
      ((pre ++ block) ++ suf)
      (((((pre ++ block) ++ block) ++ block) ++ block) ++ suf) := by
  have substituted :=
    Derives.subst basisContextualPeriod
      (instantiateThreeWords pre block suf)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesHeadMovement
    (x y : Word Nat) :
    Derives basis
      ((((x ++ x) ++ x) ++ y) ++ x)
      ((((y ++ x) ++ y) ++ y) ++ y) := by
  have substituted :=
    Derives.subst basisHeadMovement
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The short bounded search misses this consequence because the derivation
first expands the middle block and then returns through the head-movement
law. It is the period-three replacement for endpoint duplication. -/
theorem derivesRepeatedEndpointExpansion
    (x middle : Word Nat) :
    Derives basis
      ((x ++ middle) ++ x)
      (((((x ++ x) ++ x) ++ x) ++ middle) ++ x) := by
  have expandMiddle :=
    derivesContextualPeriodExpansion x middle x
  have collectLeft :=
    Derives.symm (derivesSquareFinalSwitch x (middle ++ middle))
  have collectLeft' :
      Derives basis
        (((((x ++ middle) ++ middle) ++ middle) ++ middle) ++ x)
        ((x ++ x) ++
          ((middle ++ middle) ++ (middle ++ middle))) := by
    simpa [Word.append_assoc] using collectLeft
  have interleavePrefix :=
    Derives.appendRight
      (derivesSquareInterleave x middle)
      (middle ++ middle)
  have interleavePrefix' :
      Derives basis
        ((x ++ x) ++
          ((middle ++ middle) ++ (middle ++ middle)))
        (((x ++ middle) ++ x) ++
          ((middle ++ middle) ++ middle)) := by
    simpa [Word.append_assoc] using interleavePrefix
  have moveBack :=
    Derives.prepend x (Derives.symm (derivesHeadMovement x middle))
  have moveBack' :
      Derives basis
        (((x ++ middle) ++ x) ++
          ((middle ++ middle) ++ middle))
        (((((x ++ x) ++ x) ++ x) ++ middle) ++ x) := by
    simpa [Word.append_assoc] using moveBack
  exact expandMiddle.trans <|
    collectLeft'.trans <| interleavePrefix'.trans moveBack'

private abbrev endpointWord :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints

@[simp]
private theorem toListEndpointWord
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (endpointWord initial middle final).toList =
      initial :: middle ++ [final] :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints
    initial middle final

private def wordOfPrefixFinal : List Nat -> Nat -> Word Nat
  | [], final => Word.singleton final
  | head :: tail, final => Word.mk head (tail ++ [final])

@[simp]
private theorem toListWordOfPrefixFinal
    (wordPrefix : List Nat) (final : Nat) :
    (wordOfPrefixFinal wordPrefix final).toList =
      wordPrefix ++ [final] := by
  cases wordPrefix <;>
    simp [wordOfPrefixFinal, Word.toList, Word.singleton]

@[simp]
private theorem wordOfPrefixFinalCons
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfPrefixFinal (head :: tail) final =
      Word.singleton head ++ wordOfPrefixFinal tail final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toListWordOfPrefixFinal, toListWordOfPrefixFinal]
  rfl

private theorem endpointWordEq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toListWordOfPrefixFinal, toListEndpointWord]
  rfl

private theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (endpointWord initial left final)
      (endpointWord initial right final) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.derivesMiddlePermutationOfOpenSwap
    derivesOpenInteriorSwap initial final permutation

private theorem threeCopiesPerm
    (letter : Nat) (letters : List Nat)
    (countEq : letters.count letter = 3) :
    letters.Perm
      (letter :: letter :: letter ::
        (((letters.erase letter).erase letter).erase letter)) := by
  have present : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase present
  have countOnce : (letters.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEq]
  have presentOnce : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase presentOnce
  have countTwice :
      ((letters.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, countOnce]
  have presentTwice :
      letter ∈ (letters.erase letter).erase letter :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons letter <|
    second.trans <| List.Perm.cons letter <|
      List.perm_cons_erase presentTwice

private theorem derivesDeleteInteriorTriple
    (initial final letter : Nat) (pre reduced : List Nat)
    (countEq : reduced.count letter = 3) :
    Derives basis
      (endpointWord initial (pre ++ letter :: reduced) final)
      (endpointWord initial
        (pre ++ (reduced.erase letter).erase letter) final) := by
  let remainder :=
    (((reduced.erase letter).erase letter).erase letter)
  have firstCount : (reduced.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEq]
  have secondCount :
      ((reduced.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, firstCount]
  have remainderCount : remainder.count letter = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondCount]
  have sourcePerm :
      (pre ++ letter :: reduced).Perm
        (letter :: letter :: letter :: letter ::
          (pre ++ remainder)) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = letter
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ (reduced.erase letter).erase letter).Perm
        (letter :: (pre ++ remainder)) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = letter
    · subst tested
      simp [firstCount, secondCount, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have arranged :=
    derivesMiddlePermutation initial final sourcePerm
  have contracted :=
    Derives.symm <|
      derivesContextualPeriodExpansion
        (Word.singleton initial)
        (Word.singleton letter)
        (wordOfPrefixFinal (pre ++ remainder) final)
  have contraction :
      Derives basis
        (endpointWord initial
          (letter :: letter :: letter :: letter ::
            (pre ++ remainder))
          final)
        (endpointWord initial (letter :: (pre ++ remainder)) final) := by
    simpa only [endpointWordEq, wordOfPrefixFinalCons,
      Word.append_assoc] using contracted
  exact arranged.trans <|
    contraction.trans
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesNormalizeMiddleAux :
    ∀ (initial : Nat) (pre middle : List Nat) (final : Nat),
      Derives basis
        (endpointWord initial (pre ++ middle) final)
        (endpointWord initial
          (pre ++ positiveModThreeReduce middle) final)
  | initial, pre, [], final => by
      exact Derives.refl _
  | initial, pre, letter :: tail, final => by
      have tailNormal :=
        derivesNormalizeMiddleAux initial (pre ++ [letter]) tail final
      let reduced := positiveModThreeReduce tail
      have firstStep :
          Derives basis
            (endpointWord initial (pre ++ letter :: tail) final)
            (endpointWord initial (pre ++ letter :: reduced) final) := by
        simpa [reduced, List.append_assoc] using tailNormal
      by_cases small : reduced.count letter < 3
      · have reduceEq :
            positiveModThreeReduce (letter :: tail) =
              letter :: reduced := by
          simp [positiveModThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep
      · have upper :=
          positiveModThreeReduce_count_le_three letter tail
        have upper' : reduced.count letter ≤ 3 := by
          simpa [reduced] using upper
        have lower : 3 ≤ reduced.count letter :=
          Nat.le_of_not_gt small
        have countEq : reduced.count letter = 3 := by
          omega
        have reduceEq :
            positiveModThreeReduce (letter :: tail) =
              (reduced.erase letter).erase letter := by
          simp [positiveModThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep.trans <|
          derivesDeleteInteriorTriple
            initial final letter pre reduced countEq
termination_by
  _ _ middle _ => middle.length

theorem derivesNormalizeMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (endpointWord initial middle final)
      (endpointWord initial
        (positiveModThreeReduce middle) final) := by
  simpa using derivesNormalizeMiddleAux initial [] middle final

theorem derivesAlignedEndpoints
    (initial final : Nat) {left right : List Nat}
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (residue :
      ∀ letter, left.count letter % 3 = right.count letter % 3) :
    Derives basis
      (endpointWord initial left final)
      (endpointWord initial right final) := by
  have leftNormal := derivesNormalizeMiddle initial left final
  have rightNormal := derivesNormalizeMiddle initial right final
  have middle :=
    derivesMiddlePermutation initial final
      (positiveModThreeReduce_perm support residue)
  exact leftNormal.trans <| middle.trans rightNormal.symm

private def toFinFour : Nat -> Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem s3_18_models :
    Models SemigroupBasis.Generated.S3_18.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_18.table basis toFinFour (by decide)

theorem s4_20_models :
    Models SemigroupBasis.Generated.S4_20.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_20.table basis toFinFour (by decide)

private def supportSeparator (tested : Nat) : Nat -> Fin 4 :=
  fun value => if value = tested then 0 else 3

private def initialSeparator (tested : Nat) : Nat -> Fin 4 :=
  fun value => if value = tested then 2 else 3

private def finalSeparator (tested : Nat) : Nat -> Fin 4 :=
  fun value => if value = tested then 1 else 3

private theorem supportIffOfValid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ tested,
      (tested ∈ leftInitial :: leftMiddle ∨ leftFinal = tested) ↔
        (tested ∈ rightInitial :: rightMiddle ∨ rightFinal = tested) := by
  intro tested
  have absentIff :
      (tested ∉ leftInitial :: leftMiddle ∧ leftFinal ≠ tested) ↔
        (tested ∉ rightInitial :: rightMiddle ∧
          rightFinal ≠ tested) := by
    constructor
    · intro leftAbsent
      apply
        (simpleEndpointsEval_supportSeparator_eq_three_iff
          tested rightInitial rightMiddle rightFinal).1
      exact (valid (supportSeparator tested)).symm.trans <|
        (simpleEndpointsEval_supportSeparator_eq_three_iff
          tested leftInitial leftMiddle leftFinal).2 leftAbsent
    · intro rightAbsent
      apply
        (simpleEndpointsEval_supportSeparator_eq_three_iff
          tested leftInitial leftMiddle leftFinal).1
      exact (valid (supportSeparator tested)).trans <|
        (simpleEndpointsEval_supportSeparator_eq_three_iff
          tested rightInitial rightMiddle rightFinal).2 rightAbsent
  constructor
  · intro leftPresent
    apply Decidable.byContradiction
    intro rightAbsent
    have rightAbsent' :
        tested ∉ rightInitial :: rightMiddle ∧
          rightFinal ≠ tested := by
      simpa [not_or] using rightAbsent
    have leftAbsent := absentIff.mpr rightAbsent'
    exact
      (by simpa [not_or] using leftAbsent :
        ¬(tested ∈ leftInitial :: leftMiddle ∨
          leftFinal = tested)) leftPresent
  · intro rightPresent
    apply Decidable.byContradiction
    intro leftAbsent
    have leftAbsent' :
        tested ∉ leftInitial :: leftMiddle ∧
          leftFinal ≠ tested := by
      simpa [not_or] using leftAbsent
    have rightAbsent := absentIff.mp leftAbsent'
    exact
      (by simpa [not_or] using rightAbsent :
        ¬(tested ∈ rightInitial :: rightMiddle ∨
          rightFinal = tested)) rightPresent

private theorem simpleInitialIffOfValid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ tested,
      (leftInitial = tested ∧ tested ∉ leftMiddle ∧
          leftFinal ≠ tested) ↔
        (rightInitial = tested ∧ tested ∉ rightMiddle ∧
          rightFinal ≠ tested) := by
  intro tested
  have evaluated := valid (initialSeparator tested)
  constructor
  · intro leftSimple
    have leftTwo :
        simpleEndpointsFour.semigroup.eval
            (initialSeparator tested)
            (endpointWord leftInitial leftMiddle leftFinal) =
              (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          tested leftInitial leftMiddle leftFinal).2 leftSimple
    have rightTwo := evaluated.symm.trans leftTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        tested rightInitial rightMiddle rightFinal).1 <| by
          simpa [initialSeparator] using rightTwo
  · intro rightSimple
    have rightTwo :
        simpleEndpointsFour.semigroup.eval
            (initialSeparator tested)
            (endpointWord rightInitial rightMiddle rightFinal) =
              (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          tested rightInitial rightMiddle rightFinal).2 rightSimple
    have leftTwo := evaluated.trans rightTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        tested leftInitial leftMiddle leftFinal).1 <| by
          simpa [initialSeparator] using leftTwo

private theorem simpleFinalIffOfValid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ tested,
      (leftFinal = tested ∧ tested ∉ leftInitial :: leftMiddle) ↔
        (rightFinal = tested ∧ tested ∉ rightInitial :: rightMiddle) := by
  intro tested
  have evaluated := valid (finalSeparator tested)
  constructor
  · intro leftSimple
    have leftOne :
        simpleEndpointsFour.semigroup.eval
            (finalSeparator tested)
            (endpointWord leftInitial leftMiddle leftFinal) =
              (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          tested leftInitial leftMiddle leftFinal).2 leftSimple
    have rightOne := evaluated.symm.trans leftOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        tested rightInitial rightMiddle rightFinal).1 <| by
          simpa [finalSeparator] using rightOne
  · intro rightSimple
    have rightOne :
        simpleEndpointsFour.semigroup.eval
            (finalSeparator tested)
            (endpointWord rightInitial rightMiddle rightFinal) =
              (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          tested rightInitial rightMiddle rightFinal).2 rightSimple
    have leftOne := evaluated.trans rightOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        tested leftInitial leftMiddle leftFinal).1 <| by
          simpa [finalSeparator] using leftOne

private theorem countEndpointWord
    (initial : Nat) (middle : List Nat) (final tested : Nat) :
    (endpointWord initial middle final).toList.count tested =
      [initial, final].count tested + middle.count tested := by
  simp only [toListEndpointWord, List.count_cons,
    List.count_append, List.count_nil, Nat.add_zero]
  omega

private theorem middleResidueOfAligned
    (initial final : Nat) (left right : List Nat)
    (valid :
      (Identity.mk
        (endpointWord initial left final)
        (endpointWord initial right final)).SatisfiedBy cyclicThree.semigroup) :
    ∀ tested, left.count tested % 3 = right.count tested % 3 := by
  have whole :=
    cyclicThreeValid_mod_eq
      (Identity.mk
        (endpointWord initial left final)
        (endpointWord initial right final)) valid
  intro tested
  have counts := whole tested
  rw [countEndpointWord, countEndpointWord] at counts
  omega

private theorem expandClosedMiddle
    (endpoint : Nat) (middle : List Nat)
    (absent : endpoint ∉ middle) :
    Derives basis
      (endpointWord endpoint middle endpoint)
      (endpointWord endpoint
        (endpoint :: endpoint :: endpoint :: middle) endpoint) := by
  cases middle with
  | nil =>
      simpa [endpointWord,
        SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        Word.singleton, Word.append, Word.append_assoc] using
          derivesPowerExpansion (Word.singleton endpoint)
  | cons next rest =>
      let middleWord := Word.mk next rest
      have expanded :=
        derivesRepeatedEndpointExpansion
          (Word.singleton endpoint) middleWord
      simpa [endpointWord,
        SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        middleWord, Word.singleton, Word.append, Word.append_assoc] using
          expanded

private theorem derivesClosedAligned
    (endpoint : Nat) {left right : List Nat}
    (wholeSupport :
      ∀ tested,
        (tested = endpoint ∨ tested ∈ left) ↔
          (tested = endpoint ∨ tested ∈ right))
    (residue :
      ∀ tested, left.count tested % 3 = right.count tested % 3) :
    Derives basis
      (endpointWord endpoint left endpoint)
      (endpointWord endpoint right endpoint) := by
  by_cases leftHas : endpoint ∈ left
  · by_cases rightHas : endpoint ∈ right
    · exact derivesAlignedEndpoints endpoint endpoint
        (fun tested => by
          by_cases same : tested = endpoint
          · subst tested
            simp [leftHas, rightHas]
          · simpa [same] using wholeSupport tested)
        residue
    · have rightCountZero : right.count endpoint = 0 :=
        List.count_eq_zero.mpr rightHas
      have leftPositive : 0 < left.count endpoint :=
        List.count_pos_iff.mpr leftHas
      have leftModZero : left.count endpoint % 3 = 0 := by
        rw [residue endpoint, rightCountZero]
      have leftNormal := derivesNormalizeMiddle endpoint left endpoint
      have rightExpanded := expandClosedMiddle endpoint right rightHas
      have bridge :
          Derives basis
            (endpointWord endpoint
              (positiveModThreeReduce left) endpoint)
            (endpointWord endpoint
              (endpoint :: endpoint :: endpoint :: right) endpoint) := by
        apply derivesAlignedEndpoints
        · intro tested
          by_cases same : tested = endpoint
          · subst tested
            have reducedCount :
                (positiveModThreeReduce left).count endpoint = 3 := by
              have upper :=
                positiveModThreeReduce_count_le_three endpoint left
              have positive :=
                List.count_pos_iff.mpr <|
                  (mem_positiveModThreeReduce_iff endpoint left).2 leftHas
              have modEq :=
                positiveModThreeReduce_count_mod_three endpoint left
              omega
            have reducedMember :
                endpoint ∈ positiveModThreeReduce left :=
              List.count_pos_iff.mp (by omega)
            constructor
            · intro _
              simp
            · intro _
              exact reducedMember
          · simp [same, Ne.symm same,
              mem_positiveModThreeReduce_iff]
            simpa [same] using wholeSupport tested
        · intro tested
          by_cases same : tested = endpoint
          · subst tested
            rw [positiveModThreeReduce_count_mod_three,
              leftModZero]
            simp [rightCountZero]
          · rw [positiveModThreeReduce_count_mod_three]
            simp [same, Ne.symm same, residue tested]
      exact leftNormal.trans <| bridge.trans rightExpanded.symm
  · by_cases rightHas : endpoint ∈ right
    · have leftCountZero : left.count endpoint = 0 :=
        List.count_eq_zero.mpr leftHas
      have rightPositive : 0 < right.count endpoint :=
        List.count_pos_iff.mpr rightHas
      have rightModZero : right.count endpoint % 3 = 0 := by
        rw [← residue endpoint, leftCountZero]
      have leftExpanded := expandClosedMiddle endpoint left leftHas
      have rightNormal := derivesNormalizeMiddle endpoint right endpoint
      have bridge :
          Derives basis
            (endpointWord endpoint
              (positiveModThreeReduce right) endpoint)
            (endpointWord endpoint
              (endpoint :: endpoint :: endpoint :: left) endpoint) := by
        apply derivesAlignedEndpoints
        · intro tested
          by_cases same : tested = endpoint
          · subst tested
            have reducedCount :
                (positiveModThreeReduce right).count endpoint = 3 := by
              have upper :=
                positiveModThreeReduce_count_le_three endpoint right
              have positive :=
                List.count_pos_iff.mpr <|
                  (mem_positiveModThreeReduce_iff endpoint right).2 rightHas
              have modEq :=
                positiveModThreeReduce_count_mod_three endpoint right
              omega
            have reducedMember :
                endpoint ∈ positiveModThreeReduce right :=
              List.count_pos_iff.mp (by omega)
            constructor
            · intro _
              simp
            · intro _
              exact reducedMember
          · simp [same, Ne.symm same,
              mem_positiveModThreeReduce_iff]
            simpa [same] using (wholeSupport tested).symm
        · intro tested
          by_cases same : tested = endpoint
          · subst tested
            rw [positiveModThreeReduce_count_mod_three,
              rightModZero]
            simp [leftCountZero]
          · rw [positiveModThreeReduce_count_mod_three]
            simp [same, Ne.symm same, residue tested]
      exact leftExpanded.trans <|
        bridge.symm.trans rightNormal.symm
    · exact derivesAlignedEndpoints endpoint endpoint
        (fun tested => by
          by_cases same : tested = endpoint
          · subst tested
            simp [leftHas, rightHas]
          · simpa [same] using wholeSupport tested)
        residue

private theorem derivesAlignedOfFactorValid
    (initial final : Nat) (left right : List Nat)
    (cyclicValid :
      (Identity.mk
        (endpointWord initial left final)
        (endpointWord initial right final)).SatisfiedBy cyclicThree.semigroup)
    (simpleValid :
      (Identity.mk
        (endpointWord initial left final)
        (endpointWord initial right final)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    Derives basis
      (endpointWord initial left final)
      (endpointWord initial right final) := by
  have residue :=
    middleResidueOfAligned initial final left right cyclicValid
  have wholeSupport :=
    supportIffOfValid initial left final
      initial right final simpleValid
  by_cases closed : initial = final
  · subst final
    apply derivesClosedAligned initial
    · intro tested
      constructor
      · intro leftSupport
        have leftSupport' :
            tested ∈ initial :: left ∨ initial = tested := by
          rcases leftSupport with atEndpoint | inMiddle
          · exact Or.inl (by simp [atEndpoint])
          · exact Or.inl (List.mem_cons_of_mem initial inMiddle)
        have rightSupport' := (wholeSupport tested).mp leftSupport'
        rcases rightSupport' with inWord | atEndpoint
        · simpa only [List.mem_cons] using inWord
        · exact Or.inl (Eq.symm atEndpoint)
      · intro rightSupport
        have rightSupport' :
            tested ∈ initial :: right ∨ initial = tested := by
          rcases rightSupport with atEndpoint | inMiddle
          · exact Or.inl (by simp [atEndpoint])
          · exact Or.inl (List.mem_cons_of_mem initial inMiddle)
        have leftSupport' := (wholeSupport tested).mpr rightSupport'
        rcases leftSupport' with inWord | atEndpoint
        · simpa only [List.mem_cons] using inWord
        · exact Or.inl (Eq.symm atEndpoint)
    · exact residue
  · have initialSimple :=
      simpleInitialIffOfValid initial left final
        initial right final simpleValid
    have finalSimple :=
      simpleFinalIffOfValid initial left final
        initial right final simpleValid
    apply derivesAlignedEndpoints initial final
    · intro tested
      by_cases isInitial : tested = initial
      · subst tested
        have absent :
            initial ∉ left ↔ initial ∉ right := by
          constructor
          · intro leftAbsent
            exact ((initialSimple initial).mp
              ⟨rfl, leftAbsent, Ne.symm closed⟩).2.1
          · intro rightAbsent
            exact ((initialSimple initial).mpr
              ⟨rfl, rightAbsent, Ne.symm closed⟩).2.1
        constructor
        · intro leftMember
          apply Decidable.byContradiction
          intro rightAbsent
          exact (absent.mpr rightAbsent) leftMember
        · intro rightMember
          apply Decidable.byContradiction
          intro leftAbsent
          exact (absent.mp leftAbsent) rightMember
      · by_cases isFinal : tested = final
        · subst tested
          have absent :
              final ∉ left ↔ final ∉ right := by
            constructor
            · intro leftAbsent
              have leftWholeAbsent : final ∉ initial :: left := by
                simp [Ne.symm closed, leftAbsent]
              exact fun rightMember =>
                ((finalSimple final).mp
                  ⟨rfl, leftWholeAbsent⟩).2
                    (List.mem_cons_of_mem initial rightMember)
            · intro rightAbsent
              have rightWholeAbsent : final ∉ initial :: right := by
                simp [Ne.symm closed, rightAbsent]
              exact fun leftMember =>
                ((finalSimple final).mpr
                  ⟨rfl, rightWholeAbsent⟩).2
                    (List.mem_cons_of_mem initial leftMember)
          constructor
          · intro leftMember
            apply Decidable.byContradiction
            intro rightAbsent
            exact (absent.mpr rightAbsent) leftMember
          · intro rightMember
            apply Decidable.byContradiction
            intro leftAbsent
            exact (absent.mp leftAbsent) rightMember
        · simpa [isInitial, isFinal, Ne.symm isInitial,
            Ne.symm isFinal] using wholeSupport tested
    · exact residue

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private theorem permConsToEnd (letter : Nat) :
    ∀ letters : List Nat,
      (letter :: letters).Perm (letters ++ [letter])
  | [] => List.Perm.refl _
  | next :: rest =>
      (List.Perm.swap next letter rest).trans <|
        List.Perm.cons next (permConsToEnd letter rest)

private theorem permTwoToEnd (letter : Nat) (rest : List Nat) :
    (letter :: letter :: rest).Perm (rest ++ [letter, letter]) := by
  apply (List.Perm.cons letter (permConsToEnd letter rest)).trans
  simpa [List.append_assoc] using
    permConsToEnd letter (rest ++ [letter])

private theorem permThreeToEnd
    (first second third : Nat) (rest : List Nat) :
    (first :: second :: third :: rest).Perm
      (rest ++ [first, second, third]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

private theorem derivesRepeatedFirstFinalSwitch
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (endpointWord initial (initial :: middle ++ [final]) final)
      (endpointWord initial (middle ++ [final, final]) initial) := by
  cases middle with
  | nil =>
      simpa [endpointWord,
        SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        Word.append, Word.singleton, Word.append_assoc] using
          derivesSquareFinalSwitch
            (Word.singleton initial) (Word.singleton final)
  | cons next rest =>
      have sourcePerm :
          (initial :: next :: rest ++ [final]).Perm
            (initial :: final :: next :: rest) :=
        List.Perm.cons initial <|
          (permConsToEnd final (next :: rest)).symm
      have targetPerm :
          (final :: final :: next :: rest).Perm
            (next :: rest ++ [final, final]) :=
        permTwoToEnd final (next :: rest)
      have arrange :=
        derivesMiddlePermutation initial final sourcePerm
      have switch :=
        derivesAttachmentFinal
          (Word.singleton initial) (Word.singleton final)
          (wordOfCons next rest)
      have switched :
          Derives basis
            (endpointWord initial
              (initial :: final :: next :: rest) final)
            (endpointWord initial
              (final :: final :: next :: rest) initial) := by
        simpa [endpointWord,
          SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          wordOfCons, Word.append, Word.singleton,
          Word.append_assoc] using switch
      exact arrange.trans <|
        switched.trans
          (derivesMiddlePermutation initial initial targetPerm)

private theorem repeatedInitialCount
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    2 ≤ (endpointWord initial middle final).toList.count initial := by
  rw [countEndpointWord]
  rcases repeated with member | same
  · have positive : 0 < middle.count initial :=
      List.count_pos_iff.mpr member
    simp
    omega
  · subst final
    simp

private theorem repeatedFinalCount
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : final ∈ initial :: middle) :
    2 ≤ (endpointWord initial middle final).toList.count final := by
  by_cases same : initial = final
  · subst final
    rw [countEndpointWord]
    simp
  · have middleMember : final ∈ middle := by
      simpa [same, Ne.symm same] using repeated
    have positive : 0 < middle.count final :=
      List.count_pos_iff.mpr middleMember
    rw [countEndpointWord]
    simp [same, Ne.symm same]
    omega

private theorem derivesRepeatedFinalToInitial
    (initial : Nat) (middle : List Nat) (final : Nat)
    (initialMultiple :
      2 ≤ (endpointWord initial middle final).toList.count initial)
    (finalMultiple :
      2 ≤ (endpointWord initial middle final).toList.count final) :
    ∃ switchedMiddle,
      Derives basis
        (endpointWord initial middle final)
        (endpointWord initial switchedMiddle initial) ∧
      (endpointWord initial middle final).toList.Perm
        (endpointWord initial switchedMiddle initial).toList := by
  by_cases same : initial = final
  · subst final
    exact ⟨middle, Derives.refl _, List.Perm.refl _⟩
  have middleInitialPositive : 0 < middle.count initial := by
    rw [countEndpointWord] at initialMultiple
    simp [same, Ne.symm same] at initialMultiple
    omega
  have initialMem : initial ∈ middle :=
    List.count_pos_iff.mp middleInitialPositive
  have finalCountAfterInitial :
      (middle.erase initial).count final = middle.count final := by
    rw [List.count_erase_of_ne (Ne.symm same)]
  have middleFinalPositive : 0 < middle.count final := by
    rw [countEndpointWord] at finalMultiple
    simp [same, Ne.symm same] at finalMultiple
    omega
  have finalMemAfter : final ∈ middle.erase initial := by
    apply List.count_pos_iff.mp
    rw [finalCountAfterInitial]
    exact middleFinalPositive
  let rest := (middle.erase initial).erase final
  have arrangeFront :
      middle.Perm (initial :: final :: rest) :=
    (List.perm_cons_erase initialMem).trans <|
      List.Perm.cons initial <| by
        simpa [rest] using List.perm_cons_erase finalMemAfter
  have arrange :
      middle.Perm (initial :: rest ++ [final]) :=
    arrangeFront.trans <|
      List.Perm.cons initial (permConsToEnd final rest)
  have arranged :=
    derivesMiddlePermutation initial final arrange
  let switchedMiddle := rest ++ [final, final]
  have switch :
      Derives basis
        (endpointWord initial (initial :: rest ++ [final]) final)
        (endpointWord initial switchedMiddle initial) := by
    simpa [switchedMiddle] using
      derivesRepeatedFirstFinalSwitch initial rest final
  have fullPerm :
      (endpointWord initial middle final).toList.Perm
        (endpointWord initial switchedMiddle initial).toList := by
    have appendFinal := arrange.append_right [final]
    have outerPerm := List.Perm.cons initial appendFinal
    have moveInitial :=
      List.Perm.cons initial <|
        permConsToEnd initial (rest ++ [final, final])
    exact outerPerm.trans <| by
      simpa only [toListEndpointWord, switchedMiddle,
        List.cons_append, List.nil_append, List.append_assoc] using
          moveInitial
  exact ⟨switchedMiddle, arranged.trans switch, fullPerm⟩

private theorem derivesRepeatedFinalToOther
    (initial : Nat) (middle : List Nat)
    (oldFinal newFinal : Nat)
    (finalsNe : oldFinal ≠ newFinal)
    (initialOldNe : initial ≠ oldFinal)
    (initialNewNe : initial ≠ newFinal)
    (oldMultiple :
      2 ≤
        (endpointWord initial middle oldFinal).toList.count oldFinal)
    (newMultiple :
      2 ≤
        (endpointWord initial middle oldFinal).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives basis
        (endpointWord initial middle oldFinal)
        (endpointWord initial switchedMiddle newFinal) ∧
      (endpointWord initial middle oldFinal).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
  have oldPositive : 0 < middle.count oldFinal := by
    rw [countEndpointWord] at oldMultiple
    simp [initialOldNe, Ne.symm initialOldNe] at oldMultiple
    omega
  have newAtLeastTwo : 2 ≤ middle.count newFinal := by
    rw [countEndpointWord] at newMultiple
    simp [finalsNe, initialNewNe, Ne.symm finalsNe,
      Ne.symm initialNewNe] at newMultiple
    omega
  have newMem : newFinal ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have newMemAfter : newFinal ∈ middle.erase newFinal := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  have oldMemAfter :
      oldFinal ∈ (middle.erase newFinal).erase newFinal := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_of_ne finalsNe,
      List.count_erase_of_ne finalsNe]
    exact oldPositive
  let rest :=
    ((middle.erase newFinal).erase newFinal).erase oldFinal
  have arrangeFront :
      middle.Perm (newFinal :: newFinal :: oldFinal :: rest) :=
    (List.perm_cons_erase newMem).trans <|
      List.Perm.cons newFinal <|
        (List.perm_cons_erase newMemAfter).trans <|
          List.Perm.cons newFinal <| by
            simpa [rest] using List.perm_cons_erase oldMemAfter
  have arrange :
      middle.Perm (rest ++ [newFinal, newFinal, oldFinal]) :=
    arrangeFront.trans <|
      permThreeToEnd newFinal newFinal oldFinal rest
  have arranged :=
    derivesMiddlePermutation initial oldFinal arrange
  let switchedMiddle := rest ++ [newFinal, oldFinal, oldFinal]
  have switch :
      Derives basis
        (endpointWord initial
          (rest ++ [newFinal, newFinal, oldFinal]) oldFinal)
        (endpointWord initial switchedMiddle newFinal) := by
    have contextual :=
      Derives.prepend (wordOfCons initial rest)
        (derivesSquareFinalSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal))
    simpa [endpointWord,
      SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
      switchedMiddle, wordOfCons, Word.append, Word.singleton,
      Word.append_assoc, List.append_assoc] using contextual
  have fullPerm :
      (endpointWord initial middle oldFinal).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
    have appendFinal := arrange.append_right [oldFinal]
    have outerPerm := List.Perm.cons initial appendFinal
    have suffixPerm :
        [newFinal, newFinal, oldFinal, oldFinal].Perm
          [newFinal, oldFinal, oldFinal, newFinal] :=
      List.Perm.cons newFinal <|
        permConsToEnd newFinal [oldFinal, oldFinal]
    have restPerm := List.Perm.append_left rest suffixPerm
    exact outerPerm.trans <| by
      simpa only [toListEndpointWord, switchedMiddle,
        List.cons_append, List.nil_append, List.append_assoc] using
          List.Perm.cons initial restPerm
  exact ⟨switchedMiddle, arranged.trans switch, fullPerm⟩

private theorem derivesAddInitialTriple
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    ∃ expandedMiddle,
      Derives basis
        (endpointWord initial middle final)
        (endpointWord initial expandedMiddle final) ∧
      2 ≤ expandedMiddle.count initial ∧
      ∀ tested, tested ≠ initial ->
        expandedMiddle.count tested = middle.count tested := by
  rcases repeated with middleMem | finalEq
  · have arrange :
        middle.Perm (initial :: middle.erase initial) :=
      List.perm_cons_erase middleMem
    have arranged :=
      derivesMiddlePermutation initial final arrange
    let expandedMiddle :=
      initial :: initial :: initial :: initial :: middle.erase initial
    have expansion :=
      Derives.appendRight
        (derivesPowerExpansion (Word.singleton initial))
        (wordOfPrefixFinal (middle.erase initial) final)
    have expanded :
        Derives basis
          (endpointWord initial
            (initial :: middle.erase initial) final)
          (endpointWord initial expandedMiddle final) := by
      simpa only [expandedMiddle, endpointWordEq,
        wordOfPrefixFinalCons, Word.append_assoc] using expansion
    refine ⟨expandedMiddle, arranged.trans expanded, ?_, ?_⟩
    · simp [expandedMiddle]
    · intro tested different
      simp [expandedMiddle, different, Ne.symm different]
  · subst final
    cases middle with
    | nil =>
        refine ⟨[initial, initial, initial], ?_, by simp, ?_⟩
        · simpa [endpointWord,
            SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            Word.append, Word.singleton, Word.append_assoc] using
              derivesPowerExpansion (Word.singleton initial)
        · intro tested different
          simp [different, Ne.symm different]
    | cons next rest =>
        let middleWord := Word.mk next rest
        let expandedMiddle :=
          initial :: initial :: initial :: next :: rest
        have expansion :=
          derivesRepeatedEndpointExpansion
            (Word.singleton initial) middleWord
        have expanded :
            Derives basis
              (endpointWord initial (next :: rest) initial)
              (endpointWord initial expandedMiddle initial) := by
          simpa [endpointWord,
            SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            middleWord, expandedMiddle, Word.append, Word.singleton,
            Word.append_assoc] using expansion
        refine ⟨expandedMiddle, expanded, ?_, ?_⟩
        · simp [expandedMiddle]
        · intro tested different
          simp [expandedMiddle, different, Ne.symm different]

private theorem derivesExpandInterior
    (initial : Nat) (middle : List Nat) (final selected : Nat)
    (member : selected ∈ middle) :
    ∃ expandedMiddle,
      Derives basis
        (endpointWord initial middle final)
        (endpointWord initial expandedMiddle final) ∧
      4 ≤ expandedMiddle.count selected ∧
      ∀ tested, tested ≠ selected ->
        expandedMiddle.count tested = middle.count tested := by
  have arrange :
      middle.Perm (selected :: middle.erase selected) :=
    List.perm_cons_erase member
  have arranged :=
    derivesMiddlePermutation initial final arrange
  let expandedMiddle :=
    selected :: selected :: selected :: selected ::
      middle.erase selected
  have expansion :=
    derivesContextualPeriodExpansion
      (Word.singleton initial)
      (Word.singleton selected)
      (wordOfPrefixFinal (middle.erase selected) final)
  have expanded :
      Derives basis
        (endpointWord initial
          (selected :: middle.erase selected) final)
        (endpointWord initial expandedMiddle final) := by
    simpa only [expandedMiddle, endpointWordEq,
      wordOfPrefixFinalCons, Word.append_assoc] using expansion
  refine ⟨expandedMiddle, arranged.trans expanded, ?_, ?_⟩
  · simp [expandedMiddle]
  · intro tested different
    simp [expandedMiddle, different, Ne.symm different]

private theorem derivesInitialSwitch
    (old new : Nat) (middle : List Nat) (final : Nat)
    (different : old ≠ new)
    (oldRepeated : old ∈ middle ∨ final = old)
    (newMultiple :
      2 ≤ (endpointWord old middle final).toList.count new) :
    ∃ switchedMiddle,
      Derives basis
        (endpointWord old middle final)
        (endpointWord new switchedMiddle final) := by
  obtain ⟨expandedMiddle, expand, oldCopies, otherCounts⟩ :=
    derivesAddInitialTriple old middle final oldRepeated
  have expandedNewCount :
      expandedMiddle.count new = middle.count new :=
    otherCounts new (Ne.symm different)
  by_cases finalNew : final = new
  · subst final
    have newPositive : 0 < expandedMiddle.count new := by
      rw [countEndpointWord] at newMultiple
      simp [different, Ne.symm different] at newMultiple
      rw [expandedNewCount]
      omega
    have oldMem : old ∈ expandedMiddle :=
      List.count_pos_iff.mp (by omega)
    have newMemAfterOld : new ∈ expandedMiddle.erase old := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm different)]
      exact newPositive
    have oldMemAfterOldNew :
        old ∈ (expandedMiddle.erase old).erase new := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne different,
        List.count_erase_self]
      omega
    let rest :=
      ((expandedMiddle.erase old).erase new).erase old
    have arrange :
        expandedMiddle.Perm (old :: new :: old :: rest) :=
      (List.perm_cons_erase oldMem).trans <|
        List.Perm.cons old <|
          (List.perm_cons_erase newMemAfterOld).trans <|
            List.Perm.cons new <| by
              simpa [rest] using
                List.perm_cons_erase oldMemAfterOldNew
    have arranged := derivesMiddlePermutation old new arrange
    let switchedMiddle := old :: old :: old :: rest
    have switchRaw :=
      derivesAttachmentInitial
        (Word.singleton old) (Word.singleton new)
        (wordOfCons old rest)
    have switch :
        Derives basis
          (endpointWord old (old :: new :: old :: rest) new)
          (endpointWord new switchedMiddle new) := by
      simpa [endpointWord,
        SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        switchedMiddle, wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using switchRaw
    exact ⟨switchedMiddle, expand.trans <| arranged.trans switch⟩
  · have newAtLeastTwo : 2 ≤ expandedMiddle.count new := by
      rw [countEndpointWord] at newMultiple
      simp [different, finalNew, Ne.symm different,
        Ne.symm finalNew] at newMultiple
      rw [expandedNewCount]
      exact newMultiple
    have oldMem : old ∈ expandedMiddle :=
      List.count_pos_iff.mp (by omega)
    have newMemAfterOld : new ∈ expandedMiddle.erase old := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm different)]
      omega
    have oldMemAfterOldNew :
        old ∈ (expandedMiddle.erase old).erase new := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne different,
        List.count_erase_self]
      omega
    have newMemAfterOldNewOld :
        new ∈ ((expandedMiddle.erase old).erase new).erase old := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm different),
        List.count_erase_self,
        List.count_erase_of_ne (Ne.symm different)]
      omega
    let rest :=
      (((expandedMiddle.erase old).erase new).erase old).erase new
    have arrange :
        expandedMiddle.Perm (old :: new :: old :: new :: rest) :=
      (List.perm_cons_erase oldMem).trans <|
        List.Perm.cons old <|
          (List.perm_cons_erase newMemAfterOld).trans <|
            List.Perm.cons new <|
              (List.perm_cons_erase oldMemAfterOldNew).trans <|
                List.Perm.cons old <| by
                  simpa [rest] using
                    List.perm_cons_erase newMemAfterOldNewOld
    have arranged := derivesMiddlePermutation old final arrange
    let switchedMiddle := old :: old :: old :: new :: rest
    have switchRaw :=
      Derives.appendRight
        (derivesAttachmentInitial
          (Word.singleton old) (Word.singleton new)
          (Word.singleton old))
        (wordOfPrefixFinal rest final)
    have switch :
        Derives basis
          (endpointWord old (old :: new :: old :: new :: rest) final)
          (endpointWord new switchedMiddle final) := by
      simpa only [switchedMiddle, endpointWordEq,
        wordOfPrefixFinalCons, Word.append_assoc] using switchRaw
    exact ⟨switchedMiddle, expand.trans <| arranged.trans switch⟩

private def splitMiddleFinal (current : Nat) :
    List Nat -> List Nat × Nat
  | [] => ([], current)
  | next :: rest =>
      let split := splitMiddleFinal next rest
      (current :: split.1, split.2)

private theorem splitMiddleFinalReconstruct
    (current : Nat) (rest : List Nat) :
    (splitMiddleFinal current rest).1 ++
        [(splitMiddleFinal current rest).2] =
      current :: rest := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (induction next)

private theorem endpointWordSplitMiddleFinal
    (initial current : Nat) (rest : List Nat) :
    endpointWord initial (splitMiddleFinal current rest).1
        (splitMiddleFinal current rest).2 =
      Word.mk initial (current :: rest) := by
  apply Word.toList_injective
  change
    initial ::
        ((splitMiddleFinal current rest).1 ++
          [(splitMiddleFinal current rest).2]) =
      initial :: current :: rest
  exact congrArg (List.cons initial)
    (splitMiddleFinalReconstruct current rest)

private theorem derivesSameInitial
    (initial : Nat)
    (leftMiddle : List Nat) (leftFinal : Nat)
    (rightMiddle : List Nat) (rightFinal : Nat)
    (cyclicValid :
      (Identity.mk
        (endpointWord initial leftMiddle leftFinal)
        (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
          cyclicThree.semigroup)
    (simpleValid :
      (Identity.mk
        (endpointWord initial leftMiddle leftFinal)
        (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    Derives basis
      (endpointWord initial leftMiddle leftFinal)
      (endpointWord initial rightMiddle rightFinal) := by
  have finalSimple :=
    simpleFinalIffOfValid
      initial leftMiddle leftFinal
      initial rightMiddle rightFinal simpleValid
  by_cases leftSimple :
      leftFinal ∉ initial :: leftMiddle
  · have rightSimple :=
      (finalSimple leftFinal).mp ⟨rfl, leftSimple⟩
    have finals : rightFinal = leftFinal := rightSimple.1
    subst rightFinal
    exact derivesAlignedOfFactorValid
      initial leftFinal leftMiddle rightMiddle cyclicValid simpleValid
  · have leftRepeated :
        leftFinal ∈ initial :: leftMiddle :=
      Decidable.not_not.mp leftSimple
    have rightRepeated :
        rightFinal ∈ initial :: rightMiddle := by
      apply Decidable.byContradiction
      intro rightSimple
      have leftWouldBeSimple :=
        (finalSimple rightFinal).mpr ⟨rfl, rightSimple⟩
      exact leftWouldBeSimple.2 <| by
        simpa [leftWouldBeSimple.1] using leftRepeated
    have initialSimple :=
      simpleInitialIffOfValid
        initial leftMiddle leftFinal
        initial rightMiddle rightFinal simpleValid
    by_cases initialRepeated :
        initial ∈ leftMiddle ∨ leftFinal = initial
    · have rightInitialRepeated :
          initial ∈ rightMiddle ∨ rightFinal = initial := by
        apply Decidable.byContradiction
        intro absent
        have rightMiddleAbsent :
            initial ∉ rightMiddle :=
          fun member => absent (Or.inl member)
        have rightFinalNe : rightFinal ≠ initial :=
          fun same => absent (Or.inr same)
        have leftInitialSimple :=
          (initialSimple initial).mpr
            ⟨rfl, rightMiddleAbsent, rightFinalNe⟩
        rcases initialRepeated with member | same
        · exact leftInitialSimple.2.1 member
        · exact leftInitialSimple.2.2 same
      obtain ⟨leftSwitched, leftSwitch, _⟩ :=
        derivesRepeatedFinalToInitial
          initial leftMiddle leftFinal
          (repeatedInitialCount
            initial leftMiddle leftFinal initialRepeated)
          (repeatedFinalCount
            initial leftMiddle leftFinal leftRepeated)
      obtain ⟨rightSwitched, rightSwitch, _⟩ :=
        derivesRepeatedFinalToInitial
          initial rightMiddle rightFinal
          (repeatedInitialCount
            initial rightMiddle rightFinal rightInitialRepeated)
          (repeatedFinalCount
            initial rightMiddle rightFinal rightRepeated)
      have residualCyclic :
          (Identity.mk
            (endpointWord initial leftSwitched initial)
            (endpointWord initial rightSwitched initial)).SatisfiedBy
              cyclicThree.semigroup := by
        intro valuation
        exact
          (leftSwitch.sound
            (by
              simpa [SemigroupBasis.Generated.S3_18.table_eq_catalogue_model]
                using s3_18_models)
            valuation).symm.trans <|
              (cyclicValid valuation).trans
                (rightSwitch.sound
                  (by
                    simpa [
                      SemigroupBasis.Generated.S3_18.table_eq_catalogue_model]
                      using s3_18_models)
                  valuation)
      have residualSimple :
          (Identity.mk
            (endpointWord initial leftSwitched initial)
            (endpointWord initial rightSwitched initial)).SatisfiedBy
              simpleEndpointsFour.semigroup := by
        intro valuation
        exact
          (leftSwitch.sound
            (by
              simpa [SemigroupBasis.Generated.S4_20.table_eq_catalogue_model]
                using s4_20_models)
            valuation).symm.trans <|
              (simpleValid valuation).trans
                (rightSwitch.sound
                  (by
                    simpa [
                      SemigroupBasis.Generated.S4_20.table_eq_catalogue_model]
                      using s4_20_models)
                  valuation)
      exact leftSwitch.trans <|
        (derivesAlignedOfFactorValid
          initial initial leftSwitched rightSwitched
          residualCyclic residualSimple).trans rightSwitch.symm
    · have leftMiddleInitialAbsent : initial ∉ leftMiddle :=
        fun member => initialRepeated (Or.inl member)
      have leftFinalInitialNe : leftFinal ≠ initial :=
        fun same => initialRepeated (Or.inr same)
      have rightInitialSimple :=
        (initialSimple initial).mp
          ⟨rfl, leftMiddleInitialAbsent, leftFinalInitialNe⟩
      by_cases finals : leftFinal = rightFinal
      · subst rightFinal
        exact derivesAlignedOfFactorValid
          initial leftFinal leftMiddle rightMiddle
          cyclicValid simpleValid
      · have newFinalNeInitial : rightFinal ≠ initial :=
          rightInitialSimple.2.2
        have newFinalInLeft : rightFinal ∈ leftMiddle := by
          have support :=
            supportIffOfValid
              initial leftMiddle leftFinal
              initial rightMiddle rightFinal simpleValid rightFinal
          have leftSupport :=
            support.mpr (Or.inr rfl)
          rcases leftSupport with
            headOrMiddle | oldFinal
          · rcases List.mem_cons.mp headOrMiddle with
              atInitial | inMiddle
            · exact False.elim
                (newFinalNeInitial atInitial)
            · exact inMiddle
          · exact False.elim (finals oldFinal)
        obtain
            ⟨expandedMiddle, expansion, newMultiple, otherCounts⟩ :=
          derivesExpandInterior
            initial leftMiddle leftFinal rightFinal newFinalInLeft
        have oldRepeatedExpanded :
            leftFinal ∈ initial :: expandedMiddle := by
          by_cases oldIsInitial : leftFinal = initial
          · simp [oldIsInitial]
          · have oldInMiddle : leftFinal ∈ leftMiddle := by
              simpa [oldIsInitial] using leftRepeated
            have oldCount :
                expandedMiddle.count leftFinal =
                  leftMiddle.count leftFinal :=
              otherCounts leftFinal finals
            have positive : 0 < expandedMiddle.count leftFinal := by
              rw [oldCount]
              exact List.count_pos_iff.mpr oldInMiddle
            exact List.mem_cons_of_mem initial
              (List.count_pos_iff.mp positive)
        obtain ⟨switchedMiddle, switch, _⟩ :=
          derivesRepeatedFinalToOther
            initial expandedMiddle leftFinal rightFinal
            finals leftFinalInitialNe.symm
            newFinalNeInitial.symm
            (repeatedFinalCount
              initial expandedMiddle leftFinal oldRepeatedExpanded)
            (by
              rw [countEndpointWord]
              omega)
        have leftDerivation := expansion.trans switch
        have residualCyclic :
            (Identity.mk
              (endpointWord initial switchedMiddle rightFinal)
              (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
                cyclicThree.semigroup := by
          intro valuation
          exact
            (leftDerivation.sound
              (by
                simpa [
                  SemigroupBasis.Generated.S3_18.table_eq_catalogue_model]
                  using s3_18_models)
              valuation).symm.trans (cyclicValid valuation)
        have residualSimple :
            (Identity.mk
              (endpointWord initial switchedMiddle rightFinal)
              (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
                simpleEndpointsFour.semigroup := by
          intro valuation
          exact
            (leftDerivation.sound
              (by
                simpa [
                  SemigroupBasis.Generated.S4_20.table_eq_catalogue_model]
                  using s4_20_models)
              valuation).symm.trans (simpleValid valuation)
        exact leftDerivation.trans <|
          derivesAlignedOfFactorValid
            initial rightFinal switchedMiddle rightMiddle
            residualCyclic residualSimple

private theorem singletonHeadsEqual
    (leftHead rightHead : Nat)
    (valid :
      (Identity.mk
        (Word.mk leftHead []) (Word.mk rightHead [])).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    leftHead = rightHead := by
  have evaluated := valid (supportSeparator leftHead)
  change
    supportSeparator leftHead leftHead =
      supportSeparator leftHead rightHead at evaluated
  apply Decidable.byContradiction
  intro different
  simp [supportSeparator, different, Ne.symm different] at evaluated

/-- Unrestricted completeness of the exact `C3`/simple-endpoints
intersection. All normalization and endpoint-switch lemmas quantify over
arbitrary `Nat` variables and substitute arbitrary nonempty words. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_18.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_20.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have cyclicValid :
      identity.SatisfiedBy cyclicThree.semigroup := by
    simpa [SemigroupBasis.Generated.S3_18.table_eq_catalogue_model] using
      s3Valid
  have simpleValid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup := by
    simpa [SemigroupBasis.Generated.S4_20.table_eq_catalogue_model] using
      s4Valid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          have heads :=
            singletonHeadsEqual leftHead rightHead simpleValid
          subst rightHead
          exact Derives.refl _
      | cons rightSecond rightRest =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have leftOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk leftHead [])).2 rfl
          have rightOne := evaluated.symm.trans leftOne
          have impossible :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rightHead
                (rightSecond :: rightRest))).1 rightOne
          simp at impossible
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have rightOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rightHead [])).2 rfl
          have leftOne := evaluated.trans rightOne
          have impossible :=
            (simpleEndpointsSingletonSeparator
              (Word.mk leftHead
                (leftSecond :: leftRest))).1 leftOne
          simp at impossible
      | cons rightSecond rightRest =>
          let leftSplit := splitMiddleFinal leftSecond leftRest
          let rightSplit := splitMiddleFinal rightSecond rightRest
          have leftReconstruct :
              endpointWord leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) :=
            endpointWordSplitMiddleFinal leftHead leftSecond leftRest
          have rightReconstruct :
              endpointWord rightHead rightSplit.1 rightSplit.2 =
                Word.mk rightHead (rightSecond :: rightRest) :=
            endpointWordSplitMiddleFinal rightHead rightSecond rightRest
          have endpointCyclic :
              (Identity.mk
                (endpointWord leftHead leftSplit.1 leftSplit.2)
                (endpointWord rightHead rightSplit.1
                  rightSplit.2)).SatisfiedBy cyclicThree.semigroup := by
            rw [leftReconstruct, rightReconstruct]
            exact cyclicValid
          have endpointSimple :
              (Identity.mk
                (endpointWord leftHead leftSplit.1 leftSplit.2)
                (endpointWord rightHead rightSplit.1
                  rightSplit.2)).SatisfiedBy
                    simpleEndpointsFour.semigroup := by
            rw [leftReconstruct, rightReconstruct]
            exact simpleValid
          by_cases heads : leftHead = rightHead
          · subst rightHead
            rw [← leftReconstruct, ← rightReconstruct]
            exact derivesSameInitial
              leftHead leftSplit.1 leftSplit.2
              rightSplit.1 rightSplit.2
              endpointCyclic endpointSimple
          · have initialSimple :=
              simpleInitialIffOfValid
                leftHead leftSplit.1 leftSplit.2
                rightHead rightSplit.1 rightSplit.2
                endpointSimple
            have leftRepeated :
                leftHead ∈ leftSplit.1 ∨ leftSplit.2 = leftHead := by
              apply Decidable.byContradiction
              intro absent
              have leftMiddleAbsent : leftHead ∉ leftSplit.1 :=
                fun member => absent (Or.inl member)
              have leftFinalNe : leftSplit.2 ≠ leftHead :=
                fun same => absent (Or.inr same)
              have rightSimple :=
                (initialSimple leftHead).mp
                  ⟨rfl, leftMiddleAbsent, leftFinalNe⟩
              exact heads rightSimple.1.symm
            have rightRepeated :
                rightHead ∈ rightSplit.1 ∨
                  rightSplit.2 = rightHead := by
              apply Decidable.byContradiction
              intro absent
              have rightMiddleAbsent : rightHead ∉ rightSplit.1 :=
                fun member => absent (Or.inl member)
              have rightFinalNe : rightSplit.2 ≠ rightHead :=
                fun same => absent (Or.inr same)
              have leftSimple :=
                (initialSimple rightHead).mpr
                  ⟨rfl, rightMiddleAbsent, rightFinalNe⟩
              exact heads leftSimple.1
            have support :=
              supportIffOfValid
                leftHead leftSplit.1 leftSplit.2
                rightHead rightSplit.1 rightSplit.2
                endpointSimple
            have rightHeadInLeftMiddle :
                rightHead ∈ leftSplit.1 := by
              have leftSupport :=
                (support rightHead).mpr (Or.inl (by simp))
              rcases leftSupport with
                headOrMiddle | atFinal
              · rcases List.mem_cons.mp headOrMiddle with
                  atInitial | inMiddle
                · exact False.elim (heads (Eq.symm atInitial))
                · exact inMiddle
              · by_cases inMiddle : rightHead ∈ leftSplit.1
                · exact inMiddle
                · apply False.elim
                  have leftFinalSimple :
                      leftSplit.2 = rightHead ∧
                        rightHead ∉ leftHead :: leftSplit.1 :=
                    ⟨atFinal, by
                      intro inWord
                      rcases (List.mem_cons.mp inWord) with
                        atInitial | inMiddle'
                      · exact heads (Eq.symm atInitial)
                      · exact inMiddle inMiddle'⟩
                  have finalSimple :=
                    simpleFinalIffOfValid
                      leftHead leftSplit.1 leftSplit.2
                      rightHead rightSplit.1 rightSplit.2
                      endpointSimple
                  have rightFinalSimple :=
                    (finalSimple rightHead).mp leftFinalSimple
                  exact rightFinalSimple.2 (by simp)
            obtain
                ⟨expandedMiddle, expansion,
                  newMultiple, otherCounts⟩ :=
              derivesExpandInterior
                leftHead leftSplit.1 leftSplit.2 rightHead
                rightHeadInLeftMiddle
            have leftRepeatedExpanded :
                leftHead ∈ expandedMiddle ∨
                  leftSplit.2 = leftHead := by
              rcases leftRepeated with member | atFinal
              · left
                have countEq :
                    expandedMiddle.count leftHead =
                      leftSplit.1.count leftHead :=
                  otherCounts leftHead heads
                apply List.count_pos_iff.mp
                rw [countEq]
                exact List.count_pos_iff.mpr member
              · exact Or.inr atFinal
            obtain ⟨switchedMiddle, switch⟩ :=
              derivesInitialSwitch
                leftHead rightHead expandedMiddle leftSplit.2
                heads leftRepeatedExpanded
                (by
                  rw [countEndpointWord]
                  omega)
            have leftDerivation := expansion.trans switch
            have residualCyclic :
                (Identity.mk
                  (endpointWord rightHead switchedMiddle leftSplit.2)
                  (endpointWord rightHead rightSplit.1
                    rightSplit.2)).SatisfiedBy cyclicThree.semigroup := by
              intro valuation
              exact
                (leftDerivation.sound
                  (by
                    simpa [
                      SemigroupBasis.Generated.S3_18.table_eq_catalogue_model]
                      using s3_18_models)
                  valuation).symm.trans (endpointCyclic valuation)
            have residualSimple :
                (Identity.mk
                  (endpointWord rightHead switchedMiddle leftSplit.2)
                  (endpointWord rightHead rightSplit.1
                    rightSplit.2)).SatisfiedBy
                      simpleEndpointsFour.semigroup := by
              intro valuation
              exact
                (leftDerivation.sound
                  (by
                    simpa [
                      SemigroupBasis.Generated.S4_20.table_eq_catalogue_model]
                      using s4_20_models)
                  valuation).symm.trans (endpointSimple valuation)
            rw [← leftReconstruct, ← rightReconstruct]
            exact leftDerivation.trans <|
              derivesSameInitial
                rightHead switchedMiddle leftSplit.2
                rightSplit.1 rightSplit.2
                residualCyclic residualSimple

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_18.table.semigroup
      SemigroupBasis.Generated.S4_20.table.semigroup basis where
  leftModels := s3_18_models
  rightModels := s4_20_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20

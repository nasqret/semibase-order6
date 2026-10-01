import SemigroupBasis.CoRoots.Order6FactorPairS2S594Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Obstruction
import SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers
import SemigroupBasis.Generated.S3_15

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal

open SemigroupBasis
open SemigroupBasis.Examples

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The corrected eleven-law basis. The first ten laws remain the recorded
candidate, while the final law is the square-free interior transposition
forced by both factors. -/
def correctedBasis : List (Identity Nat) :=
  basis ++ [squareFreeInteriorSwap]

/-- Soundness of all eleven laws in the left-zero factor. -/
theorem correctedModelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup correctedBasis := by
  intro identity member
  rw [correctedBasis] at member
  rcases List.mem_append.mp member with recorded | added
  · exact modelsS2_4 identity recorded
  · simp only [List.mem_singleton] at added
    subst identity
    exact squareFreeInteriorSwap_valid_s2_4

/-- Soundness of all eleven laws in the stored `S5_209` factor. -/
theorem correctedModelsS5_209 :
    Models SemigroupBasis.Generated.S5_209.table.semigroup correctedBasis := by
  intro identity member
  rw [correctedBasis] at member
  rcases List.mem_append.mp member with recorded | added
  · exact modelsS5_209 identity recorded
  · simp only [List.mem_singleton] at added
    subst identity
    exact squareFreeInteriorSwap_valid_s5_209

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteCorrectedBasis : List (Identity (Fin 4)) :=
  correctedBasis.map fun identity => identity.map toFinFour

private theorem correctedBasisRoundTripChecked :
    correctedBasis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem correctedModelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteCorrectedBasis.all table.checkIdentity = true) :
    Models table.semigroup correctedBasis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteCorrectedBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinFour).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp correctedBasisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

/-- The same eleven laws are valid in the `S3_15` widening. -/
theorem correctedModelsS3_15 :
    Models SemigroupBasis.Generated.S3_15.table.semigroup correctedBasis :=
  correctedModelsOfFiniteChecks
    SemigroupBasis.Generated.S3_15.table (by decide)

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    ∀ identity : Identity X,
      identity.SatisfiedBy G ↔ identity.SatisfiedBy H := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

private theorem sameTheoryS5_209S5_211 :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy
          SemigroupBasis.Generated.S5_209.table.semigroup ↔
        identity.SatisfiedBy
          SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S5_209.representative_basis
    SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers.S5_211.representative_basis

private theorem sameTheoryS5_209S5_500 :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy
          SemigroupBasis.Generated.S5_209.table.semigroup ↔
        identity.SatisfiedBy
          SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S5_209.representative_basis
    SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers.S5_500.representative_basis

private def leftZeroIntoLeftNormalBand (value : Fin 2) : Fin 3 :=
  if value = 0 then 1 else 2

/-- The established two-element left-zero subsemigroup of `S3_15`, repeated
locally to keep this target closure independent of the much larger
`S5_107` family module. -/
private def leftZeroEmbedding :
    Embedding SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := leftZeroIntoLeftNormalBand
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

private theorem derivesFourToThree (block : Word Nat) :
    Derives correctedBasis
      (((block ++ block) ++ block) ++ block)
      ((block ++ block) ++ block) := by
  have base :
      Derives correctedBasis (word 0 [0, 0, 0]) (word 0 [0, 0]) :=
    Derives.symm <|
      Derives.fromBasis
        (e := Identity.mk (word 0 [0, 0]) (word 0 [0, 0, 0]))
        (by decide)
  have substituted :=
    Derives.subst base
      (instantiateFourWords block block block block)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesOpenInteriorSwap
    (left first second right : Word Nat) :
    Derives correctedBasis
      (((left ++ first) ++ second) ++ right)
      (((left ++ second) ++ first) ++ right) := by
  have base :
      Derives correctedBasis
        (word 0 [1, 2, 3]) (word 0 [2, 1, 3]) :=
    Derives.fromBasis
      (e := Identity.mk (word 0 [1, 2, 3]) (word 0 [2, 1, 3]))
      (by decide)
  have substituted :=
    Derives.subst base
      (instantiateFourWords left first second right)
  simpa [word, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private abbrev endpointWord :=
  _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints

private theorem derivesPublicMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives correctedBasis
      (endpointWord initial left final)
      (endpointWord initial right final) :=
  _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.derivesMiddlePermutationOfOpenSwap
    derivesOpenInteriorSwap initial final permutation

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

private def wordOfPrefixFinal : List Nat -> Nat -> Word Nat
  | [], final => Word.singleton final
  | head :: tail, final => Word.mk head (tail ++ [final])

@[simp]
private theorem toList_wordOfPrefixFinal
    (wordPrefix : List Nat) (final : Nat) :
    (wordOfPrefixFinal wordPrefix final).toList = wordPrefix ++ [final] := by
  cases wordPrefix <;> simp [wordOfPrefixFinal, Word.toList, Word.singleton]

@[simp]
private theorem wordOfPrefixFinal_cons
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfPrefixFinal (head :: tail) final =
      Word.singleton head ++ wordOfPrefixFinal tail final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]
  rfl

private theorem endpointWord_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private theorem permConsToEnd (x : Nat) :
    ∀ letters : List Nat, (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (permConsToEnd x ys)

private theorem permTwoToEnd (x : Nat) (rest : List Nat) :
    (x :: x :: rest).Perm (rest ++ [x, x]) := by
  apply (List.Perm.cons x (permConsToEnd x rest)).trans
  simpa [List.append_assoc] using permConsToEnd x (rest ++ [x])

private theorem permSwapAround (first last : Nat) (middle : List Nat) :
    (first :: middle ++ [last]).Perm
      (last :: middle ++ [first]) := by
  have moveFirst := permConsToEnd first (middle ++ [last])
  have moveLast :=
    (permConsToEnd last middle).symm.append_right [first]
  exact moveFirst.trans <| by
    simpa [List.append_assoc] using moveLast

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Balanced consequences of the corrected basis -/

private theorem basisTripleClosedContraction :
    Derives correctedBasis
      (word 0 [0, 0, 1, 0])
      (word 0 [0, 1, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 0, 1, 0])
    (word 0 [0, 1, 0]))
    (by decide)

private theorem basisSquareFinalSwitch :
    Derives correctedBasis
      (word 0 [0, 1, 1])
      (word 0 [1, 1, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 1])
    (word 0 [1, 1, 0]))
    (by decide)

private theorem basisAttachmentFinal :
    Derives correctedBasis
      (word 0 [0, 1, 2, 1])
      (word 0 [1, 1, 2, 0]) :=
  Derives.fromBasis (e := Identity.mk
    (word 0 [0, 1, 2, 1])
    (word 0 [1, 1, 2, 0]))
    (by decide)

private theorem derivesTripleClosedContraction
    (x middle : Word Nat) :
    Derives correctedBasis
      ((((x ++ x) ++ x) ++ middle) ++ x)
      (((x ++ x) ++ middle) ++ x) := by
  have substituted :=
    Derives.subst basisTripleClosedContraction
      (instantiateTwoWords x middle)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareFinalSwitch
    (x y : Word Nat) :
    Derives correctedBasis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentFinal
    (x y z : Word Nat) :
    Derives correctedBasis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisAttachmentFinal
      (instantiateThreeWords x y z)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Endpoint-aware cap-three normalization -/

/-- Retain at most three copies in the whole word, counting the two protected
endpoints before deciding whether to retain an interior occurrence. -/
def endpointCapThreeReduce
    (initial final : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs =>
      let reduced := endpointCapThreeReduce initial final xs
      if _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final x + reduced.count x < 3 then
        x :: reduced
      else
        reduced

theorem endpointCapThreeReduce_total_le_three
    (initial final tested : Nat) (middle : List Nat) :
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
        (endpointCapThreeReduce initial final middle).count tested <= 3 := by
  induction middle with
  | nil =>
      simp only [endpointCapThreeReduce, List.count_nil, Nat.add_zero]
      have endpointBound :=
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies_le_two
          initial final tested
      omega
  | cons x xs ih =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact ih
      · exact ih

theorem endpointCapThreeReduce_total_capped
    (initial final tested : Nat) (middle : List Nat) :
    min
        (_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
          (endpointCapThreeReduce initial final middle).count tested) 3 =
      min
        (_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final tested +
          middle.count tested) 3 := by
  induction middle with
  | nil =>
      simp [endpointCapThreeReduce]
  | cons x xs ih =>
      simp only [endpointCapThreeReduce]
      split <;> rename_i small
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final x xs
          omega
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same)]
          exact ih
      · by_cases same : tested = x
        · subst tested
          rw [List.count_cons_self]
          have bound :=
            endpointCapThreeReduce_total_le_three
              initial final x xs
          omega
        · rw [List.count_cons_of_ne (Ne.symm same)]
          exact ih

theorem endpointCapThreeReduce_whole_count
    (initial : Nat) (middle : List Nat) (final tested : Nat) :
    (endpointWord initial
      (endpointCapThreeReduce initial final middle) final).toList.count tested =
      min
        ((endpointWord initial middle final).toList.count tested) 3 := by
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints]
  have capped :=
    endpointCapThreeReduce_total_capped
      initial final tested middle
  have bound :=
    endpointCapThreeReduce_total_le_three
      initial final tested middle
  omega

theorem endpointCapThreeReduce_normal_counts_eq
    {leftInitial leftFinal rightInitial rightFinal : Nat}
    {leftMiddle rightMiddle : List Nat}
    (capped : forall tested,
      min
          ((endpointWord leftInitial leftMiddle leftFinal).toList.count
            tested) 3 =
        min
          ((endpointWord rightInitial rightMiddle rightFinal).toList.count
            tested) 3) :
    forall tested,
      (endpointWord leftInitial
          (endpointCapThreeReduce
            leftInitial leftFinal leftMiddle)
          leftFinal).toList.count tested =
        (endpointWord rightInitial
          (endpointCapThreeReduce
            rightInitial rightFinal rightMiddle)
          rightFinal).toList.count tested := by
  intro tested
  rw [endpointCapThreeReduce_whole_count,
    endpointCapThreeReduce_whole_count, capped tested]

private theorem derivesDeleteFourInterior
    (initial final selected : Nat) (pre reduced : List Nat)
    (countEq : reduced.count selected = 3) :
    Derives correctedBasis
      (endpointWord initial (pre ++ selected :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder :=
    ((reduced.erase selected).erase selected).erase selected
  have firstCount : (reduced.erase selected).count selected = 2 := by
    rw [List.count_erase_self, countEq]
  have secondCount :
      ((reduced.erase selected).erase selected).count selected = 1 := by
    rw [List.count_erase_self, firstCount]
  have remainderCount : remainder.count selected = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondCount]
  have sourcePerm :
      (pre ++ selected :: reduced).Perm
        (selected :: selected :: selected :: selected ::
          pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = selected
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (selected :: selected :: selected :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = selected
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.appendRight
      (Derives.prepend (Word.singleton initial)
        (derivesFourToThree (Word.singleton selected)))
      (wordOfPrefixFinal (pre ++ remainder) final)
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          (selected :: selected :: selected :: selected ::
            pre ++ remainder) final)
        (endpointWord initial
          (selected :: selected :: selected :: pre ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteInitialExcess
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count initial = 2) :
    Derives correctedBasis
      (endpointWord initial (pre ++ initial :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder := (reduced.erase initial).erase initial
  have firstCount : (reduced.erase initial).count initial = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count initial = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (pre ++ initial :: reduced).Perm
        (initial :: initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = initial
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (initial :: initial :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = initial
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.appendRight
      (derivesFourToThree (Word.singleton initial))
      (wordOfPrefixFinal (pre ++ remainder) final)
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          (initial :: initial :: initial :: pre ++ remainder) final)
        (endpointWord initial
          (initial :: initial :: pre ++ remainder) final) := by
    simpa only [List.cons_append, endpointWord_eq,
      wordOfPrefixFinal_cons, Word.append_assoc] using contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteFinalExcess
    (initial final : Nat) (pre reduced : List Nat)
    (countEq : reduced.count final = 2) :
    Derives correctedBasis
      (endpointWord initial (pre ++ final :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  let remainder := (reduced.erase final).erase final
  have firstCount : (reduced.erase final).count final = 1 := by
    rw [List.count_erase_self, countEq]
  have remainderCount : remainder.count final = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstCount]
  have sourcePerm :
      (pre ++ final :: reduced).Perm
        ((pre ++ remainder) ++ [final, final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        ((pre ++ remainder) ++ [final, final]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = final
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have contraction :=
    Derives.prepend (wordOfCons initial (pre ++ remainder))
      (derivesFourToThree (Word.singleton final))
  have contracted :
      Derives correctedBasis
        (endpointWord initial
          ((pre ++ remainder) ++ [final, final, final]) final)
        (endpointWord initial
          ((pre ++ remainder) ++ [final, final]) final) := by
    have sourceShape :
        wordOfCons initial (pre ++ remainder) ++
            (((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) ++ Word.singleton final) =
          endpointWord initial
            ((pre ++ remainder) ++ [final, final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        wordOfCons, Word.toList, List.append_assoc]
    have targetShape :
        wordOfCons initial (pre ++ remainder) ++
            ((Word.singleton final ++ Word.singleton final) ++
              Word.singleton final) =
          endpointWord initial
            ((pre ++ remainder) ++ [final, final]) final := by
      apply Word.toList_injective
      simp [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        wordOfCons, Word.toList, List.append_assoc]
    rw [← sourceShape, ← targetShape]
    exact contraction
  exact Derives.trans
    (derivesPublicMiddlePermutation initial final sourcePerm) <|
      Derives.trans contracted <|
        derivesPublicMiddlePermutation initial final targetPerm.symm

private theorem derivesDeleteClosedExcess
    (endpoint : Nat) (pre reduced : List Nat)
    (countEq : reduced.count endpoint = 1) :
    Derives correctedBasis
      (endpointWord endpoint (pre ++ endpoint :: reduced) endpoint)
      (endpointWord endpoint (pre ++ reduced) endpoint) := by
  let remainder := reduced.erase endpoint
  have remainderCount : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, countEq]
  have sourcePerm :
      (pre ++ endpoint :: reduced).Perm
        (endpoint :: endpoint :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have targetPerm :
      (pre ++ reduced).Perm
        (endpoint :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases same : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
    · simp [remainder, same, Ne.symm same]
  have arranged :=
    derivesPublicMiddlePermutation endpoint endpoint sourcePerm
  have contraction :
      Derives correctedBasis
        (endpointWord endpoint
          (endpoint :: endpoint :: pre ++ remainder) endpoint)
        (endpointWord endpoint
          (endpoint :: pre ++ remainder) endpoint) := by
    cases restEq : pre ++ remainder with
    | nil =>
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          restEq, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesFourToThree (Word.singleton endpoint)
    | cons next rest =>
        have contracted :=
          derivesTripleClosedContraction
            (Word.singleton endpoint) (wordOfCons next rest)
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          restEq, wordOfCons, Word.append, Word.singleton,
          Word.append_assoc, List.append_assoc] using contracted
  exact arranged.trans <|
    contraction.trans <|
      derivesPublicMiddlePermutation endpoint endpoint targetPerm.symm

private theorem derivesDeleteCapThreeExcess
    (initial final selected : Nat) (pre reduced : List Nat)
    (totalEq :
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
          reduced.count selected = 3) :
    Derives correctedBasis
      (endpointWord initial (pre ++ selected :: reduced) final)
      (endpointWord initial (pre ++ reduced) final) := by
  by_cases atInitial : selected = initial
  · subst selected
    by_cases closed : initial = final
    · subst final
      have countEq : reduced.count initial = 1 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies] at totalEq
        omega
      exact derivesDeleteClosedExcess initial pre reduced countEq
    · have countEq : reduced.count initial = 2 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, closed, Ne.symm closed] at totalEq
        omega
      exact derivesDeleteInitialExcess initial final pre reduced countEq
  · by_cases atFinal : selected = final
    · subst selected
      have countEq : reduced.count final = 2 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, atInitial,
          Ne.symm atInitial] at totalEq
        omega
      exact derivesDeleteFinalExcess initial final pre reduced countEq
    · have countEq : reduced.count selected = 3 := by
        simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, atInitial, atFinal,
          Ne.symm atInitial, Ne.symm atFinal] at totalEq
        omega
      exact derivesDeleteFourInterior
        initial final selected pre reduced countEq

private theorem derivesNormalizeCapThreeAux :
    forall (initial : Nat) (pre middle : List Nat) (final : Nat),
      Derives correctedBasis
        (endpointWord initial (pre ++ middle) final)
        (endpointWord initial
          (pre ++ endpointCapThreeReduce initial final middle) final)
  | initial, pre, [], final => by
      exact Derives.refl _
  | initial, pre, selected :: tail, final => by
      have tailNormal :=
        derivesNormalizeCapThreeAux
          initial (pre ++ [selected]) tail final
      let reduced := endpointCapThreeReduce initial final tail
      have firstStep :
          Derives correctedBasis
            (endpointWord initial (pre ++ selected :: tail) final)
            (endpointWord initial (pre ++ selected :: reduced) final) := by
        simpa [reduced, List.append_assoc] using tailNormal
      by_cases small :
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
              reduced.count selected < 3
      · have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              selected :: reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep
      · have totalLe :
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
                reduced.count selected <= 3 := by
          simpa [reduced] using
            endpointCapThreeReduce_total_le_three
              initial final selected tail
        have totalEq :
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies initial final selected +
                reduced.count selected = 3 := by
          omega
        have reduceEq :
            endpointCapThreeReduce initial final (selected :: tail) =
              reduced := by
          simp [endpointCapThreeReduce, reduced, small]
        rw [reduceEq]
        exact firstStep.trans <|
          derivesDeleteCapThreeExcess
            initial final selected pre reduced totalEq
termination_by
  _ _ middle _ => middle.length

/-- Normalize all multiplicities to their values capped at three while
preserving both endpoint positions. -/
theorem derivesNormalizeCapThree
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives correctedBasis
      (endpointWord initial middle final)
      (endpointWord initial
        (endpointCapThreeReduce initial final middle) final) := by
  simpa using derivesNormalizeCapThreeAux initial [] middle final

/-! ## Balanced endpoint alignment -/

private theorem repeatedInitial_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    2 <= (endpointWord initial middle final).toList.count initial := by
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints]
  rcases repeated with member | same
  · have positive : 0 < middle.count initial :=
      List.count_pos_iff.mpr member
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies]
    omega
  · subst final
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies]

private theorem repeatedFinal_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : final ∈ initial :: middle) :
    2 <= (endpointWord initial middle final).toList.count final := by
  simp only [endpointWord,
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
    List.count_cons, List.count_append, List.count_singleton]
  have positive : 0 < (initial :: middle).count final :=
    List.count_pos_iff.mpr repeated
  simp only [List.count_cons] at positive
  by_cases endpoints : initial = final
  · subst final
    simp
  · simp [endpoints, Ne.symm endpoints] at positive ⊢
    omega

private theorem fullPerm_of_middle_arrangement
    (sourceInitial sourceFinal targetInitial targetFinal : Nat)
    (sourceMiddle targetMiddle arrangedSource arrangedTarget : List Nat)
    (sourceArrangement : sourceMiddle.Perm arrangedSource)
    (targetArrangement : targetMiddle.Perm arrangedTarget)
    (arranged :
      (endpointWord sourceInitial arrangedSource sourceFinal).toList.Perm
        (endpointWord targetInitial arrangedTarget targetFinal).toList) :
    (endpointWord sourceInitial sourceMiddle sourceFinal).toList.Perm
      (endpointWord targetInitial targetMiddle targetFinal).toList := by
  have sourceOuter :
      (endpointWord sourceInitial sourceMiddle sourceFinal).toList.Perm
        (endpointWord sourceInitial arrangedSource sourceFinal).toList := by
    simpa only [endpointWord,
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
        List.Perm.cons sourceInitial
          (sourceArrangement.append_right [sourceFinal])
  have targetOuter :
      (endpointWord targetInitial targetMiddle targetFinal).toList.Perm
        (endpointWord targetInitial arrangedTarget targetFinal).toList := by
    simpa only [endpointWord,
      _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
        List.Perm.cons targetInitial
          (targetArrangement.append_right [targetFinal])
  exact sourceOuter.trans <| arranged.trans targetOuter.symm

private theorem derivesOpenFinalFromClosed
    (initial newFinal : Nat) (middle : List Nat)
    (different : initial ≠ newFinal)
    (newMultiple :
      2 <= (endpointWord initial middle initial).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord initial middle initial)
        (endpointWord initial switchedMiddle newFinal) ∧
      (endpointWord initial middle initial).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
  have newAtLeastTwo : 2 <= middle.count newFinal := by
    rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
    simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, different,
      Ne.symm different] at newMultiple
    exact newMultiple
  have firstMem : newFinal ∈ middle :=
    List.count_pos_iff.mp (by omega)
  have secondMem : newFinal ∈ middle.erase newFinal := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  let rest := (middle.erase newFinal).erase newFinal
  have arrangement : middle.Perm (newFinal :: newFinal :: rest) :=
    (List.perm_cons_erase firstMem).trans <|
      List.Perm.cons newFinal <| by
        simpa [rest] using List.perm_cons_erase secondMem
  cases restEq : rest with
  | nil =>
      let switchedMiddle := [initial, newFinal]
      have arranged :=
        derivesPublicMiddlePermutation initial initial arrangement
      have switched :
          Derives correctedBasis
            (endpointWord initial [newFinal, newFinal] initial)
            (endpointWord initial switchedMiddle newFinal) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.symm
              (derivesSquareFinalSwitch
                (Word.singleton initial)
                (Word.singleton newFinal))
      have sourceArrangement :
          middle.Perm [newFinal, newFinal] := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm [initial, newFinal] :=
        List.Perm.refl _
      have endpointPermutation :
          (endpointWord initial
            [newFinal, newFinal] initial).toList.Perm
            (endpointWord initial
              [initial, newFinal] newFinal).toList := by
        have literalPermutation :=
          List.Perm.cons initial <|
            (permConsToEnd initial [newFinal, newFinal]).symm
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            literalPermutation
      have arrangedNil :
          Derives correctedBasis
            (endpointWord initial middle initial)
            (endpointWord initial [newFinal, newFinal] initial) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle,
        arrangedNil.trans switched,
        fullPerm_of_middle_arrangement
          initial initial initial newFinal middle switchedMiddle
          [newFinal, newFinal] [initial, newFinal]
          sourceArrangement targetArrangement endpointPermutation⟩
  | cons next tail =>
      let switchedMiddle := initial :: newFinal :: next :: tail
      have arranged :=
        derivesPublicMiddlePermutation initial initial arrangement
      have switched :
          Derives correctedBasis
            (endpointWord initial
              (newFinal :: newFinal :: next :: tail) initial)
            (endpointWord initial switchedMiddle newFinal) := by
        simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
          switchedMiddle, wordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.symm
              (derivesAttachmentFinal
                (Word.singleton initial)
                (Word.singleton newFinal)
                (wordOfCons next tail))
      have sourceArrangement :
          middle.Perm (newFinal :: newFinal :: next :: tail) := by
        simpa [restEq] using arrangement
      have targetArrangement :
          switchedMiddle.Perm
            (initial :: newFinal :: next :: tail) :=
        List.Perm.refl _
      have endpointPermutation :
          (endpointWord initial
            (newFinal :: newFinal :: next :: tail) initial).toList.Perm
            (endpointWord initial
              (initial :: newFinal :: next :: tail) newFinal).toList := by
        have literalPermutation :=
          List.Perm.cons initial <|
            permSwapAround newFinal initial
              (newFinal :: next :: tail)
        simpa only [endpointWord,
          _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
            literalPermutation
      have arrangedCons :
          Derives correctedBasis
            (endpointWord initial middle initial)
            (endpointWord initial
              (newFinal :: newFinal :: next :: tail) initial) := by
        simpa [restEq] using arranged
      exact ⟨switchedMiddle, arrangedCons.trans switched,
        fullPerm_of_middle_arrangement
          initial initial initial newFinal middle switchedMiddle
          (newFinal :: newFinal :: next :: tail)
          (initial :: newFinal :: next :: tail)
          sourceArrangement targetArrangement endpointPermutation⟩

private theorem derivesFinalSwitchPreservingInitial
    (initial oldFinal newFinal : Nat) (middle : List Nat)
    (finalsNe : oldFinal ≠ newFinal)
    (initialOldNe : initial ≠ oldFinal)
    (oldRepeated : oldFinal ∈ initial :: middle)
    (newMultiple :
      2 <= (endpointWord initial middle oldFinal).toList.count newFinal) :
    ∃ switchedMiddle,
      Derives correctedBasis
        (endpointWord initial middle oldFinal)
        (endpointWord initial switchedMiddle newFinal) ∧
      (endpointWord initial middle oldFinal).toList.Perm
        (endpointWord initial switchedMiddle newFinal).toList := by
  have oldMem : oldFinal ∈ middle := by
    rcases List.mem_cons.mp oldRepeated with atInitial | member
    · exact False.elim (initialOldNe atInitial.symm)
    · exact member
  by_cases initialNew : initial = newFinal
  · subst newFinal
    have newPositive : 0 < middle.count initial := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, initialOldNe,
        Ne.symm initialOldNe] at newMultiple
      omega
    have newMem : initial ∈ middle :=
      List.count_pos_iff.mp newPositive
    have oldMemAfterNew : oldFinal ∈ middle.erase initial := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm initialOldNe)]
      exact List.count_pos_iff.mpr oldMem
    let rest := (middle.erase initial).erase oldFinal
    have arrangement :
        middle.Perm (initial :: rest ++ [oldFinal]) := by
      have front : middle.Perm (initial :: oldFinal :: rest) :=
        (List.perm_cons_erase newMem).trans <|
          List.Perm.cons initial <| by
            simpa [rest] using List.perm_cons_erase oldMemAfterNew
      exact front.trans <|
        List.Perm.cons initial (permConsToEnd oldFinal rest)
    cases restEq : rest with
    | nil =>
        let switchedMiddle := [oldFinal, oldFinal]
        have arranged :=
          derivesPublicMiddlePermutation initial oldFinal arrangement
        have switched :
            Derives correctedBasis
              (endpointWord initial [initial, oldFinal] oldFinal)
              (endpointWord initial switchedMiddle initial) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSquareFinalSwitch
                (Word.singleton initial) (Word.singleton oldFinal)
        have sourceArrangement :
            middle.Perm [initial, oldFinal] := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm [oldFinal, oldFinal] :=
          List.Perm.refl _
        have endpointPermutation :
            (endpointWord initial
              [initial, oldFinal] oldFinal).toList.Perm
              (endpointWord initial
                [oldFinal, oldFinal] initial).toList := by
          have literalPermutation :=
            List.Perm.cons initial <|
              permConsToEnd initial [oldFinal, oldFinal]
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints] using
              literalPermutation
        have arrangedNil :
            Derives correctedBasis
              (endpointWord initial middle oldFinal)
              (endpointWord initial [initial, oldFinal] oldFinal) := by
          simpa [restEq] using arranged
        exact ⟨switchedMiddle,
          arrangedNil.trans switched,
          fullPerm_of_middle_arrangement
            initial oldFinal initial initial middle switchedMiddle
            [initial, oldFinal] [oldFinal, oldFinal]
            sourceArrangement targetArrangement endpointPermutation⟩
    | cons next tail =>
        let switchedMiddle := oldFinal :: oldFinal :: next :: tail
        have arranged :=
          derivesPublicMiddlePermutation initial oldFinal arrangement
        have attachmentPermutation :
            (initial :: next :: tail ++ [oldFinal]).Perm
              (initial :: oldFinal :: next :: tail) :=
          List.Perm.cons initial <|
            (permConsToEnd oldFinal (next :: tail)).symm
        have attachmentArranged :=
          derivesPublicMiddlePermutation
            initial oldFinal attachmentPermutation
        have attachmentSwitch :
            Derives correctedBasis
              (endpointWord initial
                (initial :: oldFinal :: next :: tail) oldFinal)
              (endpointWord initial switchedMiddle initial) := by
          simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
            switchedMiddle, wordOfCons, Word.append,
            Word.singleton, Word.append_assoc,
            List.append_assoc] using
              derivesAttachmentFinal
                (Word.singleton initial) (Word.singleton oldFinal)
                (wordOfCons next tail)
        have switched :
            Derives correctedBasis
              (endpointWord initial
                (initial :: next :: tail ++ [oldFinal]) oldFinal)
              (endpointWord initial switchedMiddle initial) :=
          attachmentArranged.trans attachmentSwitch
        have sourceArrangement :
            middle.Perm
              (initial :: next :: tail ++ [oldFinal]) := by
          simpa [restEq] using arrangement
        have targetArrangement :
            switchedMiddle.Perm
              (oldFinal :: oldFinal :: next :: tail) :=
          List.Perm.refl _
        have endpointPermutation :
            (endpointWord initial
              (initial :: next :: tail ++ [oldFinal])
              oldFinal).toList.Perm
              (endpointWord initial
                (oldFinal :: oldFinal :: next :: tail)
                initial).toList := by
          have suffixPermutation :
              (initial :: next :: tail ++ [oldFinal, oldFinal]).Perm
                (oldFinal :: oldFinal :: next :: tail ++ [initial]) := by
            have moveInitial :=
              permConsToEnd initial
                ((next :: tail) ++ [oldFinal, oldFinal])
            have moveOldFinals :=
              (permTwoToEnd oldFinal (next :: tail)).symm.append_right
                [initial]
            exact moveInitial.trans <| by
              simpa [List.append_assoc] using moveOldFinals
          have literalPermutation :=
            List.Perm.cons initial suffixPermutation
          simpa only [endpointWord,
            _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
            List.cons_append, List.append_assoc] using literalPermutation
        have arrangedCons :
            Derives correctedBasis
              (endpointWord initial middle oldFinal)
              (endpointWord initial
                (initial :: next :: tail ++ [oldFinal]) oldFinal) := by
          simpa [restEq] using arranged
        exact ⟨switchedMiddle, arrangedCons.trans switched,
          fullPerm_of_middle_arrangement
            initial oldFinal initial initial middle switchedMiddle
            (initial :: next :: tail ++ [oldFinal])
            (oldFinal :: oldFinal :: next :: tail)
            sourceArrangement targetArrangement endpointPermutation⟩
  · have initialNewNe : initial ≠ newFinal := initialNew
    have newAtLeastTwo : 2 <= middle.count newFinal := by
      rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at newMultiple
      simp [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.endpointCopies, finalsNe, initialNewNe,
        Ne.symm finalsNe, Ne.symm initialNewNe] at newMultiple
      exact newMultiple
    have firstNew : newFinal ∈ middle :=
      List.count_pos_iff.mp (by omega)
    have secondNew : newFinal ∈ middle.erase newFinal := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_self]
      omega
    have oldAfterTwoNew :
        oldFinal ∈ (middle.erase newFinal).erase newFinal := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne finalsNe,
        List.count_erase_of_ne finalsNe]
      exact List.count_pos_iff.mpr oldMem
    let rest :=
      ((middle.erase newFinal).erase newFinal).erase oldFinal
    have frontArrangement :
        middle.Perm (newFinal :: newFinal :: oldFinal :: rest) :=
      (List.perm_cons_erase firstNew).trans <|
        List.Perm.cons newFinal <|
          (List.perm_cons_erase secondNew).trans <|
            List.Perm.cons newFinal <| by
              simpa [rest] using List.perm_cons_erase oldAfterTwoNew
    have arrangement :
        middle.Perm (rest ++ [newFinal, newFinal, oldFinal]) := by
      have rotatePrefix :
          (newFinal :: newFinal :: oldFinal :: rest).Perm
            (rest ++ [newFinal, newFinal, oldFinal]) := by
        exact
          (List.perm_append_comm :
            ([newFinal, newFinal, oldFinal] ++ rest).Perm
              (rest ++ [newFinal, newFinal, oldFinal]))
      exact frontArrangement.trans rotatePrefix
    let switchedMiddle :=
      rest ++ [newFinal, oldFinal, oldFinal]
    have arranged :=
      derivesPublicMiddlePermutation initial oldFinal arrangement
    have switchedRaw :=
      Derives.prepend (wordOfCons initial rest)
        (derivesSquareFinalSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal))
    have switched :
        Derives correctedBasis
          (endpointWord initial
            (rest ++ [newFinal, newFinal, oldFinal]) oldFinal)
          (endpointWord initial switchedMiddle newFinal) := by
      simpa [endpointWord, _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.wordOfEndpoints,
        switchedMiddle, wordOfCons, Word.append,
        Word.singleton, Word.append_assoc,
        List.append_assoc] using switchedRaw
    have targetArrangement :
        switchedMiddle.Perm
          (rest ++ [newFinal, oldFinal, oldFinal]) :=
      List.Perm.refl _
    have endpointPermutation :
        (endpointWord initial
          (rest ++ [newFinal, newFinal, oldFinal])
          oldFinal).toList.Perm
          (endpointWord initial
            (rest ++ [newFinal, oldFinal, oldFinal])
            newFinal).toList := by
      have suffixPermutation :
          [newFinal, newFinal, oldFinal, oldFinal].Perm
            [newFinal, oldFinal, oldFinal, newFinal] :=
        List.Perm.cons newFinal <|
          permConsToEnd newFinal [oldFinal, oldFinal]
      have literalPermutation :=
        List.Perm.cons initial <|
          List.Perm.append_left rest suffixPermutation
      simpa only [endpointWord,
        _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
        List.cons_append, List.append_assoc] using literalPermutation
    exact ⟨switchedMiddle, arranged.trans switched,
      fullPerm_of_middle_arrangement
        initial oldFinal initial newFinal middle switchedMiddle
        (rest ++ [newFinal, newFinal, oldFinal])
        (rest ++ [newFinal, oldFinal, oldFinal])
        arrangement targetArrangement endpointPermutation⟩

/-! ## Endpoint semantics and terminal completeness -/

private def s5_209ToFinalMarker (value : Fin 5) : Fin 3 :=
  if value = 2 then 1 else if value = 4 then 2 else 0

private def finalMarkerToS5_209 (value : Fin 3) : Fin 5 :=
  if value = 0 then 0 else if value = 1 then 2 else 4

/-- The final-marker quotient of the stored `S5_209` factor. -/
private def s5_209FinalMarkerQuotient :
    SplitSurjection
      SemigroupBasis.Generated.S5_209.table.semigroup
      finalMarkerThree.semigroup where
  toFun := s5_209ToFinalMarker
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := finalMarkerToS5_209
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

private abbrev markerWordOfPrefixFinal :=
  _root_.SemigroupBasis.Examples.wordOfPrefixFinal

private theorem markerSplit_singleton_append
    (letter : Nat) (current : Word Nat) :
    splitPrefixFinal (Word.singleton letter ++ current) =
      (letter :: (splitPrefixFinal current).1,
        (splitPrefixFinal current).2) := by
  rfl

private theorem markerSplit_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    splitPrefixFinal (markerWordOfPrefixFinal stem final) =
      (stem, final) := by
  induction stem with
  | nil =>
      rfl
  | cons letter rest induction =>
      change
        splitPrefixFinal
            (Word.singleton letter ++
              markerWordOfPrefixFinal rest final) =
          (letter :: rest, final)
      rw [markerSplit_singleton_append, induction]

private theorem endpointWord_eq_markerWord
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      markerWordOfPrefixFinal (initial :: middle) final := by
  apply Word.toList_injective
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.toList_wordOfEndpoints,
    _root_.SemigroupBasis.Examples.toList_wordOfPrefixFinal]

private theorem simpleFinal_iff_of_s5_valid
    (leftInitial : Nat) (leftMiddle : List Nat) (leftFinal : Nat)
    (rightInitial : Nat) (rightMiddle : List Nat) (rightFinal : Nat)
    (valid :
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal)).SatisfiedBy
          SemigroupBasis.Generated.S5_209.table.semigroup) :
    forall tested,
      (leftFinal = tested ∧ tested ∉ leftInitial :: leftMiddle) ↔
        (rightFinal = tested ∧ tested ∉ rightInitial :: rightMiddle) := by
  intro tested
  have markerValid :=
    s5_209FinalMarkerQuotient.pushforwardIdentity
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal))
      valid
  have preserved :=
    finalMarkerValid_splitSimpleFinal_iff
      (Identity.mk
        (endpointWord leftInitial leftMiddle leftFinal)
        (endpointWord rightInitial rightMiddle rightFinal))
      markerValid tested
  have leftSplit :
      splitPrefixFinal
          (endpointWord leftInitial leftMiddle leftFinal) =
        (leftInitial :: leftMiddle, leftFinal) := by
    rw [endpointWord_eq_markerWord,
      markerSplit_wordOfPrefixFinal]
  have rightSplit :
      splitPrefixFinal
          (endpointWord rightInitial rightMiddle rightFinal) =
        (rightInitial :: rightMiddle, rightFinal) := by
    rw [endpointWord_eq_markerWord,
      markerSplit_wordOfPrefixFinal]
  rw [leftSplit, rightSplit] at preserved
  exact preserved

private theorem middlePerm_of_wholeCounts
    (initial final : Nat) (left right : List Nat)
    (counts : forall tested,
      (endpointWord initial left final).toList.count tested =
        (endpointWord initial right final).toList.count tested) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have countEq := counts tested
  rw [_root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints,
    _root_.SemigroupBasis.CoRoots.Order6FactorPairS2S594.count_wordOfEndpoints] at countEq
  omega

private theorem derivesSameEndpointsOfCounts
    (initial final : Nat) (left right : List Nat)
    (counts : forall tested,
      (endpointWord initial left final).toList.count tested =
        (endpointWord initial right final).toList.count tested) :
    Derives correctedBasis
      (endpointWord initial left final)
      (endpointWord initial right final) :=
  derivesPublicMiddlePermutation initial final <|
    middlePerm_of_wholeCounts initial final left right counts

private theorem counts_after_permutation
    {source target reference : Word Nat}
    (permutation : source.toList.Perm target.toList)
    (counts : forall tested,
      source.toList.count tested = reference.toList.count tested) :
    forall tested,
      target.toList.count tested = reference.toList.count tested := by
  intro tested
  have switched :=
    (List.perm_iff_count.mp permutation) tested
  exact switched.symm.trans (counts tested)

private theorem derivesSameInitial
    (initial : Nat)
    (leftMiddle : List Nat) (leftFinal : Nat)
    (rightMiddle : List Nat) (rightFinal : Nat)
    (s5Valid :
      (Identity.mk
        (endpointWord initial leftMiddle leftFinal)
        (endpointWord initial rightMiddle rightFinal)).SatisfiedBy
          SemigroupBasis.Generated.S5_209.table.semigroup)
    (counts : forall tested,
      (endpointWord initial leftMiddle leftFinal).toList.count tested =
        (endpointWord initial rightMiddle rightFinal).toList.count tested) :
    Derives correctedBasis
      (endpointWord initial leftMiddle leftFinal)
      (endpointWord initial rightMiddle rightFinal) := by
  by_cases finals : leftFinal = rightFinal
  · subst rightFinal
    exact derivesSameEndpointsOfCounts
      initial leftFinal leftMiddle rightMiddle counts
  · have finalSimple :=
      simpleFinal_iff_of_s5_valid
        initial leftMiddle leftFinal
        initial rightMiddle rightFinal s5Valid
    have leftRepeated : leftFinal ∈ initial :: leftMiddle := by
      apply Decidable.byContradiction
      intro absent
      have rightSimple :=
        (finalSimple leftFinal).mp ⟨rfl, absent⟩
      exact finals rightSimple.1.symm
    have rightRepeated : rightFinal ∈ initial :: rightMiddle := by
      apply Decidable.byContradiction
      intro absent
      have leftSimple :=
        (finalSimple rightFinal).mpr ⟨rfl, absent⟩
      exact finals leftSimple.1
    have rightMultiple :=
      repeatedFinal_count_two
        initial rightMiddle rightFinal rightRepeated
    have leftNewMultiple :
        2 <=
          (endpointWord initial leftMiddle leftFinal).toList.count
            rightFinal := by
      rw [counts rightFinal]
      exact rightMultiple
    by_cases closed : initial = leftFinal
    · subst leftFinal
      obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesOpenFinalFromClosed
          initial rightFinal leftMiddle
          finals
          leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      exact switch.trans <|
        derivesSameEndpointsOfCounts
          initial rightFinal switchedMiddle rightMiddle switchedCounts
    · obtain ⟨switchedMiddle, switch, permutation⟩ :=
        derivesFinalSwitchPreservingInitial
          initial leftFinal rightFinal leftMiddle
          finals closed leftRepeated leftNewMultiple
      have switchedCounts :=
        counts_after_permutation permutation counts
      exact switch.trans <|
        derivesSameEndpointsOfCounts
          initial rightFinal switchedMiddle rightMiddle switchedCounts

private def splitMiddleFinal (current : Nat) :
    List Nat -> List Nat × Nat
  | [] => ([], current)
  | next :: rest =>
      let split := splitMiddleFinal next rest
      (current :: split.1, split.2)

private theorem splitMiddleFinal_reconstruct
    (current : Nat) (rest : List Nat) :
    (splitMiddleFinal current rest).1 ++
        [(splitMiddleFinal current rest).2] =
      current :: rest := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (induction next)

private theorem endpointWord_splitMiddleFinal
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
    (splitMiddleFinal_reconstruct current rest)

private theorem head_eq_of_s2_4_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  change
    leftZeroTwo.semigroup.eval valuation identity.lhs =
      leftZeroTwo.semigroup.eval valuation identity.rhs at evaluated
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, different, Ne.symm different] at evaluated

/-- Fixed-head cap-three normalization is complete for arbitrary finite
supports. The `S5_209` hypothesis supplies the simple-final invariant used by
the only endpoint-changing branch. -/
theorem endpointCapThreeCompleteness
    (identity : Identity Nat)
    (heads : identity.lhs.head = identity.rhs.head)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup)
    (cappedCounts : forall tested,
      min (identity.lhs.toList.count tested) 3 =
        min (identity.rhs.toList.count tested) 3) :
    Derives correctedBasis identity.lhs identity.rhs := by
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          exact Derives.refl _
      | cons rightSecond rightRest =>
          by_cases same : rightSecond = leftHead
          · subst rightSecond
            have capped := cappedCounts leftHead
            simp [Word.toList] at capped
            omega
          · have capped := cappedCounts rightSecond
            simp [Word.toList, same, Ne.symm same] at capped
            omega
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          by_cases same : leftSecond = leftHead
          · subst leftSecond
            have capped := cappedCounts leftHead
            simp [Word.toList] at capped
            omega
          · have capped := cappedCounts leftSecond
            simp [Word.toList, same, Ne.symm same] at capped
      | cons rightSecond rightRest =>
          let leftSplit := splitMiddleFinal leftSecond leftRest
          let rightSplit := splitMiddleFinal rightSecond rightRest
          have leftReconstruct :
              endpointWord leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) :=
            endpointWord_splitMiddleFinal
              leftHead leftSecond leftRest
          have rightReconstruct :
              endpointWord leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) :=
            endpointWord_splitMiddleFinal
              leftHead rightSecond rightRest
          have leftNormal :=
            derivesNormalizeCapThree
              leftHead leftSplit.1 leftSplit.2
          have rightNormal :=
            derivesNormalizeCapThree
              leftHead rightSplit.1 rightSplit.2
          have normalCounts :=
            endpointCapThreeReduce_normal_counts_eq
              (leftInitial := leftHead)
              (leftFinal := leftSplit.2)
              (rightInitial := leftHead)
              (rightFinal := rightSplit.2)
              (leftMiddle := leftSplit.1)
              (rightMiddle := rightSplit.1)
              (by
                intro tested
                rw [leftReconstruct, rightReconstruct]
                exact cappedCounts tested)
          have endpointS5 :
              (Identity.mk
                (endpointWord leftHead leftSplit.1 leftSplit.2)
                (endpointWord leftHead rightSplit.1
                  rightSplit.2)).SatisfiedBy
                    SemigroupBasis.Generated.S5_209.table.semigroup := by
            rw [leftReconstruct, rightReconstruct]
            exact s5Valid
          have normalizedS5 :
              (Identity.mk
                (endpointWord leftHead
                  (endpointCapThreeReduce
                    leftHead leftSplit.2 leftSplit.1)
                  leftSplit.2)
                (endpointWord leftHead
                  (endpointCapThreeReduce
                    leftHead rightSplit.2 rightSplit.1)
                  rightSplit.2)).SatisfiedBy
                    SemigroupBasis.Generated.S5_209.table.semigroup := by
            intro valuation
            exact
              (leftNormal.sound
                correctedModelsS5_209 valuation).symm.trans <|
                (endpointS5 valuation).trans <|
                  rightNormal.sound correctedModelsS5_209 valuation
          have bridge :=
            derivesSameInitial
              leftHead
              (endpointCapThreeReduce
                leftHead leftSplit.2 leftSplit.1)
              leftSplit.2
              (endpointCapThreeReduce
                leftHead rightSplit.2 rightSplit.1)
              rightSplit.2 normalizedS5 normalCounts
          rw [← leftReconstruct, ← rightReconstruct]
          exact leftNormal.trans <| bridge.trans rightNormal.symm

/-- Every arbitrary-support identity valid in both factors follows from the
corrected eleven-law basis. -/
theorem correctedJointCompleteness
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup) :
    Derives correctedBasis identity.lhs identity.rhs :=
  endpointCapThreeCompleteness identity
    (head_eq_of_s2_4_valid identity s2Valid)
    s5Valid
    (SemigroupBasis.Examples.exponentFourValid_capped_count_eq identity <|
      SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal.valid_exponentFour_of_s5_209
        identity s5Valid)

/-- Base corrected intersection for `S2_4` and `S5_209`. -/
def intersectionS2_4S5_209 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis where
  leftModels := correctedModelsS2_4
  rightModels := correctedModelsS5_209
  complete := correctedJointCompleteness

/-- Right-factor transport from `S5_209` to `S5_211`. -/
def intersectionS2_4S5_211 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      correctedBasis :=
  intersectionS2_4S5_209.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_211

/-- Right-factor transport from `S5_209` to `S5_500`. -/
def intersectionS2_4S5_500 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      correctedBasis :=
  intersectionS2_4S5_209.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_500

/-- Widen the initial factor along the existing `S2_4` embedding in
`S3_15`. -/
def intersectionS3_15S5_209 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis where
  leftModels := correctedModelsS3_15
  rightModels := correctedModelsS5_209
  complete := by
    intro identity initialValid s5Valid
    exact correctedJointCompleteness identity
      (leftZeroEmbedding.pullback_identity identity initialValid)
      s5Valid

/-- The `S3_15` widening with the `S5_211` theory transport. -/
def intersectionS3_15S5_211 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      correctedBasis :=
  intersectionS3_15S5_209.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_211

/-- The `S3_15` widening with the `S5_500` theory transport. -/
def intersectionS3_15S5_500 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      correctedBasis :=
  intersectionS3_15S5_209.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_500

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal

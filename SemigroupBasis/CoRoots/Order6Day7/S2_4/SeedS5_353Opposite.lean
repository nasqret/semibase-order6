import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_342Family

/-!
# An unrestricted `S2_4 × S5_353ᵒᵖ` family seed

The actual left-zero factor determines the initial letter.  Independent direct
`S5_353` completeness, applied to reversed words, determines the final letter;
its complete opposite basis also supplies genuine simple-endpoint semantics.

Four staged rank-017 laws construct unrestricted interior interchange.  The
staged contraction and left-endpoint laws then replay the reviewed `S5_342`
middle-reduction and closed-word saturation shapes against the *actual*
ten-law basis.  Simple-endpoint separators identify the resulting nodup
interior sets, so their permutation completes the unrestricted pair proof
before any quotient normalizer is packaged.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

set_option maxRecDepth 100000 in
/-- The exact reversed *lower-factor* basis is sound in the simple-endpoint
detector; this is model soundness, not inferred unrestricted separation. -/
theorem lowerOppositeModelsSimpleEndpoints :
    Models simpleEndpointsFour.semigroup
      (reversedBasis SemigroupBasis.CoRoots.S5_342.basis) :=
  FiniteCertificate.checkModels_sound simpleEndpointsFour
    (reversedBasis SemigroupBasis.CoRoots.S5_342.basis)
    toFinThree (by decide)

set_option maxRecDepth 100000 in
/-- The authenticated ten displayed laws preserve simple-endpoint semantics. -/
theorem displayedModelsSimpleEndpoints :
    Models simpleEndpointsFour.semigroup basis :=
  FiniteCertificate.checkModels_sound simpleEndpointsFour basis
    toFinThree (by decide)

/-- Expand a square using the actual displayed `xx = xxx`. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis (first ++ first) ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate the first endpoint using `xxyx = xyx` backwards. -/
theorem derivesLeftEndpointExpansion (first middle : Word Nat) :
    Derives basis
      ((first ++ middle) ++ first)
      (((first ++ first) ++ middle) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive.symm
      (instantiateThree first middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate any interior block using `xyyz = xyz` backwards. -/
theorem derivesMiddleDuplication
    (initial repeated final : Word Nat) :
    Derives basis
      ((initial ++ repeated) ++ final)
      (((initial ++ repeated) ++ repeated) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive.symm
      (instantiateThree initial repeated final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move a duplicated first block using the staged `xxyz = xyxz`. -/
theorem derivesDoubledInitialMove
    (first second third : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ third)
      (((first ++ second) ++ first) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 0, 2]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Gather a repeated final block using the staged `xyzy = xzyy`. -/
theorem derivesRepeatedFinalGather
    (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ second)
      (((first ++ third) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 1]) (Word.mk 0 [2, 1, 1]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The four-step staged-law chain swaps arbitrary nonempty interior blocks:
`PABC → PAABC → PABAC → PBAAC → PBAC`. -/
theorem derivesInteriorSwap
    (stem first second suffix : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ suffix)
      (((stem ++ second) ++ first) ++ suffix) := by
  have duplicate :=
    derivesMiddleDuplication stem first (second ++ suffix)
  have shift :=
    Derives.prepend stem
      (derivesDoubledInitialMove first second suffix)
  have gather :=
    Derives.appendRight
      (derivesRepeatedFinalGather stem first second) suffix
  have contract :=
    Derives.prepend stem
      (derivesMiddleDuplication second first suffix).symm
  have firstStep :
      Derives basis
        (((stem ++ first) ++ second) ++ suffix)
        ((((stem ++ first) ++ first) ++ second) ++ suffix) := by
    simpa [Word.append_assoc] using duplicate
  have secondStep :
      Derives basis
        ((((stem ++ first) ++ first) ++ second) ++ suffix)
        ((((stem ++ first) ++ second) ++ first) ++ suffix) := by
    simpa [Word.append_assoc] using shift
  have thirdStep :
      Derives basis
        ((((stem ++ first) ++ second) ++ first) ++ suffix)
        ((((stem ++ second) ++ first) ++ first) ++ suffix) := by
    simpa [Word.append_assoc] using gather
  have fourthStep :
      Derives basis
        ((((stem ++ second) ++ first) ++ first) ++ suffix)
        (((stem ++ second) ++ first) ++ suffix) := by
    simpa [Word.append_assoc] using contract
  exact firstStep.trans <|
    secondStep.trans (thirdStep.trans fourthStep)

/-- Adjacent swaps replay every finite interior permutation. -/
theorem derivesInteriorPermutation
    (initial final : Nat) {leftMiddle rightMiddle : List Nat}
    (permutation : leftMiddle.Perm rightMiddle) :
    Derives basis
      (wordOfEndpoints initial leftMiddle final)
      (wordOfEndpoints initial rightMiddle final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons first _ induction =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (induction first)
  | swap first second rest =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton second)
          (Word.singleton first)
          (wordOfPrefixFinal rest final)
  | trans _ _ first second =>
      exact (first initial).trans (second initial)

/-- Delete a repeated leading interior letter after exposing its duplicate. -/
private theorem derivesDeleteLeadingInterior
    (initial letter final : Nat) (middle : List Nat)
    (present : letter ∈ middle) :
    Derives basis
      (wordOfEndpoints initial (letter :: middle) final)
      (wordOfEndpoints initial middle final) := by
  have expose : middle.Perm (letter :: middle.erase letter) :=
    List.perm_cons_erase present
  have sourcePermutation :
      (letter :: middle).Perm
        (letter :: letter :: middle.erase letter) :=
    List.Perm.cons letter expose
  have contraction :
      Derives basis
        (wordOfEndpoints initial
          (letter :: letter :: middle.erase letter) final)
        (wordOfEndpoints initial
          (letter :: middle.erase letter) final) := by
    simpa [wordOfEndpoints_eq, Word.append_assoc] using
      (derivesMiddleDuplication
        (Word.singleton initial)
        (Word.singleton letter)
        (wordOfPrefixFinal (middle.erase letter) final)).symm
  exact
    (derivesInteriorPermutation initial final sourcePermutation).trans <|
      contraction.trans
        (derivesInteriorPermutation initial final expose.symm)

/-- Replay the reviewed `S5_342` middle reduction with the displayed laws. -/
theorem derivesNormalizeMiddle :
    ∀ (initial : Nat) (middle : List Nat) (final : Nat),
      Derives basis
        (wordOfEndpoints initial middle final)
        (wordOfEndpoints initial
          (SemigroupBasis.CoRoots.S5_342.middleReduce middle) final)
  | initial, [], final => Derives.refl _
  | initial, letter :: rest, final => by
      have tailNormal := derivesNormalizeMiddle letter rest final
      have prefixed :
          Derives basis
            (wordOfEndpoints initial (letter :: rest) final)
            (wordOfEndpoints initial
              (letter :: SemigroupBasis.CoRoots.S5_342.middleReduce rest)
              final) := by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using
          Derives.prepend (Word.singleton initial) tailNormal
      by_cases present :
        letter ∈ SemigroupBasis.CoRoots.S5_342.middleReduce rest
      · have reduceEq :
            SemigroupBasis.CoRoots.S5_342.middleReduce (letter :: rest) =
              SemigroupBasis.CoRoots.S5_342.middleReduce rest := by
          change
            finalMarkerPrefixReduce (letter :: rest) =
              finalMarkerPrefixReduce rest
          change letter ∈ finalMarkerPrefixReduce rest at present
          simp [finalMarkerPrefixReduce, present]
        rw [reduceEq]
        exact prefixed.trans <|
          derivesDeleteLeadingInterior initial letter final
            (SemigroupBasis.CoRoots.S5_342.middleReduce rest) present
      · have reduceEq :
            SemigroupBasis.CoRoots.S5_342.middleReduce (letter :: rest) =
              letter :: SemigroupBasis.CoRoots.S5_342.middleReduce rest := by
          change
            finalMarkerPrefixReduce (letter :: rest) =
              letter :: finalMarkerPrefixReduce rest
          change letter ∉ finalMarkerPrefixReduce rest at present
          simp [finalMarkerPrefixReduce, present]
        rw [reduceEq]
        exact prefixed

/-- Nodup lists with the same membership are permutations. -/
theorem permOfNodupMembership
    {left right : List Nat}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (membership : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [membership letter]

/-- Saturate closed words using actual square expansion and endpoint insertion. -/
theorem derivesSaturate
    (initial : Nat) (middle : List Nat) (final : Nat)
    (middleNodup : middle.Nodup) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (SemigroupBasis.CoRoots.S5_342.saturatedMiddle
          initial middle final) final) := by
  by_cases endpoints : initial = final
  · subst final
    by_cases present : initial ∈ middle
    · have targetPermutation :
          middle.Perm
            (SemigroupBasis.CoRoots.S5_342.saturatedMiddle
              initial middle initial) := by
        apply permOfNodupMembership middleNodup
          (SemigroupBasis.CoRoots.S5_342.saturatedMiddle_nodup
            initial initial middleNodup)
        intro letter
        rw [SemigroupBasis.CoRoots.S5_342.saturatedMiddle_mem]
        constructor
        · exact Or.inl
        · rintro (member | ⟨_, rfl⟩)
          · exact member
          · exact present
      exact derivesInteriorPermutation initial initial targetPermutation
    · cases middle with
      | nil =>
          simpa [SemigroupBasis.CoRoots.S5_342.saturatedMiddle,
            SemigroupBasis.CoRoots.S5_342.middleReduce,
            finalMarkerPrefixReduce, wordOfEndpoints_eq,
            Word.append_assoc] using
            derivesPowerExpansion (Word.singleton initial)
      | cons first rest =>
          let middleWord : Word Nat := ⟨first, rest⟩
          have expanded :
              Derives basis
                (wordOfEndpoints initial (first :: rest) initial)
                (wordOfEndpoints initial
                  (initial :: first :: rest) initial) := by
            simpa [wordOfEndpoints, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using
              derivesLeftEndpointExpansion
                (Word.singleton initial) middleWord
          have sourceNodup : (initial :: first :: rest).Nodup := by
            exact List.nodup_cons.mpr ⟨present, middleNodup⟩
          have targetPermutation :
              (initial :: first :: rest).Perm
                (SemigroupBasis.CoRoots.S5_342.saturatedMiddle
                  initial (first :: rest) initial) := by
            apply permOfNodupMembership sourceNodup
              (SemigroupBasis.CoRoots.S5_342.saturatedMiddle_nodup
                initial initial middleNodup)
            intro letter
            rw [SemigroupBasis.CoRoots.S5_342.saturatedMiddle_mem]
            simp [eq_comm, or_comm]
          exact expanded.trans <|
            derivesInteriorPermutation initial initial targetPermutation
  · simp [SemigroupBasis.CoRoots.S5_342.saturatedMiddle, endpoints]
    exact Derives.refl _

/-- The reviewed closed, nodup endpoint normal form now uses rank-017 laws. -/
theorem derivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (SemigroupBasis.CoRoots.S5_342.normalMiddle
          initial middle final) final) := by
  simpa [SemigroupBasis.CoRoots.S5_342.normalMiddle] using
    (derivesNormalizeMiddle initial middle final).trans
      (derivesSaturate initial
        (SemigroupBasis.CoRoots.S5_342.middleReduce middle) final
        (SemigroupBasis.CoRoots.S5_342.middleReduce_nodup middle))

/-- Semantic support and simple-endpoint markers recover closed interiors. -/
private theorem middleMembershipSemantic
    (letter initial : Nat) (middle : List Nat) (final : Nat)
    (closed : initial = final → initial ∈ middle) :
    letter ∈ middle ↔
      (letter ∈ initial :: middle ∨ final = letter) ∧
      ¬(initial = letter ∧ letter ∉ middle ∧ final ≠ letter) ∧
      ¬(final = letter ∧ letter ∉ initial :: middle) := by
  constructor
  · intro member
    exact ⟨Or.inl (List.Mem.tail initial member),
      fun simple => simple.2.1 member,
      fun simple => simple.2 (List.Mem.tail initial member)⟩
  · rintro ⟨support, notInitial, notFinal⟩
    apply Decidable.byContradiction
    intro absent
    by_cases initialEq : initial = letter
    · by_cases finalEq : final = letter
      · apply absent
        simpa [initialEq] using closed (initialEq.trans finalEq.symm)
      · exact notInitial ⟨initialEq, absent, finalEq⟩
    · by_cases finalEq : final = letter
      · apply notFinal
        refine ⟨finalEq, ?_⟩
        simp [Ne.symm initialEq, absent]
      · exact False.elim <| by
          rcases support with support | support
          · exact initialEq <|
              (by simpa [absent] using support : letter = initial).symm
          · exact finalEq support

/-- Equal genuine simple-endpoint evaluations identify closed normal middles. -/
theorem normalMiddleMembership
    (initial : Nat) (leftMiddle rightMiddle : List Nat) (final : Nat)
    (leftClosed : initial = final → initial ∈ leftMiddle)
    (rightClosed : initial = final → initial ∈ rightMiddle)
    (evaluations :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial leftMiddle final) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial rightMiddle final)) :
    ∀ letter, letter ∈ leftMiddle ↔ letter ∈ rightMiddle := by
  have supportIff :
      ∀ letter,
        (letter ∈ initial :: leftMiddle ∨ final = letter) ↔
          (letter ∈ initial :: rightMiddle ∨ final = letter) := by
    intro letter
    have absentIff :
        (letter ∉ initial :: leftMiddle ∧ final ≠ letter) ↔
          (letter ∉ initial :: rightMiddle ∧ final ≠ letter) := by
      constructor
      · intro absent
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            letter initial rightMiddle final).mp
        exact
          (evaluations
            (fun value => if value = letter then (0 : Fin 4) else 3)).symm.trans <|
            (simpleEndpointsEval_supportSeparator_eq_three_iff
              letter initial leftMiddle final).mpr absent
      · intro absent
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            letter initial leftMiddle final).mp
        exact
          (evaluations
            (fun value => if value = letter then (0 : Fin 4) else 3)).trans <|
            (simpleEndpointsEval_supportSeparator_eq_three_iff
              letter initial rightMiddle final).mpr absent
    constructor
    · intro member
      apply Decidable.byContradiction
      intro absent
      have rightAbsent :
          letter ∉ initial :: rightMiddle ∧ final ≠ letter := by
        simpa [not_or] using absent
      have leftAbsent := absentIff.mpr rightAbsent
      exact
        (by simpa [not_or] using leftAbsent :
          ¬(letter ∈ initial :: leftMiddle ∨ final = letter)) member
    · intro member
      apply Decidable.byContradiction
      intro absent
      have leftAbsent :
          letter ∉ initial :: leftMiddle ∧ final ≠ letter := by
        simpa [not_or] using absent
      have rightAbsent := absentIff.mp leftAbsent
      exact
        (by simpa [not_or] using rightAbsent :
          ¬(letter ∈ initial :: rightMiddle ∨ final = letter)) member
  have initialIff :
      ∀ letter,
        (initial = letter ∧ letter ∉ leftMiddle ∧ final ≠ letter) ↔
          (initial = letter ∧ letter ∉ rightMiddle ∧ final ≠ letter) := by
    intro letter
    constructor
    · intro simple
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          letter initial rightMiddle final).mp
      exact
        (evaluations
          (fun value => if value = letter then (2 : Fin 4) else 3)).symm.trans <|
          (simpleEndpointsEval_initialSeparator_eq_two_iff
            letter initial leftMiddle final).mpr simple
    · intro simple
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          letter initial leftMiddle final).mp
      exact
        (evaluations
          (fun value => if value = letter then (2 : Fin 4) else 3)).trans <|
          (simpleEndpointsEval_initialSeparator_eq_two_iff
            letter initial rightMiddle final).mpr simple
  have finalIff :
      ∀ letter,
        (final = letter ∧ letter ∉ initial :: leftMiddle) ↔
          (final = letter ∧ letter ∉ initial :: rightMiddle) := by
    intro letter
    constructor
    · intro simple
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          letter initial rightMiddle final).mp
      exact
        (evaluations
          (fun value => if value = letter then (1 : Fin 4) else 3)).symm.trans <|
          (simpleEndpointsEval_finalSeparator_eq_one_iff
            letter initial leftMiddle final).mpr simple
    · intro simple
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          letter initial leftMiddle final).mp
      exact
        (evaluations
          (fun value => if value = letter then (1 : Fin 4) else 3)).trans <|
          (simpleEndpointsEval_finalSeparator_eq_one_iff
            letter initial rightMiddle final).mpr simple
  intro letter
  rw [middleMembershipSemantic
    letter initial leftMiddle final leftClosed]
  rw [middleMembershipSemantic
    letter initial rightMiddle final rightClosed]
  exact and_congr (supportIff letter) <|
    and_congr (not_congr (initialIff letter))
      (not_congr (finalIff letter))

/-- Validity in the actual left-zero factor fixes the initial letter. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- The head of a reversed endpoint word is exactly its original final letter. -/
theorem reverseEndpointHead
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (wordOfEndpoints initial middle final).reverse.head = final := by
  induction middle generalizing initial with
  | nil => rfl
  | cons first rest induction =>
      rw [wordOfEndpoints_cons, Word.reverse_append, Word.append_head]
      exact induction first

/-- Genuine unrestricted pair completeness from reviewed lower-factor
semantics and explicitly replayed displayed-law normalization. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have actualOpposite :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup.opposite := by
    change
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup.opposite
      at rightValid
    exact rightValid
  have lowerDerivation :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.opposite_basis_complete.2
      identity actualOpposite
  have simpleValid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup := by
    intro valuation
    exact lowerDerivation.sound
      lowerOppositeModelsSimpleEndpoints valuation
  have reversedValid :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup).mp
        actualOpposite
  have finalMarker :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.valid_firstRepeatedMarkerFour
      identity.reversed reversedValid
  have reversedHeads :=
    SemigroupBasis.CoRoots.S5_342.valid_head_eq
      identity.reversed finalMarker
  have singletonIff : identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
    have evaluated := simpleValid (fun _ => (1 : Fin 4))
    constructor
    · intro singleton
      apply (simpleEndpointsSingletonSeparator identity.rhs).mp
      rw [← evaluated]
      exact
        (simpleEndpointsSingletonSeparator identity.lhs).mpr singleton
    · intro singleton
      apply (simpleEndpointsSingletonSeparator identity.lhs).mp
      rw [evaluated]
      exact
        (simpleEndpointsSingletonSeparator identity.rhs).mpr singleton
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  change leftTail = [] ↔ rightTail = [] at singletonIff
  subst rightHead
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible :
              leftSecond :: leftRest = [] := singletonIff.mpr rfl
          simp at impossible
      | cons rightSecond rightRest =>
          let leftSuffix : Word Nat := ⟨leftSecond, leftRest⟩
          let rightSuffix : Word Nat := ⟨rightSecond, rightRest⟩
          let leftSplit := splitPrefixFinal leftSuffix
          let rightSplit := splitPrefixFinal rightSuffix
          have leftReconstruct :
              wordOfEndpoints leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) := by
            rw [wordOfEndpoints_eq]
            simp only [leftSplit]
            rw [wordOfPrefixFinal_split leftSuffix]
            rfl
          have rightReconstruct :
              wordOfEndpoints leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) := by
            rw [wordOfEndpoints_eq]
            simp only [rightSplit]
            rw [wordOfPrefixFinal_split rightSuffix]
            rfl
          have finals : leftSplit.2 = rightSplit.2 := by
            have finalHeads := reversedHeads
            change
              (Word.mk leftHead (leftSecond :: leftRest)).reverse.head =
                (Word.mk leftHead (rightSecond :: rightRest)).reverse.head
              at finalHeads
            rw [← leftReconstruct, ← rightReconstruct,
              reverseEndpointHead, reverseEndpointHead] at finalHeads
            exact finalHeads
          have rightAligned :
              wordOfEndpoints leftHead rightSplit.1 leftSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) := by
            rw [finals]
            exact rightReconstruct
          let leftMiddle :=
            SemigroupBasis.CoRoots.S5_342.normalMiddle
              leftHead leftSplit.1 leftSplit.2
          let rightMiddle :=
            SemigroupBasis.CoRoots.S5_342.normalMiddle
              leftHead rightSplit.1 leftSplit.2
          have leftNormal :
              Derives basis
                (Word.mk leftHead (leftSecond :: leftRest))
                (wordOfEndpoints leftHead leftMiddle leftSplit.2) := by
            rw [← leftReconstruct]
            simpa [leftMiddle] using
              derivesNormalEndpoints
                leftHead leftSplit.1 leftSplit.2
          have rightNormal :
              Derives basis
                (Word.mk leftHead (rightSecond :: rightRest))
                (wordOfEndpoints leftHead rightMiddle leftSplit.2) := by
            rw [← rightAligned]
            simpa [rightMiddle] using
              derivesNormalEndpoints
                leftHead rightSplit.1 leftSplit.2
          have equalSimple :
              ∀ valuation : Nat → Fin 4,
                simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints leftHead leftMiddle leftSplit.2) =
                  simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints leftHead rightMiddle leftSplit.2) := by
            intro valuation
            exact
              (leftNormal.sound
                displayedModelsSimpleEndpoints valuation).symm.trans <|
                (simpleValid valuation).trans <|
                  rightNormal.sound
                    displayedModelsSimpleEndpoints valuation
          have leftClosed :
              leftHead = leftSplit.2 → leftHead ∈ leftMiddle := by
            simpa [leftMiddle] using
              SemigroupBasis.CoRoots.S5_342.normalMiddle_closed
                leftHead leftSplit.1 leftSplit.2
          have rightClosed :
              leftHead = leftSplit.2 → leftHead ∈ rightMiddle := by
            simpa [rightMiddle] using
              SemigroupBasis.CoRoots.S5_342.normalMiddle_closed
                leftHead rightSplit.1 leftSplit.2
          have middlePermutation : leftMiddle.Perm rightMiddle := by
            apply permOfNodupMembership
              (by
                simpa [leftMiddle] using
                  SemigroupBasis.CoRoots.S5_342.normalMiddle_nodup
                    leftHead leftSplit.1 leftSplit.2)
              (by
                simpa [rightMiddle] using
                  SemigroupBasis.CoRoots.S5_342.normalMiddle_nodup
                    leftHead rightSplit.1 leftSplit.2)
            exact normalMiddleMembership
              leftHead leftMiddle rightMiddle leftSplit.2
              leftClosed rightClosed equalSimple
          exact leftNormal.trans <|
            (derivesInteriorPermutation
              leftHead leftSplit.2 middlePermutation).trans
                rightNormal.symm

/-- Construct the reviewed pair structure only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Quotient normalization is downstream of genuine joint completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_10616_representative_basis :
    BasisFor S6_10616.table.semigroup basis :=
  S6_10616.representative_basis_of_normalizer normalizer

theorem s6_10616_opposite_basis :
    BasisFor S6_10616.table.semigroup.opposite (reversedBasis basis) :=
  S6_10616.opposite_basis_of_normalizer normalizer

theorem s6_7655_representative_basis :
    BasisFor S6_7655.table.semigroup basis :=
  S6_7655.representative_basis_of_normalizer normalizer

theorem s6_7655_opposite_basis :
    BasisFor S6_7655.table.semigroup.opposite (reversedBasis basis) :=
  S6_7655.opposite_basis_of_normalizer normalizer

/-- Reviewed transport retains explicit law derivations and independent
target-to-source factor-theory implications. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed

import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_353Opposite
import SemigroupBasis.CoRoots.S5_863Completeness

/-!
# An unrestricted `S3_16 × S5_353ᵒᵖ` family seed

The five independently proved `S5_863` laws occur literally, up to one
orientation, in the authenticated rank-018 package.  The remaining displayed
contraction `xyyz = xyz` duplicates every interior variable.  Matching
endpoints are first closed with the actual displayed power/return laws, so the
already kernel-green `S2_4 × S5_353ᵒᵖ` separator theorem identifies both
closed interior supports.  Interior doubling then makes the complete
`S5_863` capped-multiplicity invariant automatic.  The actual `S3_16` factor
supplies first-occurrence order, and independent `S5_353` completeness fixes
the literal final variable.  No finite-window separation or owner premise is
used.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The exact frozen eight-law package preserves simple-endpoint semantics. -/
theorem displayedModelsSimpleEndpoints :
    Models simpleEndpointsFour.semigroup basis :=
  FiniteCertificate.checkModels_sound
    simpleEndpointsFour basis toFinThree (by decide)

/-- Each independently complete `S5_863` axiom is an exact displayed law. -/
theorem coreAxiomsDeriveDisplayed
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_863.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_863.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := law00) (by simp [basis])
  · exact (Derives.fromBasis (e := law01) (by simp [basis])).symm
  · exact Derives.fromBasis (e := law04) (by simp [basis])
  · exact Derives.fromBasis (e := law02) (by simp [basis])
  · exact Derives.fromBasis (e := law03) (by simp [basis])

/-- Expand a repeated endpoint using the actual displayed `xx = xxx`. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis (first ++ first) ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Insert the closing endpoint by reversing displayed `xxyx = xyx`. -/
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

/-- Reverse the actual displayed `xyyz = xyz` in nonempty end contexts. -/
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

/-- Insert the common endpoint into an otherwise open matching-endpoint word. -/
def closedMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  if initial = final ∧ initial ∉ middle then initial :: middle else middle

theorem closedMiddle_closed
    (initial : Nat) (middle : List Nat) (final : Nat) :
    initial = final → initial ∈ closedMiddle initial middle final := by
  intro equal
  subst final
  by_cases present : initial ∈ middle
  · simp [closedMiddle, present]
  · simp [closedMiddle, present]

theorem derivesCloseMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (closedMiddle initial middle final) final) := by
  by_cases equal : initial = final
  · subst final
    by_cases present : initial ∈ middle
    · simpa [closedMiddle, present] using
        (Derives.refl (basis := basis)
          (wordOfEndpoints initial middle initial))
    · cases middle with
      | nil =>
          simpa [closedMiddle, wordOfEndpoints, Word.singleton,
            Word.append, Word.append_assoc] using
              derivesPowerExpansion (Word.singleton initial)
      | cons first rest =>
          let interior : Word Nat := ⟨first, rest⟩
          simpa [closedMiddle, present, wordOfEndpoints, interior,
            Word.singleton, Word.append, Word.append_assoc] using
              derivesLeftEndpointExpansion
                (Word.singleton initial) interior
  · simpa [closedMiddle, equal] using
      (Derives.refl (basis := basis)
        (wordOfEndpoints initial middle final))

/-- Every interior letter occurs exactly twice in its saturation block. -/
def doubleMiddle : List Nat → List Nat
  | [] => []
  | letter :: rest => letter :: letter :: doubleMiddle rest

theorem doubleMiddle_mem (letter : Nat) :
    ∀ middle : List Nat,
      letter ∈ doubleMiddle middle ↔ letter ∈ middle
  | [] => by simp [doubleMiddle]
  | first :: rest => by
      simp [doubleMiddle, doubleMiddle_mem letter rest]

theorem count_doubleMiddle (letter : Nat) :
    ∀ middle : List Nat,
      (doubleMiddle middle).count letter = 2 * middle.count letter
  | [] => by simp [doubleMiddle]
  | first :: rest => by
      by_cases equal : first = letter
      · subst first
        simp [doubleMiddle, count_doubleMiddle letter rest]
        omega
      · simp [doubleMiddle, equal, count_doubleMiddle letter rest]

/-- Displayed law 07 independently doubles every interior occurrence. -/
theorem derivesDoubleMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial (doubleMiddle middle) final) := by
  induction middle generalizing initial with
  | nil =>
      simpa [doubleMiddle] using
        (Derives.refl (basis := basis)
          (wordOfEndpoints initial [] final))
  | cons letter rest induction =>
      have duplicate :=
        derivesMiddleDuplication
          (Word.singleton initial) (Word.singleton letter)
          (wordOfPrefixFinal rest final)
      have first :
          Derives basis
            (wordOfEndpoints initial (letter :: rest) final)
            (wordOfEndpoints initial (letter :: letter :: rest) final) := by
        simpa only [wordOfEndpoints_eq, wordOfPrefixFinal_cons,
          Word.append_assoc] using duplicate
      have second :=
        Derives.prepend
          ((Word.singleton initial) ++ (Word.singleton letter))
          (induction letter)
      exact first.trans <| by
        simpa [doubleMiddle, wordOfEndpoints, Word.singleton,
          Word.append, Word.append_assoc] using second

/-- Closing followed by saturation is derivable solely from frozen laws. -/
theorem derivesSaturatedEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (doubleMiddle (closedMiddle initial middle final)) final) :=
  (derivesCloseMiddle initial middle final).trans <|
    derivesDoubleMiddle initial (closedMiddle initial middle final) final

/-- A saturated interior membership forces multiplicity at least two. -/
theorem saturatedMiddle_count_ge_two
    (letter : Nat) (middle : List Nat)
    (present : letter ∈ doubleMiddle middle) :
    2 ≤ (doubleMiddle middle).count letter := by
  have original : letter ∈ middle :=
    (doubleMiddle_mem letter middle).mp present
  have positive : 0 < middle.count letter :=
    List.count_pos_iff.mpr original
  rw [count_doubleMiddle]
  omega

/-- Equal saturated-interior support makes exact capped multiplicities agree. -/
theorem cappedSaturatedEndpoints_eq
    (initial final letter : Nat)
    (leftMiddle rightMiddle : List Nat)
    (membership :
      letter ∈ doubleMiddle leftMiddle ↔
        letter ∈ doubleMiddle rightMiddle) :
    SemigroupBasis.CoRoots.S5_107.cappedMultiplicity
        (wordOfEndpoints initial (doubleMiddle leftMiddle) final) letter =
      SemigroupBasis.CoRoots.S5_107.cappedMultiplicity
        (wordOfEndpoints initial (doubleMiddle rightMiddle) final) letter := by
  by_cases leftPresent : letter ∈ doubleMiddle leftMiddle
  · have rightPresent := membership.mp leftPresent
    have leftInterior :=
      saturatedMiddle_count_ge_two letter leftMiddle leftPresent
    have rightInterior :=
      saturatedMiddle_count_ge_two letter rightMiddle rightPresent
    have leftWhole :
        2 ≤
          (wordOfEndpoints initial (doubleMiddle leftMiddle) final).toList.count
            letter := by
      simp only [toList_wordOfEndpoints, List.count_cons, List.count_append]
      omega
    have rightWhole :
        2 ≤
          (wordOfEndpoints initial (doubleMiddle rightMiddle) final).toList.count
            letter := by
      simp only [toList_wordOfEndpoints, List.count_cons, List.count_append]
      omega
    change
      Nat.min 2
          ((wordOfEndpoints initial (doubleMiddle leftMiddle) final).toList.count
            letter) =
        Nat.min 2
          ((wordOfEndpoints initial (doubleMiddle rightMiddle) final).toList.count
            letter)
    simp only [Nat.min_def]
    split <;> omega
  · have rightAbsent : letter ∉ doubleMiddle rightMiddle := by
      intro present
      exact leftPresent (membership.mpr present)
    have leftZero : (doubleMiddle leftMiddle).count letter = 0 :=
      List.count_eq_zero.mpr leftPresent
    have rightZero : (doubleMiddle rightMiddle).count letter = 0 :=
      List.count_eq_zero.mpr rightAbsent
    change
      Nat.min 2 ((initial :: (doubleMiddle leftMiddle ++ [final])).count letter) =
        Nat.min 2 ((initial :: (doubleMiddle rightMiddle ++ [final])).count letter)
    simp only [List.count_cons, List.count_append, leftZero, rightZero]

/-- The actual frozen left table contains the canonical LRB detector. -/
def canonicalLeftIntoActual :
    Embedding leftRegularBandThree.semigroup leftTable.semigroup where
  toFun := fun value => value
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equal
    exact equal

theorem firstOccurrences_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity (canonicalLeftIntoActual.pullback_identity identity valid)

/-- Actual lower-factor completeness proves the genuine endpoint detector. -/
theorem simpleEndpoints_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy simpleEndpointsFour.semigroup := by
  have actual :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup.opposite := by
    exact valid
  have derivation :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.opposite_basis_complete.2
      identity actual
  exact derivation.sound
    SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed.lowerOppositeModelsSimpleEndpoints

/-- Actual lower-factor semantics fix the final letter via the reversed marker. -/
theorem reversedHeads_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.reverse.head = identity.rhs.reverse.head := by
  have actual :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup.opposite := by
    exact valid
  have reversedValid :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup).mp actual
  have marker :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.valid_firstRepeatedMarkerFour
      identity.reversed reversedValid
  exact SemigroupBasis.CoRoots.S5_342.valid_head_eq identity.reversed marker

/-- Genuine unrestricted completeness for the immutable eight-law package. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have order := firstOccurrences_of_leftValid identity leftValid
  have simpleValid := simpleEndpoints_of_rightValid identity rightValid
  have reverseHeads := reversedHeads_of_rightValid identity rightValid
  have singletonIff : identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
    have evaluated := simpleValid (fun _ => (1 : Fin 4))
    constructor
    · intro singleton
      apply (simpleEndpointsSingletonSeparator identity.rhs).mp
      rw [← evaluated]
      exact (simpleEndpointsSingletonSeparator identity.lhs).mpr singleton
    · intro singleton
      apply (simpleEndpointsSingletonSeparator identity.lhs).mp
      rw [evaluated]
      exact (simpleEndpointsSingletonSeparator identity.rhs).mpr singleton
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  have heads : leftHead = rightHead := by
    have firstHeads := congrArg (fun letters : List Nat => letters.head?) order
    simpa [Word.toList, firstOccurrenceSequence] using firstHeads
  subst rightHead
  change leftTail = [] ↔ rightTail = [] at singletonIff
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible : leftSecond :: leftRest = [] := singletonIff.mpr rfl
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
            have equal := reverseHeads
            change
              (Word.mk leftHead (leftSecond :: leftRest)).reverse.head =
                (Word.mk leftHead (rightSecond :: rightRest)).reverse.head
              at equal
            rw [← leftReconstruct, ← rightReconstruct,
              SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed.reverseEndpointHead,
              SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed.reverseEndpointHead]
              at equal
            exact equal
          have rightAligned :
              wordOfEndpoints leftHead rightSplit.1 leftSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) := by
            rw [finals]
            exact rightReconstruct
          let leftClosed := closedMiddle leftHead leftSplit.1 leftSplit.2
          let rightClosed := closedMiddle leftHead rightSplit.1 leftSplit.2
          let leftMiddle := doubleMiddle leftClosed
          let rightMiddle := doubleMiddle rightClosed
          let leftWord := wordOfEndpoints leftHead leftMiddle leftSplit.2
          let rightWord := wordOfEndpoints leftHead rightMiddle leftSplit.2
          have leftNormal :
              Derives basis
                (Word.mk leftHead (leftSecond :: leftRest)) leftWord := by
            rw [← leftReconstruct]
            exact derivesSaturatedEndpoints leftHead leftSplit.1 leftSplit.2
          have rightNormal :
              Derives basis
                (Word.mk leftHead (rightSecond :: rightRest)) rightWord := by
            rw [← rightAligned]
            exact derivesSaturatedEndpoints leftHead rightSplit.1 leftSplit.2
          have equalSimple :
              ∀ valuation : Nat → Fin 4,
                simpleEndpointsFour.semigroup.eval valuation leftWord =
                  simpleEndpointsFour.semigroup.eval valuation rightWord := by
            intro valuation
            exact
              (leftNormal.sound displayedModelsSimpleEndpoints valuation).symm.trans <|
                (simpleValid valuation).trans <|
                  rightNormal.sound displayedModelsSimpleEndpoints valuation
          have leftClosedProof : leftHead = leftSplit.2 → leftHead ∈ leftMiddle := by
            intro equal
            exact (doubleMiddle_mem leftHead leftClosed).mpr <|
              closedMiddle_closed leftHead leftSplit.1 leftSplit.2 equal
          have rightClosedProof : leftHead = leftSplit.2 → leftHead ∈ rightMiddle := by
            intro equal
            exact (doubleMiddle_mem leftHead rightClosed).mpr <|
              closedMiddle_closed leftHead rightSplit.1 leftSplit.2 equal
          have middleMembership : ∀ letter, letter ∈ leftMiddle ↔ letter ∈ rightMiddle :=
            SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank017.Seed.normalMiddleMembership
              leftHead leftMiddle rightMiddle leftSplit.2
              leftClosedProof rightClosedProof equalSimple
          have normalizedLeftValid :
              (⟨leftWord, rightWord⟩ : Identity Nat).SatisfiedBy
                leftTable.semigroup := by
            intro valuation
            exact
              (leftNormal.sound leftModels valuation).symm.trans <|
                (leftValid valuation).trans <|
                  rightNormal.sound leftModels valuation
          have signature :
              SemigroupBasis.CoRoots.S5_863.SameInitialSimpleFinalSignature
                leftWord rightWord := by
            refine ⟨
              firstOccurrences_of_leftValid
                (⟨leftWord, rightWord⟩ : Identity Nat) normalizedLeftValid,
              ?_, ?_⟩
            · intro letter
              exact cappedSaturatedEndpoints_eq
                leftHead leftSplit.2 letter leftClosed rightClosed
                (middleMembership letter)
            · simp [leftWord, rightWord, wordOfEndpoints, Word.final]
          have core :=
            SemigroupBasis.CoRoots.S5_863.derivesOfSignature signature
          exact leftNormal.trans <|
            (core.transport coreAxiomsDeriveDisplayed).trans rightNormal.symm

/-- Package the actual intersection only after its unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Reviewed quotient normalizer for both independently authenticated classes. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_10620_representative_basis :
    BasisFor S6_10620.table.semigroup basis :=
  S6_10620.representative_basis_of_normalizer normalizer

theorem s6_10620_opposite_basis :
    BasisFor S6_10620.table.semigroup.opposite (reversedBasis basis) :=
  S6_10620.opposite_basis_of_normalizer normalizer

theorem s6_7659_representative_basis :
    BasisFor S6_7659.table.semigroup basis :=
  S6_7659.representative_basis_of_normalizer normalizer

theorem s6_7659_opposite_basis :
    BasisFor S6_7659.table.semigroup.opposite (reversedBasis basis) :=
  S6_7659.opposite_basis_of_normalizer normalizer

/-- Transport remains conditional on explicit displayed derivations and both
independently proved unrestricted factor-theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed

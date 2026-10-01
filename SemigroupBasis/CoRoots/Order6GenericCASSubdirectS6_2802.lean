import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2802
import SemigroupBasis.Generated.S3_8

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2802

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2802.subdirectPair

private def instantiateTwoWords
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | index + 2 => Word.singleton (index + 2)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | index + 3 => Word.singleton (index + 3)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.basis]

private theorem rootLaw4 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law4.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law4.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.basis]

private theorem derivesCommutativity (first second : Word Nat) :
    Derives rootBasis (first ++ second) (second ++ first) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateTwoWords first second)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law0,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using
      substituted

private theorem derivesPermutation (first second : Word Nat)
    (permutation : first.toList.Perm second.toList) :
    Derives rootBasis first second :=
  SemigroupBasis.CoRoots.Order6GenericCASShortTwo.derivesPermutation
    derivesCommutativity first second permutation

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem bind_append
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution =
      first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem supportOfCapped
    {first second : List Nat}
    (capped : ∀ letter,
      min (first.count letter) 2 = min (second.count letter) 2) :
    ∀ letter, letter ∈ first ↔ letter ∈ second := by
  intro letter
  constructor
  · intro member
    have positive : 0 < first.count letter :=
      List.count_pos_iff.mpr member
    have secondPositive : 0 < second.count letter := by
      have equality := capped letter
      omega
    exact List.count_pos_iff.mp secondPositive
  · intro member
    have positive : 0 < second.count letter :=
      List.count_pos_iff.mpr member
    have firstPositive : 0 < first.count letter := by
      have equality := capped letter
      omega
    exact List.count_pos_iff.mp firstPositive

private theorem all_eq_of_count_eq_length (selected : Nat) :
    ∀ letters : List Nat,
      letters.count selected = letters.length →
        ∀ letter, letter ∈ letters → letter = selected
  | [], _ => by simp
  | head :: tail, equality => by
      by_cases headSelected : head = selected
      · subst head
        rw [List.count_cons_self, List.length_cons] at equality
        have tailEquality :
            tail.count selected = tail.length := by
          omega
        intro letter member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact all_eq_of_count_eq_length selected tail
            tailEquality letter member
      · have bound :=
          List.count_le_length (a := selected) (l := tail)
        rw [List.count_cons_of_ne headSelected,
          List.length_cons] at equality
        omega

private theorem count_eq_length_of_all_eq
    (selected : Nat) (letters : List Nat)
    (allEqual : ∀ letter, letter ∈ letters → letter = selected) :
    letters.count selected = letters.length := by
  induction letters with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headSelected : head = selected := allEqual head (by simp)
      subst head
      rw [List.count_cons_self, List.length_cons]
      congr 1
      exact inductionHypothesis <| by
        intro letter member
        exact allEqual letter (by simp [member])

/-- Capped multiplicities are injective on equal-length words of length at
most three. The only apparent `2`/`3` ambiguity forces singleton support and
is resolved by support preservation. -/
private theorem countEqOfCappedShort
    {first second : List Nat}
    (lengthEq : first.length = second.length)
    (short : first.length ≤ 3)
    (capped : ∀ letter,
      min (first.count letter) 2 = min (second.count letter) 2) :
    ∀ letter, first.count letter = second.count letter := by
  have support := supportOfCapped capped
  have secondShort : second.length ≤ 3 := by omega
  intro selected
  have firstBound :=
    List.count_le_length (a := selected) (l := first)
  have secondBound :=
    List.count_le_length (a := selected) (l := second)
  by_cases firstThree : first.count selected = 3
  · have firstLength : first.length = 3 := by omega
    have firstAll :=
      all_eq_of_count_eq_length selected first (by omega)
    have secondAll :
        ∀ letter, letter ∈ second → letter = selected := by
      intro letter member
      exact firstAll letter ((support letter).mpr member)
    have secondCount :=
      count_eq_length_of_all_eq selected second secondAll
    omega
  · by_cases secondThree : second.count selected = 3
    · have secondLength : second.length = 3 := by omega
      have secondAll :=
        all_eq_of_count_eq_length selected second (by omega)
      have firstAll :
          ∀ letter, letter ∈ first → letter = selected := by
        intro letter member
        exact secondAll letter ((support letter).mp member)
      have firstCount :=
        count_eq_length_of_all_eq selected first firstAll
      omega
    · have equality := capped selected
      omega

private def twiceFronted (selected : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons selected
    (selected :: (word.toList.erase selected).erase selected)

private theorem word_perm_twiceFronted
    (selected : Nat) (word : Word Nat)
    (repeated : 2 ≤ word.toList.count selected) :
    word.toList.Perm (twiceFronted selected word).toList := by
  have firstMember : selected ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase firstMember
  have erasedCount :
      (word.toList.erase selected).count selected =
        word.toList.count selected - 1 := by
    rw [List.count_erase_self]
  have secondMember : selected ∈ word.toList.erase selected :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase secondMember
  simpa [twiceFronted, wordOfCons, Word.toList] using
    first.trans (List.Perm.cons selected second)

/-- Add one occurrence of a letter which is already repeated in a long word.
Law 4 is applied after exposing two copies and two nonempty residual blocks. -/
private theorem derivesSupportedSingleExpansion
    (selected : Nat) (word : Word Nat)
    (long : 4 ≤ word.toList.length)
    (repeated : 2 ≤ word.toList.count selected) :
    Derives rootBasis word (Word.singleton selected ++ word) := by
  have firstMember : selected ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  have erasedCount :
      (word.toList.erase selected).count selected =
        word.toList.count selected - 1 := by
    rw [List.count_erase_self]
  have secondMember : selected ∈ word.toList.erase selected :=
    List.count_pos_iff.mp (by omega)
  have firstLength := List.length_erase_of_mem firstMember
  have secondLength := List.length_erase_of_mem secondMember
  have residualLong :
      2 ≤ ((word.toList.erase selected).erase selected).length := by
    omega
  have enter :=
    derivesPermutation word (twiceFronted selected word)
      (word_perm_twiceFronted selected word repeated)
  cases residualEq : (word.toList.erase selected).erase selected with
  | nil => simp [residualEq] at residualLong
  | cons first rest =>
      cases rest with
      | nil => simp [residualEq] at residualLong
      | cons second suffix =>
          have expanded :=
            Derives.subst rootLaw4 <|
              instantiateThreeWords
                (Word.singleton selected)
                (Word.singleton first)
                (wordOfCons second suffix)
          have middle :
              Derives rootBasis
                (twiceFronted selected word)
                (Word.singleton selected ++ twiceFronted selected word) := by
            simpa [twiceFronted, residualEq, wordOfCons,
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law4,
              instantiateThreeWords, Word.bind, Word.append,
              Word.singleton, Word.append_assoc] using expanded
          have exit :
              Derives rootBasis
                (Word.singleton selected ++ twiceFronted selected word)
                (Word.singleton selected ++ word) :=
            Derives.prepend (Word.singleton selected) enter.symm
          exact enter.trans (middle.trans exit)

private def selectedSquare (selected : Nat) : Word Nat :=
  Word.singleton selected ++ Word.singleton selected

/-- Add the two-letter protected context used to replay the complete
`S3_8` theory. -/
private theorem derivesSupportedDoubleExpansion
    (selected : Nat) (word : Word Nat)
    (long : 4 ≤ word.toList.length)
    (repeated : 2 ≤ word.toList.count selected) :
    Derives rootBasis word (selectedSquare selected ++ word) := by
  have first :=
    derivesSupportedSingleExpansion selected word long repeated
  have extendedLong :
      4 ≤ (Word.singleton selected ++ word).toList.length := by
    rw [Word.toList_append, List.length_append]
    simp
    omega
  have extendedRepeated :
      2 ≤ (Word.singleton selected ++ word).toList.count selected := by
    rw [Word.toList_append, List.count_append]
    simp
    omega
  have second :=
    derivesSupportedSingleExpansion selected
      (Word.singleton selected ++ word) extendedLong extendedRepeated
  simpa [selectedSquare, Word.append_assoc] using first.trans second

/-- Replay `xx = xxx` behind two fixed nonempty context words. -/
private theorem derivesExponentExpansionBehind
    (contextFirst contextSecond word : Word Nat) :
    Derives rootBasis
      ((contextFirst ++ contextSecond) ++ (word ++ word))
      ((contextFirst ++ contextSecond) ++ ((word ++ word) ++ word)) := by
  have enter :=
    derivesCommutativity (contextFirst ++ contextSecond) (word ++ word)
  have expanded :=
    Derives.subst rootLaw4 <|
      instantiateThreeWords word contextFirst contextSecond
  have expanded' :
      Derives rootBasis
        ((word ++ word) ++ (contextFirst ++ contextSecond))
        (((word ++ word) ++ word) ++
          (contextFirst ++ contextSecond)) := by
    simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.law4,
      instantiateThreeWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using expanded
  have exit :=
    derivesCommutativity ((word ++ word) ++ word)
      (contextFirst ++ contextSecond)
  exact enter.trans <| expanded'.trans exit

/-- Transport an arbitrary derivation from the complete `S3_8` basis while
retaining two nonempty context words. -/
private theorem liftExponentThree
    {first second : Word Nat}
    (derivation : Derives commutativeExponentThreeBasis first second)
    (contextFirst contextSecond : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives rootBasis
      ((contextFirst ++ contextSecond) ++ first.bind substitution)
      ((contextFirst ++ contextSecond) ++ second.bind substitution) := by
  induction derivation generalizing contextFirst contextSecond substitution with
  | fromBasis member =>
      simp only [commutativeExponentThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [exponentThreeLaw, exponentXX, exponentXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesExponentExpansionBehind contextFirst contextSecond
            (substitution 0)
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [exponentCommutativityLaw, exponentXY, exponentYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend (contextFirst ++ contextSecond) commute
  | refl => exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm
        (inductionHypothesis contextFirst contextSecond substitution)
  | trans _ _ firstProof secondProof =>
      exact Derives.trans
        (firstProof contextFirst contextSecond substitution)
        (secondProof contextFirst contextSecond substitution)
  | prepend added _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis contextFirst
          (contextSecond ++ added.bind substitution) substitution
  | appendRight _ added inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis contextFirst contextSecond substitution)
          (added.bind substitution)
  | subst _ firstSubstitution inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis contextFirst contextSecond
          (fun letter => (firstSubstitution letter).bind substitution)

private theorem s3_8_table_eq_canonical_catalogue :
    SemigroupBasis.Generated.S3_8.table =
      SemigroupBasis.Generated.Catalogue.S3_8.table := by
  unfold SemigroupBasis.Generated.S3_8.table
    SemigroupBasis.Generated.Catalogue.S3_8.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext first second
  decide +revert

private theorem generatedLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup) :
    identity.SatisfiedBy SemigroupBasis.Generated.S3_8.table.semigroup := by
  rw [s3_8_table_eq_canonical_catalogue]
  exact valid

private theorem concreteLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup := by
  rw [← SemigroupBasis.Generated.S3_8.table_eq_catalogue_model]
  exact generatedLeftValid identity valid

private theorem derivesShort
    (identity : Identity Nat)
    (sameLength : identity.lhs.toList.length =
      identity.rhs.toList.length)
    (short : identity.lhs.toList.length ≤ 3)
    (capped : ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2) :
    Derives rootBasis identity.lhs identity.rhs := by
  exact derivesPermutation identity.lhs identity.rhs <|
    List.perm_iff_count.mpr <|
      countEqOfCappedShort sameLength short capped

private theorem derivesLong
    (identity : Identity Nat)
    (lhsLong : 4 ≤ identity.lhs.toList.length)
    (rhsLong : 4 ≤ identity.rhs.toList.length)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_8.table.semigroup)
    (capped : ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2) :
    Derives rootBasis identity.lhs identity.rhs := by
  by_cases hasRepeated :
      ∃ selected, 2 ≤ identity.lhs.toList.count selected
  · obtain ⟨selected, lhsRepeated⟩ := hasRepeated
    have rhsRepeated :
        2 ≤ identity.rhs.toList.count selected := by
      have equality := capped selected
      omega
    have lhsExpanded :=
      derivesSupportedDoubleExpansion selected identity.lhs
        lhsLong lhsRepeated
    have rhsExpanded :=
      derivesSupportedDoubleExpansion selected identity.rhs
        rhsLong rhsRepeated
    have factorDerivation :
        Derives commutativeExponentThreeBasis
          identity.lhs identity.rhs :=
      SemigroupBasis.Generated.S3_8.representative_basis.2
        identity leftValid
    let selectedWord := Word.singleton selected
    have lifted :=
      liftExponentThree factorDerivation selectedWord selectedWord
        Word.singleton
    have lifted' :
        Derives rootBasis
          (selectedSquare selected ++ identity.lhs)
          (selectedSquare selected ++ identity.rhs) := by
      simpa [selectedSquare, selectedWord, bind_singleton] using lifted
    exact lhsExpanded.trans <| lifted'.trans rhsExpanded.symm
  · have countEq :
        ∀ letter,
          identity.lhs.toList.count letter =
            identity.rhs.toList.count letter := by
      intro letter
      have lhsSmall : identity.lhs.toList.count letter < 2 := by
        have notRepeated :
            ¬ 2 ≤ identity.lhs.toList.count letter := by
          intro repeated
          exact hasRepeated ⟨letter, repeated⟩
        omega
      have equality := capped letter
      have lhsBound : identity.lhs.toList.count letter ≤ 2 := by omega
      by_cases rhsBound : identity.rhs.toList.count letter ≤ 2
      · simpa [Nat.min_eq_left lhsBound,
          Nat.min_eq_left rhsBound] using equality
      · have rhsLarge : 2 ≤ identity.rhs.toList.count letter := by omega
        have lhsEqTwo : identity.lhs.toList.count letter = 2 := by
          simpa [Nat.min_eq_left lhsBound,
            Nat.min_eq_right rhsLarge] using equality
        omega
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq

private theorem factorIntersectionComplete
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have leftGenerated := generatedLeftValid identity leftValid
  have capped := exponentValid_capped_count_eq identity
    (concreteLeftValid identity leftValid)
  rcases
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family.lengthShape
        identity rightValid with
    ⟨lhsOne, rhsOne⟩ |
    ⟨lhsTwo, rhsTwo⟩ |
    ⟨lhsThree, rhsThree⟩ |
    ⟨lhsLong, rhsLong⟩
  · exact derivesShort identity (lhsOne.trans rhsOne.symm) (by omega) capped
  · exact derivesShort identity (lhsTwo.trans rhsTwo.symm) (by omega) capped
  · exact derivesShort identity
      (lhsThree.trans rhsThree.symm) (by omega) capped
  · exact derivesLong identity lhsLong rhsLong leftGenerated capped

private theorem leftFactorModels :
    Models SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.models
      identity member)

private theorem rightFactorModels :
    Models SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2802.models
      identity member)

/-- Exact source-only unconditional basis endpoint for the mixed generic-CAS
root `S6_2802 = S3_8 x S4_11`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    factorIntersectionComplete).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2802

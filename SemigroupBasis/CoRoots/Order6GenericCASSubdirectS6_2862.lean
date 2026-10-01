import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2862
import SemigroupBasis.Generated.S3_10

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2862

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2862.subdirectPair

private def instantiateTwoWords
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | index + 2 => Word.singleton (index + 2)

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | index + 4 => Word.singleton (index + 4)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis]

private theorem rootLaw6 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis]

private theorem derivesCommutativity (first second : Word Nat) :
    Derives rootBasis (first ++ second) (second ++ first) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateTwoWords first second)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law0,
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

/-- On equal-length words of length at most three, support plus coordinate
parity determines every exact multiplicity. -/
private theorem countEqOfParityShort
    {first second : List Nat}
    (lengthEq : first.length = second.length)
    (short : first.length ≤ 3)
    (support : ∀ letter, letter ∈ first ↔ letter ∈ second)
    (parity : ∀ letter,
      first.count letter % 2 = second.count letter % 2) :
    ∀ letter, first.count letter = second.count letter := by
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
    · have zeroEq :
          first.count selected = 0 ↔ second.count selected = 0 := by
        rw [List.count_eq_zero, List.count_eq_zero]
        constructor
        · intro absent member
          exact absent ((support selected).mpr member)
        · intro absent member
          exact absent ((support selected).mp member)
      have residue := parity selected
      by_cases firstZero : first.count selected = 0
      · have secondZero := zeroEq.mp firstZero
        omega
      · have secondNonzero : second.count selected ≠ 0 :=
          fun secondZero => firstZero (zeroEq.mpr secondZero)
        omega

private def fronted (selected : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons selected (word.toList.erase selected)

private theorem word_perm_fronted
    (selected : Nat) (word : Word Nat)
    (present : selected ∈ word.toList) :
    word.toList.Perm (fronted selected word).toList := by
  simpa [fronted, wordOfCons, Word.toList] using
    List.perm_cons_erase present

private def selectedSquare (selected : Nat) : Word Nat :=
  Word.singleton selected ++ Word.singleton selected

private def selectedTriple (selected : Nat) : Word Nat :=
  selectedSquare selected ++ Word.singleton selected

private def selectedFourth (selected : Nat) : Word Nat :=
  selectedSquare selected ++ selectedSquare selected

/-- Add two copies of a supported letter to a long word. Exposing the selected
letter leaves three nonempty blocks, so law 6 applies directly. -/
private theorem derivesSupportedPairExpansion
    (selected : Nat) (word : Word Nat)
    (long : 4 ≤ word.toList.length)
    (present : selected ∈ word.toList) :
    Derives rootBasis word (selectedSquare selected ++ word) := by
  have erasedLength := List.length_erase_of_mem present
  have residualLong : 3 ≤ (word.toList.erase selected).length := by
    omega
  have enter :=
    derivesPermutation word (fronted selected word)
      (word_perm_fronted selected word present)
  cases residualEq : word.toList.erase selected with
  | nil => simp [residualEq] at residualLong
  | cons first rest =>
      cases rest with
      | nil => simp [residualEq] at residualLong
      | cons second more =>
          cases more with
          | nil => simp [residualEq] at residualLong
          | cons third suffix =>
              let selectedWord := Word.singleton selected
              let residualWord := wordOfCons first (second :: third :: suffix)
              have moveSelected :=
                derivesCommutativity selectedWord residualWord
              have expanded :=
                Derives.subst rootLaw6 <|
                  instantiateFourWords
                    (Word.singleton first)
                    (Word.singleton second)
                    (wordOfCons third suffix)
                    selectedWord
              have expanded' :
                  Derives rootBasis
                    (residualWord ++ selectedWord)
                    (residualWord ++ selectedTriple selected) := by
                simpa [residualWord, selectedWord, selectedTriple,
                  selectedSquare, wordOfCons,
                  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6,
                  instantiateFourWords, Word.bind, Word.append,
                  Word.singleton, Word.append_assoc] using expanded
              have moveTriple :=
                derivesCommutativity residualWord (selectedTriple selected)
              have middle :
                  Derives rootBasis
                    (fronted selected word)
                    (selectedSquare selected ++ fronted selected word) := by
                have combined :=
                  moveSelected.trans (expanded'.trans moveTriple)
                simpa [fronted, residualEq, residualWord, selectedWord,
                  selectedTriple, selectedSquare, wordOfCons,
                  Word.append, Word.singleton, Word.append_assoc] using
                    combined
              have exit :
                  Derives rootBasis
                    (selectedSquare selected ++ fronted selected word)
                    (selectedSquare selected ++ word) :=
                Derives.prepend (selectedSquare selected) enter.symm
              exact enter.trans (middle.trans exit)

/-- Add the four-letter protected context used to replay the complete
`S3_10` parity theory. -/
private theorem derivesSupportedFourthExpansion
    (selected : Nat) (word : Word Nat)
    (long : 4 ≤ word.toList.length)
    (present : selected ∈ word.toList) :
    Derives rootBasis word (selectedFourth selected ++ word) := by
  have first :=
    derivesSupportedPairExpansion selected word long present
  have extendedLong :
      4 ≤ (selectedSquare selected ++ word).toList.length := by
    rw [Word.toList_append, List.length_append]
    simp [selectedSquare]
    omega
  have extendedPresent :
      selected ∈ (selectedSquare selected ++ word).toList := by
    simp [selectedSquare, Word.toList_append, Word.singleton, Word.toList]
  have second :=
    derivesSupportedPairExpansion selected
      (selectedSquare selected ++ word) extendedLong extendedPresent
  simpa [selectedFourth, Word.append_assoc] using first.trans second

/-- Replay `x = xxx` behind three fixed nonempty context words. -/
private theorem derivesParityExpansionBehind
    (contextFirst contextSecond contextThird word : Word Nat) :
    Derives rootBasis
      (((contextFirst ++ contextSecond) ++ contextThird) ++ word)
      (((contextFirst ++ contextSecond) ++ contextThird) ++
        ((word ++ word) ++ word)) := by
  have expanded :=
    Derives.subst rootLaw6 <|
      instantiateFourWords contextFirst contextSecond contextThird word
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using expanded

/-- Transport an arbitrary derivation from the complete `S3_10` basis while
retaining three nonempty context words. -/
private theorem liftParityThree
    {first second : Word Nat}
    (derivation : Derives commutativeParityBasis first second)
    (contextFirst contextSecond contextThird : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives rootBasis
      (((contextFirst ++ contextSecond) ++ contextThird) ++
        first.bind substitution)
      (((contextFirst ++ contextSecond) ++ contextThird) ++
        second.bind substitution) := by
  induction derivation generalizing contextFirst contextSecond contextThird substitution with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesParityExpansionBehind contextFirst contextSecond
            contextThird (substitution 0)
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend
            ((contextFirst ++ contextSecond) ++ contextThird) commute
  | refl => exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm
        (inductionHypothesis contextFirst contextSecond contextThird
          substitution)
  | trans _ _ firstProof secondProof =>
      exact Derives.trans
        (firstProof contextFirst contextSecond contextThird substitution)
        (secondProof contextFirst contextSecond contextThird substitution)
  | prepend added _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis contextFirst contextSecond
          (contextThird ++ added.bind substitution) substitution
  | appendRight _ added inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis contextFirst contextSecond contextThird
            substitution)
          (added.bind substitution)
  | subst _ firstSubstitution inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis contextFirst contextSecond contextThird
          (fun letter => (firstSubstitution letter).bind substitution)

private theorem generatedLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup) :
    identity.SatisfiedBy SemigroupBasis.Generated.S3_10.table.semigroup := by
  rw [SemigroupBasis.Generated.S3_10.table_eq_canonical_catalogue]
  exact valid

private theorem concreteLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup) :
    identity.SatisfiedBy parityIdentityThree.semigroup := by
  rw [← SemigroupBasis.Generated.S3_10.table_eq_catalogue_model]
  exact generatedLeftValid identity valid

private theorem derivesShort
    (identity : Identity Nat)
    (sameLength : identity.lhs.toList.length =
      identity.rhs.toList.length)
    (short : identity.lhs.toList.length ≤ 3)
    (support : ∀ letter,
      letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList)
    (parity : ∀ letter,
      identity.lhs.toList.count letter % 2 =
        identity.rhs.toList.count letter % 2) :
    Derives rootBasis identity.lhs identity.rhs := by
  exact derivesPermutation identity.lhs identity.rhs <|
    List.perm_iff_count.mpr <|
      countEqOfParityShort sameLength short support parity

private theorem derivesLong
    (identity : Identity Nat)
    (lhsLong : 4 ≤ identity.lhs.toList.length)
    (rhsLong : 4 ≤ identity.rhs.toList.length)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_10.table.semigroup)
    (support : ∀ letter,
      letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList) :
    Derives rootBasis identity.lhs identity.rhs := by
  let selected := identity.lhs.head
  have lhsPresent : selected ∈ identity.lhs.toList := by
    simp [selected, Word.toList]
  have rhsPresent : selected ∈ identity.rhs.toList :=
    (support selected).mp lhsPresent
  have lhsExpanded :=
    derivesSupportedFourthExpansion selected identity.lhs
      lhsLong lhsPresent
  have rhsExpanded :=
    derivesSupportedFourthExpansion selected identity.rhs
      rhsLong rhsPresent
  have factorDerivation :
      Derives commutativeParityBasis identity.lhs identity.rhs :=
    SemigroupBasis.Generated.S3_10.representative_basis.2
      identity leftValid
  let selectedWord := Word.singleton selected
  have lifted :=
    liftParityThree factorDerivation selectedWord selectedWord
      (selectedSquare selected) Word.singleton
  have lifted' :
      Derives rootBasis
        (selectedFourth selected ++ identity.lhs)
        (selectedFourth selected ++ identity.rhs) := by
    simpa [selectedFourth, selectedSquare, selectedWord,
      bind_singleton, Word.append_assoc] using lifted
  exact lhsExpanded.trans <| lifted'.trans rhsExpanded.symm

private theorem factorIntersectionComplete
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have leftGenerated := generatedLeftValid identity leftValid
  have leftConcrete := concreteLeftValid identity leftValid
  have support := parityIdentityValid_support identity leftConcrete
  have parity := parityIdentityValid_parity identity leftConcrete
  rcases
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family.lengthShape
        identity rightValid with
    ⟨lhsOne, rhsOne⟩ |
    ⟨lhsTwo, rhsTwo⟩ |
    ⟨lhsThree, rhsThree⟩ |
    ⟨lhsLong, rhsLong⟩
  · exact derivesShort identity
      (lhsOne.trans rhsOne.symm) (by omega) support parity
  · exact derivesShort identity
      (lhsTwo.trans rhsTwo.symm) (by omega) support parity
  · exact derivesShort identity
      (lhsThree.trans rhsThree.symm) (by omega) support parity
  · exact derivesLong identity lhsLong rhsLong leftGenerated support

private theorem leftFactorModels :
    Models SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.models
      identity member)

private theorem rightFactorModels :
    Models SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.models
      identity member)

/-- Exact source-only unconditional basis endpoint for the mixed generic-CAS
root `S6_2862 = S3_10 x S4_11`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    factorIntersectionComplete).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2862

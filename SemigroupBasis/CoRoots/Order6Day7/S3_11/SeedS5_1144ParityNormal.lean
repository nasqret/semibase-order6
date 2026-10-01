import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144SquaredBand
import SemigroupBasis.CoRoots.S5_441Invariant

/-!
# Unrestricted first-order / last-order / parity normalization

The complete regular-band normal form cannot be replayed unguarded: its
idempotence axiom is false on the S3_11 factor.  Instead normalize TWO whole
copies at each end of a five-copy expansion, and retain the resulting squared
regular-band normal forms as fixed two-sided parity guards.

Every middle-block permutation and parity deletion is transported from the
already completed regular-orthogroup syntactic calculus, never from its
semantics.  No quotient normalizer or rank-2 completeness hypothesis occurs.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank003.basis

private abbrev TargetList (left right : List Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis left right

/-- A parity-neutral, complete regular-band guard. -/
def bandGuard (letters : List Nat) : List Nat :=
  let normal := SemigroupBasis.CoRoots.S5_1092.regularBandNormalList letters
  normal ++ normal

/-- Every original variable is present in each squared regular-band guard. -/
theorem mem_bandGuard_of_mem
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ letters) :
    letter ∈ bandGuard letters := by
  change
    letter ∈
      (SemigroupBasis.Examples.firstOccurrenceSequence letters ++
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence letters) ++
      (SemigroupBasis.Examples.firstOccurrenceSequence letters ++
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence letters)
  apply List.mem_append.mpr
  exact Or.inl <| List.mem_append.mpr <| Or.inr <|
    (SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.mem_lastOccurrenceSequence_iff
      letter letters).mpr member

/-- The guard is uniquely determined by first and last occurrence order. -/
theorem bandGuard_eq_of_occurrenceSequences
    {left right : List Nat}
    (firstEqual :
      SemigroupBasis.Examples.firstOccurrenceSequence left =
        SemigroupBasis.Examples.firstOccurrenceSequence right)
    (lastEqual :
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence left =
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence right) :
    bandGuard left = bandGuard right := by
  simp [bandGuard, SemigroupBasis.CoRoots.S5_1092.regularBandNormalList,
    firstEqual, lastEqual]

/-- The COMPLETE lower-band normalizer lifts only between whole squares. -/
theorem listDerivesBandGuard (source : Word Nat) :
    TargetList
      (source.toList ++ source.toList)
      (bandGuard source.toList) := by
  have lower :=
    SemigroupBasis.CoRoots.S5_1092.listDerivesRegularBandNormal source
  simpa [bandGuard] using liftRegularBandListSquared lower

/-- Squared canonical band guards retain the middle parity residue. -/
def parityBandNormalList (letters : List Nat) : List Nat :=
  bandGuard letters ++ parityReduce letters ++ bandGuard letters

/-- Every unrestricted nonempty word derives to its guarded parity normal
form using a five-copy period-two expansion and two whole-square lifts. -/
theorem listDerivesParityBandNormal (source : Word Nat) :
    TargetList source.toList (parityBandNormalList source.toList) := by
  let letters := source.toList
  let guard := bandGuard letters
  have triple : TargetList letters ((letters ++ letters) ++ letters) :=
    transportRegularOrthogroupList <|
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.listDerivesPowerExpansion
        letters
  have expandFirst :
      TargetList
        ((letters ++ letters) ++ letters)
        (((letters ++ letters) ++ letters) ++ (letters ++ letters)) := by
    simpa [List.append_assoc] using triple.append (letters ++ letters)
  have quintuple :
      TargetList letters
        (((letters ++ letters) ++ letters) ++ (letters ++ letters)) :=
    triple.trans expandFirst
  have square : TargetList (letters ++ letters) guard := by
    simpa [letters, guard] using listDerivesBandGuard source
  have normalizeLeft :
      TargetList
        (((letters ++ letters) ++ letters) ++ (letters ++ letters))
        ((guard ++ letters) ++ (letters ++ letters)) := by
    simpa [List.append_assoc] using
      square.append (letters ++ (letters ++ letters))
  have normalizeRight :
      TargetList
        ((guard ++ letters) ++ (letters ++ letters))
        ((guard ++ letters) ++ guard) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
        (guard ++ letters) square
  have support : ∀ letter, letter ∈ letters → letter ∈ guard := by
    intro letter member
    exact mem_bandGuard_of_mem member
  have normalizeMiddle :
      TargetList
        ((guard ++ letters) ++ guard)
        ((guard ++ parityReduce letters) ++ guard) := by
    simpa [List.append_assoc] using
      transportRegularOrthogroupList <|
        SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.listDerivesParityReduceBetweenGuards
          guard letters guard support support
  have completed :=
    quintuple.trans <| normalizeLeft.trans <|
      normalizeRight.trans normalizeMiddle
  simpa [letters, guard, parityBandNormalList, List.append_assoc] using
    completed

/-- Equal complete regular-band signatures give identical guards; equal
variable parity gives a guarded permutation of their reduced middle blocks. -/
theorem listDerivesEqualParityBandNormals
    (left right : Word Nat)
    (firstEqual :
      SemigroupBasis.Examples.firstOccurrenceSequence left.toList =
        SemigroupBasis.Examples.firstOccurrenceSequence right.toList)
    (lastEqual :
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence left.toList =
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence right.toList)
    (sameParity :
      ∀ letter,
        left.toList.count letter % 2 = right.toList.count letter % 2) :
    TargetList
      (parityBandNormalList left.toList)
      (parityBandNormalList right.toList) := by
  have guardEqual :=
    bandGuard_eq_of_occurrenceSequences firstEqual lastEqual
  have permutation :
      (parityReduce left.toList).Perm (parityReduce right.toList) :=
    parityReduce_perm_of_parity_eq sameParity
  have guarded :
      ∀ letter, letter ∈ parityReduce left.toList →
        letter ∈ bandGuard left.toList := by
    intro letter member
    exact mem_bandGuard_of_mem <|
      SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.source_mem_of_parityReduce_mem
        member
  have orthogroup :=
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.listDerivesTwoSidedGuardedPermutation
      (bandGuard left.toList) (bandGuard left.toList)
      guarded guarded permutation
  have transported := transportRegularOrthogroupList orthogroup
  simpa [parityBandNormalList, guardEqual, List.append_assoc] using
    transported

/-- Genuine unrestricted completeness for exactly first-occurrence order,
last-occurrence order, and per-variable parity. -/
theorem derivesOfBandParitySignature
    (left right : Word Nat)
    (firstEqual :
      SemigroupBasis.Examples.firstOccurrenceSequence left.toList =
        SemigroupBasis.Examples.firstOccurrenceSequence right.toList)
    (lastEqual :
      SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence left.toList =
        SemigroupBasis.CoRoots.S5_1092.lastOccurrenceSequence right.toList)
    (sameParity :
      ∀ letter,
        left.toList.count letter % 2 = right.toList.count letter % 2) :
    Derives targetBasis left right := by
  have leftNormal := listDerivesParityBandNormal left
  have rightNormal := listDerivesParityBandNormal right
  have middle :=
    listDerivesEqualParityBandNormals
      left right firstEqual lastEqual sameParity
  have completed := leftNormal.trans (middle.trans rightNormal.symm)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.toWord completed

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144

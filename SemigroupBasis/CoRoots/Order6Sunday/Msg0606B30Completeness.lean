import SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankNormalization

/-! Exact scanner-count binding and unconditional B30 completeness.
The canonical form consists of the retained squared successor factors,
the sorted global multiple letters with exponents 2 + count mod 2, and
the final simple block. Every normalization step is a B30 derivation. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30Completeness

open SemigroupBasis
open Msg0521RepairedThirtyLawFinite (basis)
open Msg0604B30JointSignature
open Msg0604B30TripledFactors (ListDerives)
open Msg0606B30BankCollection
open Msg0606B30BankNormalization
open S5_402 (terminatedBlockScan terminatedFactorMarkers terminatedBlocks
  sortedTerminatedBlocks sortedTerminatedTail_perm retainedSortedFactors
  renderSquaredTerminatedBlocks terminatedFinalBlock)

private theorem flatMap_congr_on {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have tail := ih (fun y hy => same y (by simp [hy]))
      simp only [List.flatMap_cons, same x (by simp), tail]

theorem scan_marker_count (whole current remaining : List Nat) (tested : Nat) :
    (terminatedFactorMarkers (terminatedBlockScan whole current remaining).1).count tested =
      if whole.count tested = 1 then 0 else remaining.count tested := by
  induction remaining generalizing current with
  | nil => simp [terminatedBlockScan, terminatedFactorMarkers]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simp only [terminatedBlockScan, if_pos simple]
        rw [ih]
        by_cases same : letter = tested
        · subst letter; simp [simple]
        · simp only [List.count_cons_of_ne same]
      · simp only [terminatedBlockScan, if_neg simple]
        change (letter :: terminatedFactorMarkers (terminatedBlockScan whole [] rest).1).count tested = _
        by_cases same : letter = tested
        · subst letter
          simp only [List.count_cons_self]
          rw [ih]
          simp [simple]
        · simp only [List.count_cons_of_ne same]
          exact ih []

theorem sorted_factors_perm (letters : List Nat) :
    (sortedTerminatedBlocks letters).Perm (terminatedBlocks letters) := by
  cases shape : terminatedBlocks letters with
  | nil => simp [sortedTerminatedBlocks, shape]
  | cons first rest =>
      simpa [sortedTerminatedBlocks, shape] using
        List.Perm.cons first (sortedTerminatedTail_perm rest)

theorem sortedFactorLabels_count (letters : List Nat) (tested : Nat) :
    (sortedFactorLabels letters).count tested =
      if letters.count tested = 1 then 0 else letters.count tested := by
  have permutation := (sorted_factors_perm letters).map (fun f : List Nat × Nat => f.2)
  have count := (List.perm_iff_count.mp permutation) tested
  change (sortedFactorLabels letters).count tested =
    (terminatedFactorMarkers (terminatedBlocks letters)).count tested at count
  exact count.trans (by
    simpa [terminatedBlocks] using scan_marker_count letters [] letters tested)

theorem multiple_keys_support (letters : List Nat) (x : Nat) :
    x ∈ S5_107.sortedMultipleLetters letters ↔ x ∈ sortedFactorLabels letters := by
  rw [S5_107.sortedMultipleLetters_mem_iff, ← List.count_pos_iff, sortedFactorLabels_count]
  by_cases simple : letters.count x = 1
  · simp [simple]
  · simp only [if_neg simple]
    omega

theorem multiple_keys_nodup (letters : List Nat) :
    (S5_107.sortedMultipleLetters letters).Nodup := by
  unfold S5_107.sortedMultipleLetters
  exact (List.mergeSort_perm
    ((S5_107.distinctLetters letters).filter (fun x => decide (2 ≤ letters.count x)))
    (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr
      ((S5_107.distinctLetters_nodup letters).filter (fun x => decide (2 ≤ letters.count x)))

def canonicalBank (letters : List Nat) : List Nat :=
  (S5_107.sortedMultipleLetters letters).flatMap
    fun x => List.replicate (2 + letters.count x % 2) x

theorem parityBank_eq_canonicalBank (letters : List Nat) :
    parityBank (S5_107.sortedMultipleLetters letters) (sortedFactorLabels letters) =
      canonicalBank letters := by
  unfold parityBank canonicalBank
  apply flatMap_congr_on
  intro x member
  have multiple := (S5_107.sortedMultipleLetters_mem_iff x letters).mp member
  have notSimple : letters.count x ≠ 1 := by omega
  rw [sortedFactorLabels_count, if_neg notSimple]

def canonicalList (letters : List Nat) : List Nat :=
  renderSquaredTerminatedBlocks (retainedSortedFactors letters) ++
    canonicalBank letters ++ terminatedFinalBlock letters

theorem listDerivesCanonical (letters : List Nat) :
    ListDerives letters (canonicalList letters) := by
  have collected := listDerivesSquaredPrefixCubicBank letters
  cases shape : sortedTerminatedBlocks letters with
  | nil =>
      have labelsEmpty : sortedFactorLabels letters = [] := by
        simp [sortedFactorLabels, shape, terminatedFactorMarkers]
      have keysEmpty : S5_107.sortedMultipleLetters letters = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x member
        have impossible := (multiple_keys_support letters x).mp member
        simp [labelsEmpty] at impossible
      simpa [canonicalList, canonicalBank, keysEmpty, labelsEmpty] using collected
  | cons first rest =>
      have normalized := listDerivesNormalizeCubicBank first (S5_402.blockBearingFactors rest)
        (S5_107.sortedMultipleLetters letters) (sortedFactorLabels letters)
        (terminatedFinalBlock letters) (multiple_keys_nodup letters)
        (multiple_keys_support letters)
      rw [parityBank_eq_canonicalBank] at normalized
      have normalized' : ListDerives
          (renderSquaredTerminatedBlocks (retainedSortedFactors letters) ++
            renderCubeBank (sortedFactorLabels letters) ++ terminatedFinalBlock letters)
          (canonicalList letters) := by
        simpa [canonicalList, retainedSortedFactors, shape] using normalized
      exact collected.trans normalized'

theorem canonicalBank_eq_of_signature {left right : Word Nat} (same : JointSignature left right) :
    canonicalBank left.toList = canonicalBank right.toList := by
  unfold canonicalBank
  rw [S5_402.sortedMultipleLetters_eq_of_sameSignature same.quotient]
  apply flatMap_congr_on
  intro x _
  rw [same.parity x]

theorem canonicalList_eq_of_signature {left right : Word Nat} (same : JointSignature left right) :
    canonicalList left.toList = canonicalList right.toList := by
  unfold canonicalList
  rw [S5_402.retainedSortedFactors_eq_of_sameSignature same.quotient,
    canonicalBank_eq_of_signature same,
    S5_402.terminatedFinalBlock_eq_of_sameSignature same.quotient]

/-- Unrestricted signature-to-B30 derivability. -/
theorem derivesOfJointSignature (left right : Word Nat) (same : JointSignature left right) :
    Derives basis left right := by
  have leftDerivation := listDerivesCanonical left.toList
  have rightDerivation := listDerivesCanonical right.toList
  rw [← canonicalList_eq_of_signature same] at rightDerivation
  have paired := leftDerivation.trans rightDerivation.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord paired

theorem S6_4091.representative_basis :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup basis :=
  S6_4091_basisFor_iff_signature_derivable.mpr derivesOfJointSignature

theorem S6_4091.opposite_basis :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4091.table.semigroup.opposite (reversedBasis basis) :=
  S6_4091.representative_basis.oppositeReversed

theorem S6_4297.representative_basis :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup basis :=
  S6_4297_basisFor_iff_signature_derivable.mpr derivesOfJointSignature

theorem S6_4297.opposite_basis :
    BasisFor Msg0521RepairedThirtyLawFinite.S6_4297.table.semigroup.opposite (reversedBasis basis) :=
  S6_4297.representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30Completeness

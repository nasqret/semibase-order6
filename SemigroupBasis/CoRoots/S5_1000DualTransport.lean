import SemigroupBasis.CoRoots.S5_1000Invariant
import SemigroupBasis.CoRoots.S5_1155Completeness

namespace SemigroupBasis.CoRoots.S5_1000

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Reversal of the exact semantic signature -/

private theorem reverse_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).reverse =
      Word.mk final stem.reverse := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_wordOfPrefixFinal]
  simp [Word.toList]

private theorem reverse_eq_splitPrefixFinal (word : Word Nat) :
    word.reverse =
      Word.mk (splitPrefixFinal word).2
        (splitPrefixFinal word).1.reverse :=
  (congrArg Word.reverse
      (wordOfPrefixFinal_split word).symm).trans
    (reverse_wordOfPrefixFinal
      (splitPrefixFinal word).1
      (splitPrefixFinal word).2)

private theorem simpleInitialMarker_reverse (word : Word Nat) :
    S5_1155.simpleInitialMarker word.reverse =
      if (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 then
        none
      else
        some (splitPrefixFinal word).2 := by
  rw [reverse_eq_splitPrefixFinal]
  by_cases member :
      (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1
  · have countNonzero :
        (splitPrefixFinal word).1.count
            (splitPrefixFinal word).2 ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr member)
    simp [S5_1155.simpleInitialMarker, Word.toList,
      member, countNonzero]
  · have countZero :
        (splitPrefixFinal word).1.reverse.count
          (splitPrefixFinal word).2 = 0 := by
      rw [List.count_reverse]
      exact List.count_eq_zero.mpr member
    have countOne :
        ((splitPrefixFinal word).2 ::
            (splitPrefixFinal word).1.reverse).count
            (splitPrefixFinal word).2 = 1 := by
      simp [countZero]
    simp [S5_1155.simpleInitialMarker, Word.toList,
      member, countOne]

private theorem simpleInitialMarker_reverse_eq_of_sameSimpleFinal
    {left right : Word Nat}
    (same : S5_196.SameSimpleFinal left right) :
    S5_1155.simpleInitialMarker left.reverse =
      S5_1155.simpleInitialMarker right.reverse := by
  rw [simpleInitialMarker_reverse, simpleInitialMarker_reverse]
  by_cases leftMember :
      (splitPrefixFinal left).2 ∈ (splitPrefixFinal left).1
  · have rightMember :
        (splitPrefixFinal right).2 ∈
          (splitPrefixFinal right).1 := by
      apply Decidable.byContradiction
      intro rightAbsent
      have rightSimple :
          S5_196.SimpleFinal right (splitPrefixFinal right).2 :=
        ⟨rfl, rightAbsent⟩
      have leftSimple :
          S5_196.SimpleFinal left (splitPrefixFinal right).2 :=
        (same (splitPrefixFinal right).2).mpr rightSimple
      have finals :
          (splitPrefixFinal left).2 =
            (splitPrefixFinal right).2 :=
        leftSimple.1
      exact leftSimple.2 (by simpa [finals] using leftMember)
    simp [leftMember, rightMember]
  · have leftSimple :
        S5_196.SimpleFinal left (splitPrefixFinal left).2 :=
      ⟨rfl, leftMember⟩
    have rightSimple :
        S5_196.SimpleFinal right (splitPrefixFinal left).2 :=
      (same (splitPrefixFinal left).2).mp leftSimple
    have finals :
        (splitPrefixFinal right).2 =
          (splitPrefixFinal left).2 :=
      rightSimple.1
    have rightAbsent :
        (splitPrefixFinal right).2 ∉
          (splitPrefixFinal right).1 := by
      rw [finals]
      exact rightSimple.2
    have rightAbsentCommon :
        (splitPrefixFinal left).2 ∉
          (splitPrefixFinal right).1 := by
      rw [← finals]
      exact rightAbsent
    simp [leftMember, rightAbsentCommon, finals]

/-- Reversing an `S5_1000` signature turns its unique-final marker into
the `S5_1155` simple-initial marker while preserving support and all
multiplicity residues. -/
theorem sameSignature_reversed
    {left right : Word Nat}
    (same : S5_1000Invariant.SameSignature left right) :
    S5_1155.SameSemanticSignature
      left.reverse right.reverse := by
  refine S5_1155.SameSemanticSignature.mk ?_ ?_ ?_
  · intro letter
    simpa only [Word.toList_reverse, List.mem_reverse] using
      same.support letter
  · intro letter
    simpa only [Word.toList_reverse, List.count_reverse] using
      same.positiveMultiplicityModThree letter
  · exact simpleInitialMarker_reverse_eq_of_sameSimpleFinal
      same.uniqueFinal

/-! ## Transport of the dual comparison presentation -/

private def yx : Word Nat := ⟨1, [0]⟩
private def yxxxx : Word Nat := ⟨1, [0, 0, 0, 0]⟩
private def zyx : Word Nat := ⟨2, [1, 0]⟩
private def zxy : Word Nat := ⟨2, [0, 1]⟩
private def yyxxx : Word Nat := ⟨1, [1, 0, 0, 0]⟩
private def xyyxx : Word Nat := ⟨0, [1, 1, 0, 0]⟩

private def reversedPrefixExpansionLaw : Identity Nat :=
  ⟨yx, yxxxx⟩

private def reversedPrefixSwapLaw : Identity Nat :=
  ⟨zyx, zxy⟩

private def reversedFinalMoveLaw : Identity Nat :=
  ⟨yyxxx, xyyxx⟩

private def expectedReversedBasis : List (Identity Nat) :=
  [S5_1155.powerLaw, reversedPrefixExpansionLaw,
    reversedPrefixSwapLaw, reversedFinalMoveLaw]

private theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  decide

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem reversedPowerLawDerives :
    Derives (reversedBasis basis)
      S5_1155.powerLaw.lhs S5_1155.powerLaw.rhs := by
  apply Derives.fromBasis (e := S5_1155.powerLaw)
  rw [reversedBasis_eq_expected]
  simp [expectedReversedBasis]

private theorem reversedPrefixExpansionLawDerives :
    Derives (reversedBasis basis)
      reversedPrefixExpansionLaw.lhs
      reversedPrefixExpansionLaw.rhs := by
  apply Derives.fromBasis (e := reversedPrefixExpansionLaw)
  rw [reversedBasis_eq_expected]
  simp [expectedReversedBasis]

private theorem reversedPrefixSwapLawDerives :
    Derives (reversedBasis basis)
      reversedPrefixSwapLaw.lhs reversedPrefixSwapLaw.rhs := by
  apply Derives.fromBasis (e := reversedPrefixSwapLaw)
  rw [reversedBasis_eq_expected]
  simp [expectedReversedBasis]

private theorem reversedFinalMoveLawDerives :
    Derives (reversedBasis basis)
      reversedFinalMoveLaw.lhs reversedFinalMoveLaw.rhs := by
  apply Derives.fromBasis (e := reversedFinalMoveLaw)
  rw [reversedBasis_eq_expected]
  simp [expectedReversedBasis]

private theorem dualTailExpansionLawDerives :
    Derives (reversedBasis basis)
      S5_1155.tailExpansionLaw.lhs
      S5_1155.tailExpansionLaw.rhs := by
  let substitution := instantiateThreeWords
    (Word.singleton 1) (Word.singleton 0) (Word.singleton 2)
  have derived :=
    Derives.subst reversedPrefixExpansionLawDerives substitution
  have leftEndpoint :
      reversedPrefixExpansionLaw.lhs.bind substitution =
        S5_1155.tailExpansionLaw.lhs := by
    decide
  have rightEndpoint :
      reversedPrefixExpansionLaw.rhs.bind substitution =
        S5_1155.tailExpansionLaw.rhs := by
    decide
  rw [leftEndpoint, rightEndpoint] at derived
  exact derived

private theorem dualSuffixSwapLawDerives :
    Derives (reversedBasis basis)
      S5_1155.suffixSwapLaw.lhs
      S5_1155.suffixSwapLaw.rhs := by
  let substitution := instantiateThreeWords
    (Word.singleton 2) (Word.singleton 1) (Word.singleton 0)
  have derived :=
    Derives.subst reversedPrefixSwapLawDerives substitution
  have leftEndpoint :
      reversedPrefixSwapLaw.lhs.bind substitution =
        S5_1155.suffixSwapLaw.lhs := by
    decide
  have rightEndpoint :
      reversedPrefixSwapLaw.rhs.bind substitution =
        S5_1155.suffixSwapLaw.rhs := by
    decide
  rw [leftEndpoint, rightEndpoint] at derived
  exact derived

private theorem dualMovementLawDerives :
    Derives (reversedBasis basis)
      S5_1155.dualMovementLaw.lhs
      S5_1155.dualMovementLaw.rhs := by
  let substitution := instantiateThreeWords
    (Word.singleton 1) (Word.singleton 0) (Word.singleton 2)
  have derived :=
    Derives.subst reversedFinalMoveLawDerives substitution
  have leftEndpoint :
      reversedFinalMoveLaw.lhs.bind substitution =
        S5_1155.dualMovementLaw.lhs := by
    decide
  have rightEndpoint :
      reversedFinalMoveLaw.rhs.bind substitution =
        S5_1155.dualMovementLaw.rhs := by
    decide
  rw [leftEndpoint, rightEndpoint] at derived
  exact derived

/-- Every `S5_1155` dual-comparison law follows from the reversed
`S5_1000` basis by one of the explicit variable substitutions above. -/
theorem dualComparisonAxiomDerivesFromReversedBasis
    (identity : Identity Nat)
    (member : identity ∈ S5_1155.dualComparisonBasis) :
    Derives (reversedBasis basis) identity.lhs identity.rhs := by
  simp only [S5_1155.dualComparisonBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact reversedPowerLawDerives
  · exact dualTailExpansionLawDerives
  · exact dualMovementLawDerives
  · exact dualSuffixSwapLawDerives

/-- Transport a derivation in the `S5_1155` dual comparison system to
the reversed `S5_1000` presentation. -/
theorem transportDualComparisonDerivation
    {left right : Word Nat}
    (derivation :
      Derives S5_1155.dualComparisonBasis left right) :
    Derives (reversedBasis basis) left right :=
  derivation.transport dualComparisonAxiomDerivesFromReversedBasis

/-! ## Derivational completeness -/

/-- The four-law `S5_1000` basis derives every pair of words with the
exact support, modulo-three multiplicity, and unique-final signature. -/
theorem derivesOfSameSignature
    {left right : Word Nat}
    (same : S5_1000Invariant.SameSignature left right) :
    Derives basis left right := by
  have semantic :
      S5_1155.SameSemanticSignature left.reverse right.reverse :=
    sameSignature_reversed same
  have canonical :
      Derives S5_1155.basis left.reverse right.reverse :=
    S5_1155.canonicalCompleteness.derive
      left.reverse right.reverse semantic
  have comparison :
      Derives S5_1155.dualComparisonBasis
        left.reverse right.reverse :=
    S5_1155.derivesInDualComparison canonical
  have transported :
      Derives (reversedBasis basis) left.reverse right.reverse :=
    transportDualComparisonDerivation comparison
  simpa using transported.reverse

end SemigroupBasis.CoRoots.S5_1000

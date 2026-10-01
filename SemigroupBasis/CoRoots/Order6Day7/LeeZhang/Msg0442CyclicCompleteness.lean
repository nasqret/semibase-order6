import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicSemantics

/-! Unrestricted completeness of the exact msg0442 three-law pair system.
The cyclic factor separates lengths 1,2,3,>=4. All four strata have actual
derivations. Only then are the C1 normalizer and literal endpoints formed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

open SemigroupBasis Examples

theorem oneWordShape (word : Word Nat) (length : word.toList.length = 1) :
    ∃ a, word = Word.singleton a := by
  rcases word with ⟨a, tail⟩
  rcases tail with _ | ⟨b, rest⟩
  · exact ⟨a, rfl⟩
  · simp [Word.toList] at length

theorem twoWordShape (word : Word Nat) (length : word.toList.length = 2) :
    ∃ a b, word = Word.mk a [b] := by
  rcases word with ⟨a, tail⟩
  rcases tail with _ | ⟨b, rest⟩
  · simp [Word.toList] at length
  rcases rest with _ | ⟨c, remaining⟩
  · exact ⟨a, b, rfl⟩
  · simp [Word.toList] at length

theorem threeWordShape (word : Word Nat) (length : word.toList.length = 3) :
    ∃ a b c, word = Word.mk a [b, c] := by
  rcases word with ⟨a, tail⟩
  rcases tail with _ | ⟨b, rest⟩
  · simp [Word.toList] at length
  rcases rest with _ | ⟨c, remaining⟩
  · simp [Word.toList] at length
  rcases remaining with _ | ⟨d, suffix⟩
  · exact ⟨a, b, c, rfl⟩
  · simp [Word.toList] at length

/-- ALL Identity Nat and every finite support; there is no bounded premise. -/
theorem pair_complete (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := by
  have catalogueValid : identity.SatisfiedBy Generated.Catalogue.S4_11.table.semigroup := by
    rw [← Generated.S4_11.table_eq_canonical_catalogue]
    exact cyclicValid
  have strata := Order6GenericCASSubdirectS4_11Family.lengthShape identity catalogueValid
  rcases identity with ⟨left, right⟩
  rcases strata with ⟨leftOne, rightOne⟩ | ⟨leftTwo, rightTwo⟩ |
    ⟨leftThree, rightThree⟩ | ⟨leftLong, rightLong⟩
  · rcases oneWordShape left leftOne with ⟨a, rfl⟩
    rcases oneWordShape right rightOne with ⟨b, rfl⟩
    exact oneComplete a b markerValid
  · rcases twoWordShape left leftTwo with ⟨a, b, rfl⟩
    rcases twoWordShape right rightTwo with ⟨c, d, rfl⟩
    exact twoComplete a b c d markerValid
  · rcases threeWordShape left leftThree with ⟨a, b, c, rfl⟩
    rcases threeWordShape right rightThree with ⟨d, e, f, rfl⟩
    exact threeComplete a b c d e f markerValid
  · exact longComplete ⟨left, right⟩ markerValid leftLong rightLong

def pairIntersection : IntersectionBasis markerTable.semigroup cyclicTable.semigroup pairBasis where
  leftModels := pairMarkerModels
  rightModels := pairCyclicModels
  complete := pair_complete

noncomputable def pairQuotientNormalizer : IntersectionNormalizer markerTable.semigroup cyclicTable.semigroup pairBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer pairIntersection

noncomputable def pairNormalizer : IntersectionNormalizer markerTable.semigroup cyclicTable.semigroup pairBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer pairQuotientNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) (fun _ valid => valid)

def pairOppositeIntersection :
    IntersectionBasis markerTable.semigroup.opposite cyclicTable.semigroup.opposite (reversedBasis pairBasis) :=
  pairIntersection.oppositeReversed

noncomputable def pairOppositeNormalizer :
    IntersectionNormalizer markerTable.semigroup.opposite cyclicTable.semigroup.opposite (reversedBasis pairBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer pairOppositeIntersection

theorem pair2797_representative_basis : BasisFor table2797.semigroup pairBasis :=
  pairNormalizer.basisFor pairMarkerModels pairCyclicModels subdirect2797
theorem pair2798_representative_basis : BasisFor table2798.semigroup pairBasis :=
  pairNormalizer.basisFor pairMarkerModels pairCyclicModels subdirect2798
theorem pair2797_opposite_basis : BasisFor table2797.semigroup.opposite (reversedBasis pairBasis) :=
  pair2797_representative_basis.oppositeReversed
theorem pair2798_opposite_basis : BasisFor table2798.semigroup.opposite (reversedBasis pairBasis) :=
  pair2798_representative_basis.oppositeReversed

theorem pair2797_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2797.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := pair2797_representative_basis.2 identity valid
theorem pair2798_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2798.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := pair2798_representative_basis.2 identity valid
theorem pair2797_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2797.semigroup.opposite) :
    Derives (reversedBasis pairBasis) identity.lhs identity.rhs := pair2797_opposite_basis.2 identity valid
theorem pair2798_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2798.semigroup.opposite) :
    Derives (reversedBasis pairBasis) identity.lhs identity.rhs := pair2798_opposite_basis.2 identity valid

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

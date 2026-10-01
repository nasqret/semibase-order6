import SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12.Macros
import SemigroupBasis.Subdirect

/-!
# L3 light root `S3_15 / S4_12`: completeness

The factor `S4_12` separates literal commutative words of lengths one and two
from the long exponent-parity regime.  The factor `S3_15` restores the head
and full support.  The frozen marker replay in `Macros` derives the resulting
long-word classifier.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12

open SemigroupBasis
open SemigroupBasis.Examples

private theorem s3_15_valid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftNormalBandFifteen.semigroup at valid
  exact leftNormalBandFifteenValid_head_eq identity valid

private theorem s3_15_valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  change identity.SatisfiedBy leftNormalBandFifteen.semigroup at valid
  exact leftNormalBandFifteenValid_support_eq identity valid

private theorem s4_12_valid_class
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_12.table.semigroup) :
    (identity.lhs.toList.length = 1 ∧
        identity.rhs.toList.length = 1 ∧
        identity.lhs.toList.Perm identity.rhs.toList) ∨
      (identity.lhs.toList.length = 2 ∧
        identity.rhs.toList.length = 2 ∧
        identity.lhs.toList.Perm identity.rhs.toList) ∨
      (3 ≤ identity.lhs.toList.length ∧
        3 ≤ identity.rhs.toList.length ∧
        ∀ z, identity.lhs.toList.count z % 2 =
          identity.rhs.toList.count z % 2) := by
  have derivation :=
    SemigroupBasis.Generated.S4_12.representative_basis.2
      identity valid
  have cyclicValid :
      identity.SatisfiedBy cyclicThreeTwo.semigroup :=
    derivation.sound cyclicThreeTwoBasis_models
  exact cyclicThreeTwoValid_class identity cyclicValid

private theorem words_equal_of_length_one
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (heads : u.head = v.head) :
    u = v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          have uTailZero : uTail.length = 0 := by
            simpa [Word.toList] using uOne
          have vTailZero : vTail.length = 0 := by
            simpa [Word.toList] using vOne
          have uTailNil := List.eq_nil_of_length_eq_zero uTailZero
          have vTailNil := List.eq_nil_of_length_eq_zero vTailZero
          subst uTail
          subst vTail
          simpa using heads

private theorem words_equal_of_length_two
    (u v : Word Nat)
    (uTwo : u.toList.length = 2)
    (vTwo : v.toList.length = 2)
    (heads : u.head = v.head)
    (permutation : u.toList.Perm v.toList) :
    u = v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          have uTailOne : uTail.length = 1 := by
            simpa [Word.toList] using uTwo
          have vTailOne : vTail.length = 1 := by
            simpa [Word.toList] using vTwo
          obtain ⟨uLast, rfl⟩ := List.length_eq_one_iff.mp uTailOne
          obtain ⟨vLast, rfl⟩ := List.length_eq_one_iff.mp vTailOne
          simp only at heads
          subst vHead
          by_cases sameLast : vLast = uLast
          · subst vLast
            rfl
          · have countEq :=
              List.perm_iff_count.mp permutation uLast
            by_cases lastIsHead : uLast = uHead
            · subst uLast
              simp [Word.toList, sameLast] at countEq
            · have differentHead : uHead ≠ uLast :=
                Ne.symm lastIsHead
              simp [Word.toList, differentHead,
                sameLast] at countEq

theorem derives_of_s3_15_s4_12_valid
    (identity : Identity Nat)
    (headSupportValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup)
    (shortParityValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_12.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := s3_15_valid_head identity headSupportValid
  rcases s4_12_valid_class identity shortParityValid with
    lengthOne | lengthTwo | long
  · rw [words_equal_of_length_one identity.lhs identity.rhs
      lengthOne.1 lengthOne.2.1 heads]
    exact Derives.refl _
  · rw [words_equal_of_length_two identity.lhs identity.rhs
      lengthTwo.1 lengthTwo.2.1 heads lengthTwo.2.2]
    exact Derives.refl _
  · exact derivesLongHeadSupportParity identity.lhs identity.rhs
      long.1 long.2.1 heads
      (s3_15_valid_support identity headSupportValid)
      long.2.2

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_12.table.semigroup basis where
  leftModels := basis_s3_15_models
  rightModels := basis_s4_12_models
  complete := derives_of_s3_15_s4_12_valid

end SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12

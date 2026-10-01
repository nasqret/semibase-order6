import SemigroupBasis.CoRoots.Order6SporadicSection17C5InputGapData

/-! The new four/five-letter screen examples are raw13 consequences.
The exact nonzero gap counts remain bounded screening data, not refutations
of unrestricted completeness. No finite screen is a premise of these proofs. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem allUnrestricted_compare_checked (left right : List Nat)
    (leftMask : left.all (unrestrictedMask left) = true)
    (rightMask : right.all (unrestrictedMask right) = true)
    (intoRight : left.all (fun x => decide (x ∈ right)) = true)
    (intoLeft : right.all (fun x => decide (x ∈ left)) = true) :
    ListDerives left right := by
  apply allUnrestricted_compare
  · exact allUnrestricted_of_mask left leftMask
  · exact allUnrestricted_of_mask right rightMask
  · intro x
    constructor
    · intro member
      exact of_decide_eq_true ((List.all_eq_true.mp intoRight) x member)
    · intro member
      exact of_decide_eq_true ((List.all_eq_true.mp intoLeft) x member)

theorem screenWitness_xyxy_yxyx : ListDerives [0,1,0,1] [1,0,1,0] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xzxz_zxzx : ListDerives [0,2,0,2] [2,0,2,0] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xtxt_txtx : ListDerives [0,3,0,3] [3,0,3,0] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xuxu_uxux : ListDerives [0,4,0,4] [4,0,4,0] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xyxy_xyxyx : ListDerives [0,1,0,1] [0,1,0,1,0] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xyxy_yxyxy : ListDerives [0,1,0,1] [1,0,1,0,1] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

theorem screenWitness_xyxy_xyxyxy : ListDerives [0,1,0,1] [0,1,0,1,0,1] :=
  allUnrestricted_compare_checked _ _ (by decide) (by decide) (by decide) (by decide)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.allUnrestricted_compare_checked
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_yxyx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xzxz_zxzx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xtxt_txtx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xuxu_uxux
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_xyxyx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_yxyxy
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_xyxyxy

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

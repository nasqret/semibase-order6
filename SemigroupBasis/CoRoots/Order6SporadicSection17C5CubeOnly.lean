import SemigroupBasis.CoRoots.Order6SporadicSection17C5BodyNormalization

/-! The complete all-unrestricted-letter subcase, and exact derivations of
the first four gaps reported by the MAX8 letter-instance screen. A bounded
gap is not a proof that the raw basis cannot derive the displayed identity. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem allUnrestricted_of_mask (letters : List Nat)
    (checked : letters.all (unrestrictedMask letters) = true) :
    ∀ x ∈ letters, Unrestricted x letters := by
  intro x member
  exact (unrestrictedMask_true letters x).mp ((List.all_eq_true.mp checked) x member)

theorem cubeTile_flatMap_allUnrestricted (original remaining : List Nat)
    (all : ∀ x ∈ remaining, Unrestricted x original) :
    remaining.flatMap (cubeTile (unrestrictedMarkers original)) = cubeBody remaining := by
  induction remaining with
  | nil => rfl
  | cons x xs ih =>
      have head := all x List.mem_cons_self
      have tail : ∀ y ∈ xs, Unrestricted y original :=
        fun y member => all y (List.mem_cons_of_mem x member)
      change cubeTile (unrestrictedMarkers original) x ++
        xs.flatMap (cubeTile (unrestrictedMarkers original)) = [x,x,x] ++ cubeBody xs
      rw [cubeTile_unrestricted original x head,ih tail]

theorem allUnrestricted_derives_cubeBody (letters : List Nat)
    (all : ∀ x ∈ letters, Unrestricted x letters) :
    ListDerives letters (cubeBody letters) := by
  have shape : cubicForm letters = cubeBody letters :=
    cubeTile_flatMap_allUnrestricted letters letters all
  have derivation := cubicForm_derives letters
  rw [shape] at derivation
  exact derivation

theorem allUnrestricted_compare {left right : List Nat}
    (leftAll : ∀ x ∈ left, Unrestricted x left)
    (rightAll : ∀ x ∈ right, Unrestricted x right)
    (content : ∀ x, x ∈ left ↔ x ∈ right) :
    ListDerives left right :=
  (allUnrestricted_derives_cubeBody left leftAll).trans
    ((cubeBody_sameContent content).trans (allUnrestricted_derives_cubeBody right rightAll).symm)

theorem Semantics.SameEval.allUnrestricted_derives {which : Bool} {left right : List Nat}
    (same : Semantics.SameEval which left right)
    (all : ∀ x ∈ left, Unrestricted x left) : ListDerives left right := by
  have rightAll : ∀ x ∈ right, Unrestricted x right := by
    intro x member
    exact (same.unrestricted x).mp (all x ((same.mem x).mpr member))
  exact allUnrestricted_compare all rightAll (fun x => same.mem x)

theorem screenWitness_xyxy_xyyyx : ListDerives [0,1,0,1] [0,1,1,1,0] := by
  apply allUnrestricted_compare
  · exact allUnrestricted_of_mask _ (by decide)
  · exact allUnrestricted_of_mask _ (by decide)
  · intro x
    simp [or_assoc,or_left_comm,or_comm]

theorem screenWitness_xyxy_yxxxy : ListDerives [0,1,0,1] [1,0,0,0,1] := by
  apply allUnrestricted_compare
  · exact allUnrestricted_of_mask _ (by decide)
  · exact allUnrestricted_of_mask _ (by decide)
  · intro x
    simp [or_assoc,or_left_comm,or_comm]

theorem screenWitness_xyxy_xyyyyx : ListDerives [0,1,0,1] [0,1,1,1,1,0] := by
  apply allUnrestricted_compare
  · exact allUnrestricted_of_mask _ (by decide)
  · exact allUnrestricted_of_mask _ (by decide)
  · intro x
    simp [or_assoc,or_left_comm,or_comm]

theorem screenWitness_xyxy_yxxxxy : ListDerives [0,1,0,1] [1,0,0,0,0,1] := by
  apply allUnrestricted_compare
  · exact allUnrestricted_of_mask _ (by decide)
  · exact allUnrestricted_of_mask _ (by decide)
  · intro x
    simp [or_assoc,or_left_comm,or_comm]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.allUnrestricted_of_mask
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeTile_flatMap_allUnrestricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.allUnrestricted_derives_cubeBody
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.allUnrestricted_compare
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.allUnrestricted_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_xyyyx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_yxxxy
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_xyyyyx
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.screenWitness_xyxy_yxxxxy

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

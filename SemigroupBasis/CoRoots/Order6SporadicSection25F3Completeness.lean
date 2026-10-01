import SemigroupBasis.CoRoots.Order6SporadicSection25F3SeparatorBase
import SemigroupBasis.CoRoots.Order6SporadicSection25F3CutRestriction

/-! The unrestricted Section25 Prop25.5 converse. Induction is on the
actual left word length, splitting only at a proved B0 exact separator.
No bounded alphabet, window, normalizer field or comparison is a premise. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
open SemigroupBasis

theorem derives_by_length (size : Nat) :
    ∀ left right : Word Nat, left.toList.length = size →
      (⟨left,right⟩ : Identity Nat).SatisfiedBy semigroup →
      (⟨left,right⟩ : Identity Nat).SatisfiedBy
        Generated.Catalogue.S4_96.table.semigroup.opposite →
      Derives (basis true) left right := by
  induction size using Nat.strongRecOn with
  | ind size smaller =>
      intro left right lengthEqual separatorValid affineValid
      classical
      by_cases noSeparator : NoExactSeparator left.toList
      · exact separatorFree_compare ⟨left,right⟩ separatorValid affineValid noSeparator
      · have existsCut : ∃ front separator back,
            Examples.UniqueSeparatorFourExactCut left.toList front separator back := by
          apply Classical.byContradiction
          intro absent
          apply noSeparator
          intro front separator back cut
          exact absent ⟨front, separator, back, cut⟩
        rcases existsCut with ⟨leftFront, separator, leftBack, leftCut⟩
        rcases Examples.uniqueSeparatorFourEqualEval_transportExactCut
            left right separatorValid leftCut with
          ⟨rightFront, rightBack, rightCut, frontSupport, backSupport⟩
        have frontDerives : ListDerives true leftFront rightFront := by
          rcases leftFront with _ | ⟨first, rest⟩
          · have rightEmpty : rightFront = [] := by
              rcases rightFront with _ | ⟨other, remaining⟩
              · rfl
              · have impossible : other ∈ ([] : List Nat) :=
                  (frontSupport other).mp (List.Mem.head _)
                exact False.elim (List.not_mem_nil impossible)
            rw [rightEmpty]
            exact S5_107.ListDerives.refl []
          · rcases rightFront with _ | ⟨other, remaining⟩
            · have impossible : first ∈ ([] : List Nat) :=
                (frontSupport first).mpr (List.Mem.head _)
              exact False.elim (List.not_mem_nil impossible)
            · have factors := exactCut_prefix_factors ⟨left,right⟩
                ⟨first,rest⟩ ⟨other,remaining⟩ leftBack rightBack separator
                leftCut rightCut (fun letter => (frontSupport letter).symm)
                separatorValid affineValid
              have shorter : (⟨first,rest⟩ : Word Nat).toList.length < size := by
                change (first :: rest).length < size
                rw [← lengthEqual, leftCut.1]
                simp only [List.length_append, List.length_cons]
                omega
              have recursive : Derives (basis true) (⟨first,rest⟩ : Word Nat) ⟨other,remaining⟩ :=
                smaller _ shorter _ _ rfl factors.1 factors.2
              exact S5_107.ListDerives.ofWord recursive
        have backDerives : ListDerives true leftBack rightBack := by
          rcases leftBack with _ | ⟨first, rest⟩
          · have rightEmpty : rightBack = [] := by
              rcases rightBack with _ | ⟨other, remaining⟩
              · rfl
              · have impossible : other ∈ ([] : List Nat) :=
                  (backSupport other).mp (List.Mem.head _)
                exact False.elim (List.not_mem_nil impossible)
            rw [rightEmpty]
            exact S5_107.ListDerives.refl []
          · rcases rightBack with _ | ⟨other, remaining⟩
            · have impossible : first ∈ ([] : List Nat) :=
                (backSupport first).mpr (List.Mem.head _)
              exact False.elim (List.not_mem_nil impossible)
            · have factors := exactCut_suffix_factors ⟨left,right⟩
                leftFront rightFront ⟨first,rest⟩ ⟨other,remaining⟩ separator
                leftCut rightCut (fun letter => (backSupport letter).symm)
                separatorValid affineValid
              have shorter : (⟨first,rest⟩ : Word Nat).toList.length < size := by
                change (first :: rest).length < size
                rw [← lengthEqual, leftCut.1]
                simp only [List.length_append, List.length_cons]
                omega
              have recursive : Derives (basis true) (⟨first,rest⟩ : Word Nat) ⟨other,remaining⟩ :=
                smaller _ shorter _ _ rfl factors.1 factors.2
              exact S5_107.ListDerives.ofWord recursive
        have leftStep : ListDerives true left.toList (rightFront ++ separator :: leftBack) := by
          rw [leftCut.1]
          exact frontDerives.append (separator :: leftBack)
        have rightStep : ListDerives true (rightFront ++ separator :: leftBack) right.toList := by
          rw [rightCut.1]
          simpa only [List.append_assoc, List.singleton_append] using
            backDerives.prepend (rightFront ++ [separator])
        exact S5_107.ListDerives.toWord (leftStep.trans rightStep)

theorem derives_of_library_factors (identity : Identity Nat)
    (separatorValid : identity.SatisfiedBy semigroup)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite) :
    Derives (basis true) identity.lhs identity.rhs :=
  derives_by_length identity.lhs.toList.length identity.lhs identity.rhs rfl separatorValid affineValid

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.derives_by_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.derives_of_library_factors

end SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

private theorem semigroup_eq_of_mul_eq {S : Type} (first second : Semigroup S)
    (same : first.mul = second.mul) : first = second := by
  cases first
  cases second
  cases same
  rfl

theorem F3_separator_semigroup_eq_actual :
    F3Separator.semigroup = Generated.Catalogue.S4_69.table.semigroup := by
  apply semigroup_eq_of_mul_eq
  funext first second
  decide +revert

theorem F3_derives_of_actual_factors (identity : Identity Nat)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (separatorValid : identity.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup) :
    Derives (basis true) identity.lhs identity.rhs := by
  have libraryValid : identity.SatisfiedBy F3Separator.semigroup := by
    rw [F3_separator_semigroup_eq_actual]
    exact separatorValid
  exact F3Separator.derives_of_library_factors identity libraryValid affineValid

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3_separator_semigroup_eq_actual
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3_derives_of_actual_factors

end SemigroupBasis.CoRoots.Order6SporadicSection25

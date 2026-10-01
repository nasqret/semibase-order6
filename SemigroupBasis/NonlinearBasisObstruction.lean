import SemigroupBasis.Equational

/-!
# A shared unrestricted obstruction for presentations with nonlinear sides

Nonempty substitutions preserve the presence of a repeated variable.
Consequently every derivation from an all-nonlinear presentation fixes
each square-free endpoint. The variable type, basis, substitutions,
contexts, and word lengths are unrestricted.
-/

namespace SemigroupBasis

def AllSidesNonlinear (basis : List (Identity α)) : Prop :=
  ∀ identity ∈ basis,
    ¬ identity.lhs.toList.Nodup ∧ ¬ identity.rhs.toList.Nodup

private theorem nodup_of_flatMap_nodup
    (source : List α) (images : α → List α)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) : source.Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons] at mappedNodup
      have split := List.nodup_append.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        obtain ⟨marker, markerMember⟩ :=
          List.exists_mem_of_ne_nil (images head) (imageNonempty head)
        have markerInTail : marker ∈ tail.flatMap images := by
          simp only [List.mem_flatMap]
          exact ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

private theorem source_nodup_of_bind_nodup
    (source : Word α) (substitution : α → Word α)
    (bound : (source.bind substitution).toList.Nodup) : source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

/-- Every square-free endpoint is rigid under the full derivation calculus. -/
theorem Derives.squareFree_rigid_of_allSidesNonlinear
    {basis : List (Identity α)} {left right : Word α}
    (derivation : Derives basis left right) (nonlinear : AllSidesNonlinear basis) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := nonlinear _ member
      exact ⟨fun nodup => False.elim (repeated.1 nodup),
        fun nodup => False.elim (repeated.2 nodup)⟩
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun nodup => (ih.2 nodup).symm,
      fun nodup => (ih.1 nodup).symm⟩
  | trans _ _ first second =>
      constructor
      · intro nodup
        have equalFirst := first.1 nodup
        subst_vars
        exact second.1 nodup
      · intro nodup
        have equalSecond := second.2 nodup
        subst_vars
        exact first.2 nodup
  | prepend _ _ ih =>
      constructor
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.1 suffixNodup]
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.2 suffixNodup]
  | appendRight _ _ ih =>
      constructor
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.1 prefixNodup]
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.2 prefixNodup]
  | subst _ substitution ih =>
      constructor
      · intro nodup
        have sourceNodup := source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.1 sourceNodup]
      · intro nodup
        have targetNodup := source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.2 targetNodup]

/-- One distinct square-free endpoint suffices for unrestricted nonderivability. -/
theorem not_derivable_of_nonlinear_basis
    {basis : List (Identity α)} {left right : Word α}
    (nonlinear : AllSidesNonlinear basis) (squareFree : left.toList.Nodup)
    (distinct : left ≠ right) : ¬ Derives basis left right := by
  intro derivation
  exact distinct ((derivation.squareFree_rigid_of_allSidesNonlinear nonlinear).1 squareFree)

end SemigroupBasis

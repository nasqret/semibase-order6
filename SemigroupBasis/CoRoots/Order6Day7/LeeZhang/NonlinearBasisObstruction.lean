import SemigroupBasis.Opposite

/-! A basis whose every side repeats a variable cannot move a linear word.
This extracts the list/derivation argument already used privately in
CoRoots.Order6FactorPairS3_8S5_240Obstruction into a reusable theorem.
Nonempty substitution is essential: these are semigroup words, not monoid
words permitting the empty substitution. No finite screen is a premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.NonlinearBasisObstruction

open SemigroupBasis

variable {α : Type u} {β : Type v}

def NonlinearSides (basis : List (Identity α)) : Prop :=
  ∀ identity ∈ basis,
    ¬ identity.lhs.toList.Nodup ∧ ¬ identity.rhs.toList.Nodup

theorem nodup_of_nonempty_flatMap_nodup
    (source : List α) (images : α → List β)
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
        have markerInTail : marker ∈ tail.flatMap images :=
          List.mem_flatMap.mpr ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

theorem nodup_of_bind_nodup (source : Word α) (substitution : α → Word β)
    (bound : (source.bind substitution).toList.Nodup) : source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_nonempty_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

/-- Unrestricted derivations, including arbitrary nonempty substitutions,
fix every linear word. Both directions are retained for symmetry/transitivity. -/
theorem derives_linear_rigid {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) {left right : Word α}
    (derivation : Derives basis left right) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := nonlinear _ member
      exact ⟨fun nodup => False.elim (repeated.1 nodup),
        fun nodup => False.elim (repeated.2 nodup)⟩
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih =>
      exact ⟨fun nodup => (ih.2 nodup).symm, fun nodup => (ih.1 nodup).symm⟩
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
  | prepend p _ ih =>
      constructor
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.1 suffixNodup]
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.2 suffixNodup]
  | appendRight _ suffix ih =>
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
        rw [ih.1 (nodup_of_bind_nodup _ substitution nodup)]
      · intro nodup
        rw [ih.2 (nodup_of_bind_nodup _ substitution nodup)]

theorem not_derives_of_linear_ne {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) {left right : Word α}
    (linear : left.toList.Nodup) (different : left ≠ right) :
    ¬ Derives basis left right := by
  intro derivation
  exact different ((derives_linear_rigid nonlinear derivation).1 linear)

theorem not_complete_of_valid_linear_identity {S : Type w}
    {G : Semigroup S} {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) (identity : Identity α)
    (valid : identity.SatisfiedBy G) (linear : identity.lhs.toList.Nodup)
    (different : identity.lhs ≠ identity.rhs) :
    ¬ (∀ e : Identity α, e.SatisfiedBy G → Derives basis e.lhs e.rhs) := by
  intro complete
  exact not_derives_of_linear_ne nonlinear linear different (complete identity valid)

theorem not_basisFor_of_valid_linear_identity {S : Type w}
    {G : Semigroup S} {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) (identity : Identity α)
    (valid : identity.SatisfiedBy G) (linear : identity.lhs.toList.Nodup)
    (different : identity.lhs ≠ identity.rhs) : ¬ BasisFor G basis := by
  intro complete
  exact not_complete_of_valid_linear_identity nonlinear identity valid linear different complete.2

theorem not_derives_reversed {basis : List (Identity α)} {left right : Word α}
    (obstruction : ¬ Derives basis left right) :
    ¬ Derives (reversedBasis basis) left.reverse right.reverse := by
  intro derivation
  apply obstruction
  simpa only [reversedBasis_reversedBasis, Word.reverse_reverse] using derivation.reverse

theorem not_complete_opposite_of_valid_linear_identity {S : Type w}
    {G : Semigroup S} {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) (identity : Identity α)
    (valid : identity.SatisfiedBy G) (linear : identity.lhs.toList.Nodup)
    (different : identity.lhs ≠ identity.rhs) :
    ¬ (∀ e : Identity α, e.SatisfiedBy G.opposite →
        Derives (reversedBasis basis) e.lhs e.rhs) := by
  intro complete
  have reversedValid : identity.reversed.SatisfiedBy G.opposite := by
    rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
    exact valid
  exact not_derives_reversed (not_derives_of_linear_ne nonlinear linear different)
    (complete identity.reversed reversedValid)

theorem not_basisFor_opposite_of_valid_linear_identity {S : Type w}
    {G : Semigroup S} {basis : List (Identity α)}
    (nonlinear : NonlinearSides basis) (identity : Identity α)
    (valid : identity.SatisfiedBy G) (linear : identity.lhs.toList.Nodup)
    (different : identity.lhs ≠ identity.rhs) :
    ¬ BasisFor G.opposite (reversedBasis basis) := by
  intro complete
  exact not_complete_opposite_of_valid_linear_identity nonlinear identity valid linear different complete.2

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.NonlinearBasisObstruction

import SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240Prelude

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240

open SemigroupBasis

/-- The square-free common identity omitted by the recorded basis. -/
def missingPrefixSwap : Identity Nat :=
  Identity.mk (Word.mk 0 [1, 2, 3]) (Word.mk 1 [0, 2, 3])

def missingPrefixSwapFin : Identity (Fin 4) :=
  Identity.mk (Word.mk 0 [1, 2, 3]) (Word.mk 1 [0, 2, 3])

theorem missingPrefixSwap_map :
    missingPrefixSwapFin.map Fin.val = missingPrefixSwap := rfl

theorem missingPrefixSwap_valid_s3_8 :
    missingPrefixSwap.SatisfiedBy
      SemigroupBasis.Generated.S3_8.table.semigroup := by
  rw [← missingPrefixSwap_map]
  exact SemigroupBasis.Generated.S3_8.table.checkIdentityNat_sound
    missingPrefixSwapFin (by decide)

theorem missingPrefixSwap_valid_s5_240 :
    missingPrefixSwap.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup := by
  rw [← missingPrefixSwap_map]
  exact SemigroupBasis.Generated.Catalogue.S5_240.table.checkIdentityNat_sound
    missingPrefixSwapFin (by decide)

private theorem nodup_of_flatMap_nodup
    (source : List Nat) (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) :
    source.Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons] at mappedNodup
      have split := List.nodup_append.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        obtain ⟨marker, markerMember⟩ :=
          List.exists_mem_of_ne_nil
            (images head) (imageNonempty head)
        have markerInTail : marker ∈ tail.flatMap images := by
          simp only [List.mem_flatMap]
          exact ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

private theorem source_nodup_of_bind_nodup
    (source : Word Nat) (substitution : Nat → Word Nat)
    (bound : (source.bind substitution).toList.Nodup) :
    source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

private theorem recordedBasis_has_repetition :
    ∀ identity ∈ recordedBasis,
      ¬ identity.lhs.toList.Nodup ∧
        ¬ identity.rhs.toList.Nodup := by
  decide

/-- A derivation from the recorded eight laws cannot move a square-free word.
Every displayed side has a repeated variable, and nonempty substitution,
context extension, symmetry, and transitivity preserve that rigidity. -/
private theorem recordedDerives_nodup_rigid
    {left right : Word Nat}
    (derivation : Derives recordedBasis left right) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := recordedBasis_has_repetition _ member
      exact
        ⟨fun nodup => False.elim (repeated.1 nodup),
          fun nodup => False.elim (repeated.2 nodup)⟩
  | refl =>
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ induction =>
      exact
        ⟨fun nodup => (induction.2 nodup).symm,
          fun nodup => (induction.1 nodup).symm⟩
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
        have sourceNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.1 sourceNodup]
      · intro nodup
        have targetNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.2 targetNodup]

theorem missingPrefixSwap_not_derivable :
    ¬ Derives recordedBasis
      missingPrefixSwap.lhs missingPrefixSwap.rhs := by
  intro derivation
  have literal := (recordedDerives_nodup_rigid derivation).1 (by decide)
  exact (by decide : missingPrefixSwap.lhs ≠ missingPrefixSwap.rhs) literal

/-- The exact eight-law joint-completeness claim is false. -/
theorem recordedJointCompleteness_isFalse :
    ¬ (∀ (identity : Identity Nat),
        identity.SatisfiedBy SemigroupBasis.Generated.S3_8.table.semigroup →
        identity.SatisfiedBy
          SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup →
        Derives recordedBasis identity.lhs identity.rhs) := by
  intro complete
  exact missingPrefixSwap_not_derivable
    (complete missingPrefixSwap
      missingPrefixSwap_valid_s3_8 missingPrefixSwap_valid_s5_240)

end SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240

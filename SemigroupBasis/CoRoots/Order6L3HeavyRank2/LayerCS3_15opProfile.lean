import SemigroupBasis.CoRoots.Order6L3HeavyRank2.Blocks
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.Nonfinite.GraphParity

/-!
# The common unrestricted profile of the `S3_15^op` factor

All four C1 pairs share exactly this left-factor information: validity in the
opposite left normal band preserves support and the final variable.  The
right-factor sections may consume the profile, but must prove their own
additional signature and reach lemmas.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2

open SemigroupBasis
open SemigroupBasis.Examples

/-- The two word coordinates detected by the common `S3_15^op` factor. -/
structure SameLastSupport (left right : Word Nat) : Prop where
  final_eq : left.final = right.final
  support_eq : forall letter : Nat,
    letter ∈ left.toList ↔ letter ∈ right.toList

namespace SameLastSupport

theorem refl (word : Word Nat) : SameLastSupport word word :=
  ⟨rfl, fun _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameLastSupport left right) :
    SameLastSupport right left :=
  ⟨same.final_eq.symm, fun letter => (same.support_eq letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameLastSupport left middle)
    (second : SameLastSupport middle right) :
    SameLastSupport left right :=
  ⟨first.final_eq.trans second.final_eq,
    fun letter => (first.support_eq letter).trans
      (second.support_eq letter)⟩

end SameLastSupport

/-- The exact opposite table in the rank-two block is definitionally the
opposite of the stored `S3_15` semigroup. -/
theorem s3_15OppositeTable_semigroup :
    s3_15OppositeTable.semigroup =
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite := by
  rfl

private theorem reverse_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).reverse =
      Word.mk final stem.reverse := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_wordOfPrefixFinal]
  simp [Word.toList]

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem splitPrefixFinal_snd_eq_final (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  calc
    word.reverse.head =
        (wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2).reverse.head :=
      congrArg (fun rebuilt : Word Nat => rebuilt.reverse.head)
        (wordOfPrefixFinal_split word).symm
    _ = (splitPrefixFinal word).2 :=
      congrArg Word.head <|
        reverse_wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2
    _ = word.final := splitPrefixFinal_snd_eq_final word

/-- Every identity valid in the common left factor has equal final letters
and equal support. -/
theorem sameLastSupport_of_s3_15Opposite_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s3_15OppositeTable.semigroup) :
    SameLastSupport identity.lhs identity.rhs := by
  have targetValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup.opposite := by
    simpa only [s3_15OppositeTable_semigroup] using valid
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Examples.leftNormalBandFifteen.semigroup := by
    apply
      (Identity.satisfiedBy_opposite_iff_reversed identity
        SemigroupBasis.Examples.leftNormalBandFifteen.semigroup).mp
    simpa only
      [SemigroupBasis.Generated.S3_15.table,
        SemigroupBasis.Examples.leftNormalBandFifteen] using targetValid
  have reversedSupport :=
    SemigroupBasis.Examples.leftNormalBandFifteenValid_support_eq
      identity.reversed reversedValid
  have reversedHeads :=
    SemigroupBasis.Examples.leftNormalBandFifteenValid_head_eq
      identity.reversed reversedValid
  have finalEq : identity.lhs.final = identity.rhs.final := by
    simpa only [Identity.reversed, reverse_head_eq_final] using
      reversedHeads
  refine ⟨finalEq, ?_⟩
  intro letter
  simpa only [Identity.reversed, Word.toList_reverse,
    List.mem_reverse] using reversedSupport letter

end SemigroupBasis.CoRoots.Order6L3HeavyRank2

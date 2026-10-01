import SemigroupBasis.Nonfinite.B2One.StabilityReconstruction

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis
open SemigroupBasis.Examples.B2One

/-!
Closure of the remaining semantic projection boundary in Perkins's proof for
the six-element Brandt monoid.
-/

/-- Every valid bounded-variable contextual rewrite preserves the
distinguished six-occurrence projection required by Sapir's reconstruction of
Perkins's argument. -/
theorem perkinsSemanticProjection :
    PerkinsSemanticProjectionLemma := by
  intro bound identity valid uses pre post substitution semantic pattern
    z zMiddle
  rcases
      selectContextPackedPreimageLayers
        valid uses pre post substitution semantic pattern with
    ⟨packed, augmented, packedValid, _packedUses,
      leftMapped, rightMapped, firstBlock, secondBlock,
      firstPerm, secondPerm, targetShape, independent, distinguished⟩
  have transport :=
    bind_projection_stable_of_PerkinsDistinguishedPreimages
      leftMapped pattern packedValid
      firstPerm secondPerm targetShape independent distinguished zMiddle
  rw [leftMapped, rightMapped] at transport
  have leftProjection :
      (contextWord pre
          (identity.lhs.bind substitution) post).toList.filter
            (keepTriple 0 1 z) =
        [0, 1, z, 0, z, 1] := by
    simpa [occurrenceProjection, keepTriple] using
      pattern.occurrenceProjection_eq zMiddle
  have rightProjection :
      (contextWord pre
          (identity.rhs.bind substitution) post).toList.filter
            (keepTriple 0 1 z) =
        [0, 1, z, 0, z, 1] :=
    transport.symm.trans leftProjection
  simpa [occurrenceProjection, keepTriple] using rightProjection

/-- Perkins's nonfinite-basis theorem for the printed `B₂¹` multiplication
table, with no remaining semantic hypothesis. -/
theorem table_nonfinitelyBased :
    NonfinitelyBased table.semigroup :=
  table_nonfinitelyBased_of_semanticProjection
    perkinsSemanticProjection

/-- The corresponding unconditional theorem for catalogue class `S6_8564`. -/
theorem s6_8564_nonfinitelyBased :
    NonfinitelyBased catalogueTable.semigroup :=
  s6_8564_nonfinitelyBased_of_semanticProjection
    perkinsSemanticProjection

end SemigroupBasis.Nonfinite.B2One

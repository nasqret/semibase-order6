import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788Derivations
import SemigroupBasis.CoRoots.Order6LeeZhangCondition14EndpointNormal

/-!
# Replaying the Condition 14 anchored calculus in the exact C2 basis

This bridge is exclusively syntactic: all six source axioms receive explicit
C2 displayed-law derivations before any old anchored-interior derivation is
transported.  It never asserts validity in the stronger `S5_791` factor or
imports that factor's semantic signature as a premise.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.basis

/-- Each of the six old anchored-calculus axioms is a genuine consequence
of the exact eighteen displayed C2 laws. -/
theorem condition14AxiomDerives
    (identity : Identity Nat) (member : identity ∈ sourceBasis) :
    Derives targetBasis identity.lhs identity.rhs := by
  change identity ∈
    [Identity.mk (Word.mk 0 [0, 0, 0]) (Word.mk 0 [0]),
      Identity.mk (Word.mk 0 [1, 1, 1, 0]) (Word.mk 0 [1, 0]),
      Identity.mk (Word.mk 0 [1, 0, 0, 0]) (Word.mk 0 [1, 0]),
      Identity.mk (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]),
      Identity.mk (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [0, 1, 2, 0]),
      Identity.mk (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0])]
    at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    first | second | third | fourth | fifth | sixth
  · subst identity
    exact
      (Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]))
        (by decide)).symm
  · subst identity
    exact
      (Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [1, 0])
          (Word.mk 0 [1, 1, 1, 0]))
        (by decide)).symm
  · subst identity
    exact
      (Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [1, 0])
          (Word.mk 0 [1, 0, 0, 0]))
        (by decide)).symm
  · subst identity
    exact
      Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [0, 1, 0])
          (Word.mk 0 [1, 0, 0]))
        (by decide)
  · subst identity
    exact
      (Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [0, 1, 2, 0])
          (Word.mk 0 [1, 0, 2, 0]))
        (by decide)).symm
  · subst identity
    exact
      (Derives.fromBasis
        (e := Identity.mk (Word.mk 0 [0, 1, 1])
          (Word.mk 0 [1, 0, 1]))
        (by decide)).symm.trans
          (Derives.fromBasis
            (e := Identity.mk (Word.mk 0 [0, 1, 1])
              (Word.mk 0 [1, 1, 0]))
            (by decide))

/-- Transport every old Condition 14 word derivation only after its axioms
have been discharged in the target basis. -/
theorem transportCondition14Derives
    {left right : Word Nat}
    (derivation : Derives sourceBasis left right) :
    Derives targetBasis left right :=
  Derives.transport condition14AxiomDerives derivation

/-- List-level transport retains the empty-list case without manufacturing
an impossible empty semigroup word. -/
theorem transportCondition14ListDerives
    {left right : List Nat}
    (derivation :
      SemigroupBasis.CoRoots.S5_107.ListDerives sourceBasis left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis left right := by
  cases derivation with
  | empty =>
      exact .empty
  | words derivation =>
      exact .words (transportCondition14Derives derivation)

/-- Reuse the entire anchored parity/initial interior normalizer in C2,
with both endpoint occurrences fixed. -/
theorem listDerivesClosedParityInitialNormal
    (endpoint : Nat) (interior : List Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
      ([endpoint] ++ interior ++ [endpoint])
      ([endpoint] ++
        SemigroupBasis.Examples.parityInitialNormalList interior ++
        [endpoint]) :=
  transportCondition14ListDerives
    (SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.listDerivesClosedParityInitialNormal
      endpoint interior)

/-- Every support-connected component also inherits the already-proved
anchored parity/initial normalization, with no stronger semantic premise. -/
theorem listDerivesComponentInitialParityLocalNormal
    (component : List Nat) (nonempty : component ≠ [])
    (connected :
      SemigroupBasis.Examples.ConnectedComponentSupportConnected component) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis component
      (SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentInitialParityRender
        component
        (SemigroupBasis.Examples.firstOccurrenceSequence component)
        (SemigroupBasis.Examples.connectedComponentSignatureOfList component)) :=
  transportCondition14ListDerives
    (SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.listDerivesComponentInitialParityLocalNormal
      component nonempty connected)

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

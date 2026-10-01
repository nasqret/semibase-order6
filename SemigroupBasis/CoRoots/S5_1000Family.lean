import SemigroupBasis.CoRoots.S5_1000DualTransport

namespace SemigroupBasis.CoRoots.S5_1000Family

open SemigroupBasis

/-- The common reversed presentation for both catalogue tables:
`xx = xxxxx`, `yx = yxxxx`, `zyx = zxy`, and
`yyxxx = xyyxx`. -/
def oppositeBasis : List (Identity Nat) :=
  [
    ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩,
    ⟨⟨1, [0]⟩, ⟨1, [0, 0, 0, 0]⟩⟩,
    ⟨⟨2, [1, 0]⟩, ⟨2, [0, 1]⟩⟩,
    ⟨⟨1, [1, 0, 0, 0]⟩, ⟨0, [1, 1, 0, 0]⟩⟩
  ]

theorem oppositeBasis_eq_reversedBasis :
    oppositeBasis =
      reversedBasis SemigroupBasis.CoRoots.S5_1000.basis := by
  decide

namespace S5_1000

/-- Unconditional direct basis endpoint for the exact `S5_1000` table. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_1000.table.semigroup
      SemigroupBasis.CoRoots.S5_1000.basis := by
  refine
    ⟨SemigroupBasis.CoRoots.S5_1000.S5_1000.models, ?_⟩
  intro identity valid
  exact SemigroupBasis.CoRoots.S5_1000.derivesOfSameSignature
    (SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1000.valid_sameSignature
      identity valid)

/-- Unconditional endpoint for the opposite `S5_1000` table. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_1000.table.semigroup.opposite
      oppositeBasis := by
  rw [oppositeBasis_eq_reversedBasis]
  exact basisFor.oppositeReversed

end S5_1000

namespace S5_1003

/-- Unconditional direct basis endpoint for the exact `S5_1003` table. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_1003.table.semigroup
      SemigroupBasis.CoRoots.S5_1000.basis := by
  refine
    ⟨SemigroupBasis.CoRoots.S5_1000.S5_1003.models, ?_⟩
  intro identity valid
  exact SemigroupBasis.CoRoots.S5_1000.derivesOfSameSignature
    (SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1003.valid_sameSignature
      identity valid)

/-- Unconditional endpoint for the opposite `S5_1003` table. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_1003.table.semigroup.opposite
      oppositeBasis := by
  rw [oppositeBasis_eq_reversedBasis]
  exact basisFor.oppositeReversed

end S5_1003

/-- Aggregate proposition exposing both tables in both anti-isomorphism
orientations. -/
structure FamilyBasisEndpoints : Prop where
  s5_1000 :
    BasisFor Generated.Catalogue.S5_1000.table.semigroup
      SemigroupBasis.CoRoots.S5_1000.basis
  s5_1000_opposite :
    BasisFor Generated.Catalogue.S5_1000.table.semigroup.opposite
      oppositeBasis
  s5_1003 :
    BasisFor Generated.Catalogue.S5_1003.table.semigroup
      SemigroupBasis.CoRoots.S5_1000.basis
  s5_1003_opposite :
    BasisFor Generated.Catalogue.S5_1003.table.semigroup.opposite
      oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  s5_1000 := S5_1000.basisFor
  s5_1000_opposite := S5_1000.oppositeBasisFor
  s5_1003 := S5_1003.basisFor
  s5_1003_opposite := S5_1003.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_1000Family

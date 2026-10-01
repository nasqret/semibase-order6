import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection
import SemigroupBasis.FiniteCertificate

/-!
# Exact L2D rank-22 extension for the two H7 endpoints

The rank-22 design packet records a 24-law basis with SHA-256
`0d636ee4eaef78fc358af1ca29251363549dae8e39016134eec361836b536b23`
for `S6_8562` and `S6_11276`.  Its first six laws are literally the
unrestricted H7 basis (SHA-256
`7b8c7ea4dec16028e8794bbb06124946433f5a00add459eb3bfb7c173611ca09`).
The remaining eighteen laws are sound shortcuts.  Therefore the exact packet
basis follows from the existing H7 completeness theorem by `BasisFor.replace`;
no bounded-closure argument is used here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L2DRank22

open SemigroupBasis

namespace H7

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection.H7.basis

end H7

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## The eighteen packet laws following the exact H7 prefix -/

def law06 : Identity Nat :=
  Identity.mk (w 1 [0, 0, 1]) (w 1 [0, 0, 1, 0])

def law07 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [0, 1, 1])

def law08 : Identity Nat :=
  Identity.mk (w 2 [2, 0, 1, 0]) (w 2 [0, 1, 2, 2, 0])

def law09 : Identity Nat :=
  Identity.mk (w 2 [2, 1, 0, 1]) (w 2 [1, 0, 2, 2, 1])

def law10 : Identity Nat :=
  Identity.mk (w 0 [0, 2, 1, 0, 2]) (w 0 [0, 2, 1, 2])

def law11 : Identity Nat :=
  Identity.mk (w 2 [0, 1, 0, 1, 2]) (w 2 [0, 1, 2, 2])

def law12 : Identity Nat :=
  Identity.mk (w 0 [2, 1, 0, 2, 2]) (w 0 [1, 0, 2, 1, 0])

def law13 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 0, 2]) (w 0 [1, 0, 2, 0, 1])

def law14 : Identity Nat :=
  Identity.mk (w 0 [1, 1, 2, 0, 2]) (w 0 [1, 2, 0, 2])

def law15 : Identity Nat :=
  Identity.mk (w 1 [0, 0, 2, 1]) (w 1 [2, 1, 0, 0])

def law16 : Identity Nat :=
  Identity.mk (w 2 [0, 0, 1, 0]) (w 2 [1, 0, 0, 1])

def law17 : Identity Nat :=
  Identity.mk (w 0 [2, 1, 1, 0]) (w 0 [2, 0, 2, 1, 0])

def law18 : Identity Nat :=
  Identity.mk (w 2 [0, 1, 1, 2]) (w 2 [0, 1, 2, 0, 2])

def law19 : Identity Nat :=
  Identity.mk (w 2 [1, 0, 2, 1, 2]) (w 2 [1, 0, 0, 2])

def law20 : Identity Nat :=
  Identity.mk (w 1 [0, 2, 2, 1]) (w 1 [0, 1, 0, 2, 1])

def law21 : Identity Nat :=
  Identity.mk (w 0 [1, 1, 2, 1]) (w 0 [2, 1, 1, 2])

def law22 : Identity Nat :=
  Identity.mk (w 1 [2, 0, 0, 1]) (w 1 [2, 0, 1, 2, 1])

def law23 : Identity Nat :=
  Identity.mk (w 1 [0, 0, 2, 0]) (w 1 [2, 0, 0, 2])

/-- The exact 24-law rank-22 packet basis.  The append form makes the
literal H7-prefix inclusion transparent to the kernel. -/
def basis : List (Identity Nat) :=
  H7.basis ++
    [law06, law07, law08, law09, law10, law11, law12, law13,
      law14, law15, law16, law17, law18, law19, law20, law21,
      law22, law23]

def displayedBasisSHA256 : String :=
  "0d636ee4eaef78fc358af1ca29251363549dae8e39016134eec361836b536b23"

theorem basis_length : basis.length = 24 := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem h7AxiomsDerive
    (identity : Identity Nat) (member : identity ∈ H7.basis) :
    Derives basis identity.lhs identity.rhs :=
  Derives.fromBasis (List.mem_append.mpr (Or.inl member))

namespace S6_8562

abbrev table :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection.S6_8562.table

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

/-- Exact 24-law representative endpoint for `S6_8562`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection.S6_8562.representative_basis.replace
    models h7AxiomsDerive

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8562

namespace S6_11276

abbrev table :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection.S6_11276.table

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

/-- Exact 24-law representative endpoint for `S6_11276`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection.S6_11276.representative_basis.replace
    models h7AxiomsDerive

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11276

end SemigroupBasis.CoRoots.Order6L2DRank22

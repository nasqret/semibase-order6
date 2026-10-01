import SemigroupBasis.Examples.CyclicFour
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S4_37

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact Smallsemi catalogue representative `S4_37`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_37.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_37.table := rfl

/-- The exact catalogue basis `xy = yx`, `xxxxy = y`. -/
abbrev basis : List (Identity Nat) :=
  cyclicFourBasis

/-- Relabel the additive presentation of `C4` by the zero-based permutation
`[0, 2, 1, 3]`, equivalently `[1, 3, 2, 4]` in catalogue notation. -/
def cyclicFourRelabel (a : Fin 4) : Fin 4 :=
  if a = 0 then 0
  else if a = 1 then 2
  else if a = 2 then 1
  else 3

/-- The audited table isomorphism, used in the direction needed by the
embedded-subsemigroup identity-theory transfer theorem. -/
def cyclicFourEmbedding :
    Embedding cyclicFour.semigroup table.semigroup where
  toFun := cyclicFourRelabel
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b equal
    exact by decide +revert

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteCancellationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 0, 1]⟩, ⟨1, []⟩⟩

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      cyclicFourCommutativityLaw := rfl

theorem finiteCancellationLaw_map :
    finiteCancellationLaw.map Fin.val =
      cyclicFourCancellationLaw := rfl

/-- Exhaustive finite reflection checks that the exact catalogue table
models the two displayed identities. -/
theorem representative_models :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, cyclicFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)
  · rw [← finiteCancellationLaw_map]
    exact table.checkIdentityNat_sound finiteCancellationLaw (by decide)

/-- `S4_37` inherits the complete `C4` identity theory through the explicit
four-element embedding. -/
theorem basis_complete :
    BasisFor table.semigroup basis :=
  cyclicFourBasis_complete.inheritAlongEmbedding
    cyclicFourEmbedding representative_models

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

/-- The catalogue table is commutative, hence equal to its opposite
semigroup without any carrier relabeling. -/
theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_37.table
    SemigroupBasis.Generated.Catalogue.S4_37.mul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite basis := by
  rw [self_dual]
  exact basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite basis :=
  opposite_basis_complete

end SemigroupBasis.CoRoots.S4_37

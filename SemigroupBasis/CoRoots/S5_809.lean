import SemigroupBasis.Generated.S4_75
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_809

open SemigroupBasis
open SemigroupBasis.Examples

def xx : Word Nat := ⟨0, [0]⟩
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def yxx : Word Nat := ⟨1, [0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def finalGatherLaw : Identity Nat := ⟨xyx, yxx⟩

/-- Edmunds' exact basis for M15, identified with `S5_809`. -/
def basis : List (Identity Nat) :=
  [powerLaw, finalGatherLaw]

/-- The literal reverse-word basis `xx = xxx`, `xyx = xxy`. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def expectedOppositeBasis : List (Identity Nat) :=
  [powerLaw, ⟨xyx, xxy⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

/-- The reversed M15 basis is exactly the already formalized published
order-four root basis for Edmunds' `S(5,2)`. -/
theorem oppositeBasis_eq_publishedRootBasis :
    oppositeBasis = edmundsFiveTwoFourBasis := by
  rfl

/-- Reconstructed M15 multiplication in the stored order `0,a,b,c,1`.
The nonidentity star table is Edmunds' `000/abc/abc`. -/
def publishedM15Mul (a b : Fin 5) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 4 then 1 else 0
  else if a = 2 then
    if b = 0 then 0
    else if b = 1 then 1
    else if b = 3 then 3
    else 2
  else if a = 3 then
    if b = 0 then 0
    else if b = 1 then 1
    else if b = 2 then 2
    else 3
  else b

def publishedM15Table : FiniteTable where
  order := 5
  mul := publishedM15Mul
  assoc := by decide

theorem publishedM15Mul_eq_catalogue (a b : Fin 5) :
    publishedM15Mul a b =
      Generated.Catalogue.S5_809.mul a b := by
  decide +revert

/-- Exact historical-to-Smallsemi table identification. -/
theorem publishedM15Table_eq_catalogue :
    publishedM15Table =
      Generated.Catalogue.S5_809.table := by
  unfold publishedM15Table Generated.Catalogue.S5_809.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  exact publishedM15Mul_eq_catalogue a b

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteFinalGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteFinalGatherLaw_map :
    finiteFinalGatherLaw.map Fin.val = finalGatherLaw := rfl

/-- Direct finite verification of both M15 laws. -/
theorem publishedM15Models :
    Models publishedM15Table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact publishedM15Table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteFinalGatherLaw_map]
    exact publishedM15Table.checkIdentityNat_sound
      finiteFinalGatherLaw (by decide)

theorem catalogueModels :
    Models Generated.Catalogue.S5_809.table.semigroup basis := by
  rw [← publishedM15Table_eq_catalogue]
  exact publishedM15Models

def firstSeparator :
    Hom Generated.S4_75.table.semigroup
      publishedM15Table.semigroup.opposite where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩
    else if a.val = 1 then ⟨1, by decide⟩
    else if a.val = 2 then ⟨0, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro a b
    exact by decide +revert

def secondSeparator :
    Hom Generated.S4_75.table.semigroup
      publishedM15Table.semigroup.opposite where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩
    else if a.val = 1 then ⟨2, by decide⟩
    else if a.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro a b
    exact by decide +revert

def separatorProfilesOneBased : List (List Nat) :=
  [
    List.ofFn (fun a : Fin 4 => (firstSeparator.toFun a).val + 1),
    List.ofFn (fun a : Fin 4 => (secondSeparator.toFun a).val + 1)
  ]

theorem separatorProfilesOneBased_certificate :
    separatorProfilesOneBased =
      [[1, 2, 1, 5], [3, 3, 4, 5]] := by
  decide

theorem separatorPair_injective :
    Function.Injective
      (fun a : Fin 4 =>
        (firstSeparator.toFun a, secondSeparator.toFun a)) := by
  intro a b
  exact by decide +revert

/-- The two published-root homomorphisms jointly separate all four root
elements, hence embed `S4_75` into `(M15ᵒᵖ)^2`. -/
def publishedRootPowerEmbedding :
    Embedding Generated.S4_75.table.semigroup
      (publishedM15Table.semigroup.opposite.pi (Fin 2)) where
  toFun := fun a coordinate =>
    if coordinate = 0 then
      firstSeparator.toFun a
    else
      secondSeparator.toFun a
  map_mul := by
    intro a b
    funext coordinate
    exact by decide +revert
  injective := by
    intro a b equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

/-- Unconditional completeness in the opposite orientation. The published
`S4_75` theorem supplies completeness, the two-coordinate separator supplies
the reverse identity inclusion, and the direct table check supplies models. -/
theorem publishedM15Opposite_basis_complete :
    BasisFor publishedM15Table.semigroup.opposite oppositeBasis := by
  have targetModels :
      Models publishedM15Table.semigroup.opposite
        edmundsFiveTwoFourBasis := by
    rw [← oppositeBasis_eq_publishedRootBasis]
    exact publishedM15Models.oppositeReversed
  have inherited :
      BasisFor publishedM15Table.semigroup.opposite
        edmundsFiveTwoFourBasis :=
    Generated.S4_75.representative_basis.inheritAlongPowerEmbedding
      publishedRootPowerEmbedding targetModels
  rw [oppositeBasis_eq_publishedRootBasis]
  exact inherited

/-- Unconditional completeness in Edmunds' stored M15 orientation. -/
theorem publishedM15_basis_complete :
    BasisFor publishedM15Table.semigroup basis := by
  have reversed :=
    publishedM15Opposite_basis_complete.oppositeReversed
  simpa [oppositeBasis] using reversed

/-- Exact representative endpoint for catalogue `S5_809`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_809.table.semigroup basis := by
  rw [← publishedM15Table_eq_catalogue]
  exact publishedM15_basis_complete

/-- Exact opposite endpoint with the literal reversed basis. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_809.table.semigroup.opposite
      oppositeBasis := by
  rw [← publishedM15Table_eq_catalogue]
  exact publishedM15Opposite_basis_complete

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_809.table.semigroup basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_809.table.semigroup.opposite
      (reversedBasis basis) := by
  simpa [oppositeBasis] using opposite_basis_complete

end SemigroupBasis.CoRoots.S5_809

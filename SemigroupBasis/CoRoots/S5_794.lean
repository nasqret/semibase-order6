import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis

@[simp] private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxzwz : Word Nat := w 0 [0, 2, 3, 2]
def xzxwz : Word Nat := w 0 [2, 0, 3, 2]
def xxzx : Word Nat := w 0 [0, 2, 0]
def xzx : Word Nat := w 0 [2, 0]
def xxzz : Word Nat := w 0 [0, 2, 2]
def xzxz : Word Nat := w 0 [2, 0, 2]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxzwz : Word Nat := w 0 [1, 0, 2, 3, 2]
def xyzxwz : Word Nat := w 0 [1, 2, 0, 3, 2]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzwxz : Word Nat := w 0 [1, 2, 3, 0, 2]
def xyzwzx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xzwxz : Word Nat := w 0 [2, 3, 0, 2]
def xzwzx : Word Nat := w 0 [2, 3, 2, 0]
def xzzx : Word Nat := w 0 [2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def firstDeletionLaw : Identity Nat := ⟨xxzwz, xzxwz⟩
def leftDeletionLaw : Identity Nat := ⟨xxzx, xzx⟩
def squareInterchangeLaw : Identity Nat := ⟨xxzz, xzxz⟩
def rightExpansionLaw : Identity Nat := ⟨xyx, xyxx⟩
def mixedDeletionLaw : Identity Nat := ⟨xyxzwz, xyzxwz⟩
def middleDeletionLaw : Identity Nat := ⟨xyxzx, xyzx⟩
def doubledSuffixLaw : Identity Nat := ⟨xyxzz, xyzxz⟩
def longRotationLaw : Identity Nat := ⟨xyzwxz, xyzwzx⟩
def terminalSquareLaw : Identity Nat := ⟨xyzxz, xyzzx⟩
def shortRotationLaw : Identity Nat := ⟨xzwxz, xzwzx⟩
def alternatingSquareLaw : Identity Nat := ⟨xzxz, xzzx⟩

/-- The exact common basis recorded for `S5_794`, `S5_802`, and `S5_810`. -/
def basis : List (Identity Nat) :=
  [powerLaw, firstDeletionLaw, leftDeletionLaw, squareInterchangeLaw,
    rightExpansionLaw, mixedDeletionLaw, middleDeletionLaw,
    doubledSuffixLaw, longRotationLaw, terminalSquareLaw,
    shortRotationLaw, alternatingSquareLaw]

/-- The three identities stated for Edmunds' `M14` in Proposition 3.2(b),
before taking closure under deletion. -/
def publishedCoreBasis : List (Identity Nat) :=
  [⟨xyzx, xyxzx⟩, longRotationLaw, mixedDeletionLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Convert exhaustive checks on the four variables used by the basis into
a `Models` theorem over the repository's infinite variable type. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- Edmunds' `M14` multiplication in the stored element order
`0, a, b, c, 1`. The nonidentity star table is `000/abb/acc`. -/
def publishedM14Mul (a b : Fin 5) : Fin 5 :=
  if a = 4 then b
  else if b = 4 then a
  else if a = 0 then 0
  else if b = 0 then 0
  else if a = 1 then 0
  else if b = 1 then 1
  else a

def publishedM14Table : FiniteTable where
  order := 5
  mul := publishedM14Mul
  assoc := by decide

theorem publishedM14Mul_eq_catalogue
    (a b : Fin 5) :
    publishedM14Mul a b =
      Generated.Catalogue.S5_802.mul a b := by
  decide +revert

/-- The direct table identification recorded in
`edmunds_order5_monoid_mapping.json`. -/
def publishedM14ToCatalogue :
    Embedding publishedM14Table.semigroup
      Generated.Catalogue.S5_802.table.semigroup where
  toFun := id
  map_mul := publishedM14Mul_eq_catalogue
  injective := Function.injective_id

def catalogueToPublishedM14 :
    Embedding Generated.Catalogue.S5_802.table.semigroup
      publishedM14Table.semigroup where
  toFun := id
  map_mul := by
    intro a b
    exact (publishedM14Mul_eq_catalogue a b).symm
  injective := Function.injective_id

theorem publishedM14Models :
    Models publishedM14Table.semigroup basis :=
  models_of_finite_checks publishedM14Table (by decide)

theorem catalogueS5_802Models :
    Models Generated.Catalogue.S5_802.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_802.table (by decide)

/-- The sole unformalized content of Edmunds' Proposition 3.2(b): every
identity valid in the explicitly reconstructed `M14` table is derivable from
the twelve deletion-closure laws. This is a proposition, not an axiom. -/
def M14CompletenessObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy publishedM14Table.semigroup →
      Derives basis identity.lhs identity.rhs

theorem publishedM14BasisFor_of_completeness
    (completeness : M14CompletenessObligation) :
    BasisFor publishedM14Table.semigroup basis :=
  ⟨publishedM14Models, completeness⟩

theorem catalogueS5_802BasisFor_of_publishedCompleteness
    (completeness : M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_802.table.semigroup basis :=
  (publishedM14BasisFor_of_completeness completeness).inheritAlongEmbedding
    publishedM14ToCatalogue catalogueS5_802Models

end SemigroupBasis.CoRoots.S5_794

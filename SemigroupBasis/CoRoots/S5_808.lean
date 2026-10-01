import SemigroupBasis.CoRoots.S5_848
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_808

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xxyyz : Word Nat := w 0 [0, 1, 1, 2]
def xyyxz : Word Nat := w 0 [1, 1, 0, 2]
def zyyxx : Word Nat := w 2 [1, 1, 0, 0]
def zxyyx : Word Nat := w 2 [0, 1, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def gatherLaw : Identity Nat := ⟨xyx, yxx⟩
def tailSquareLaw : Identity Nat := ⟨xxyyz, xyyxz⟩

/-- The exact catalogue basis for `S5_808` and `S5_844`:
`xx = xxx`, `xyx = yxx`, and `xxyyz = xyyxz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, tailSquareLaw]

/-- The literal reverse-word basis for the non-self-dual opposite class. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem oppositeBasis_eq_literal :
    oppositeBasis =
      [⟨xx, xxx⟩, ⟨xyx, xxy⟩, ⟨zyyxx, zxyyx⟩] := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the three displayed variables imply the
corresponding `Models` theorem over the standard infinite variable type. -/
theorem models_of_finite_checks
    (model : FiniteTable)
    (checks : finiteBasis.all model.checkIdentity = true) :
    Models model.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    model.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_808.table

theorem table_eq_canonical_catalogue :
    table = Generated.Catalogue.S5_808.table := rfl

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private theorem oppositePowerDerives :
    Derives oppositeBasis xx xxx := by
  refine Derives.fromBasis (e := ⟨xx, xxx⟩) ?_
  rw [oppositeBasis_eq_literal]
  exact List.Mem.head _

private theorem oppositeGatherDerives :
    Derives oppositeBasis xyx xxy := by
  refine Derives.fromBasis (e := ⟨xyx, xxy⟩) ?_
  rw [oppositeBasis_eq_literal]
  exact List.Mem.tail _ (List.Mem.head _)

private theorem oppositeTailDerives :
    Derives oppositeBasis zyyxx zxyyx := by
  refine Derives.fromBasis (e := ⟨zyyxx, zxyyx⟩) ?_
  rw [oppositeBasis_eq_literal]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private def swapXZ : Nat → Word Nat
  | 0 => Word.singleton 2
  | 1 => Word.singleton 1
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

/-- After orienting the gather law by symmetry, the nontrivial bridge
to the `S5_848` basis is the `x`/`z` renaming of the third law. -/
theorem canonicalTailDerives :
    Derives oppositeBasis
      SemigroupBasis.CoRoots.S5_848.xyyzz
      SemigroupBasis.CoRoots.S5_848.xzyyz := by
  have renamed := Derives.subst oppositeTailDerives swapXZ
  change
    Derives oppositeBasis
      (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  simpa [zyyxx, zxyyx, w, swapXZ, Word.bind,
    Word.singleton] using renamed

/-- Every axiom of the dual normal-form root follows from the literal
reverse-word catalogue basis. -/
theorem canonicalAxiomsDerive
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_848.basis) :
    Derives oppositeBasis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_848.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change Derives oppositeBasis xx xxx
    exact oppositePowerDerives
  · change Derives oppositeBasis xxy xyx
    exact oppositeGatherDerives.symm
  · exact canonicalTailDerives

/-- The exact opposite table models the dual normal-form root basis. -/
theorem canonicalOppositeModels :
    Models table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_848.basis := by
  intro identity member valuation
  exact
    (canonicalAxiomsDerive identity member).sound
      oppositeModels valuation

/-- The first separating homomorphism
`[1,2,1,3,5] : S5_848 -> S5_808^op`. -/
def firstDualHom :
    Hom SemigroupBasis.CoRoots.S5_848.table.semigroup
      table.semigroup.opposite where
  toFun := fun value =>
    if value = (0 : Fin 5) then (0 : Fin 5)
    else if value = (1 : Fin 5) then (1 : Fin 5)
    else if value = (2 : Fin 5) then (0 : Fin 5)
    else if value = (3 : Fin 5) then (2 : Fin 5)
    else (4 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

/-- The second separating homomorphism
`[3,3,4,3,3] : S5_848 -> S5_808^op`. -/
def secondDualHom :
    Hom SemigroupBasis.CoRoots.S5_848.table.semigroup
      table.semigroup.opposite where
  toFun := fun value =>
    if value = (2 : Fin 5) then (3 : Fin 5) else (2 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

def dualHomomorphismsOneBased : List (List Nat) :=
  [[(firstDualHom.toFun (0 : Fin 5)).val + 1,
      (firstDualHom.toFun (1 : Fin 5)).val + 1,
      (firstDualHom.toFun (2 : Fin 5)).val + 1,
      (firstDualHom.toFun (3 : Fin 5)).val + 1,
      (firstDualHom.toFun (4 : Fin 5)).val + 1],
    [(secondDualHom.toFun (0 : Fin 5)).val + 1,
      (secondDualHom.toFun (1 : Fin 5)).val + 1,
      (secondDualHom.toFun (2 : Fin 5)).val + 1,
      (secondDualHom.toFun (3 : Fin 5)).val + 1,
      (secondDualHom.toFun (4 : Fin 5)).val + 1]]

theorem dualHomomorphismsOneBased_certificate :
    dualHomomorphismsOneBased =
      [[1, 2, 1, 3, 5], [3, 3, 4, 3, 3]] := by
  decide

def dualDiagonalSignaturesOneBased : List (Nat × Nat) :=
  [((firstDualHom.toFun (0 : Fin 5)).val + 1,
      (secondDualHom.toFun (0 : Fin 5)).val + 1),
    ((firstDualHom.toFun (1 : Fin 5)).val + 1,
      (secondDualHom.toFun (1 : Fin 5)).val + 1),
    ((firstDualHom.toFun (2 : Fin 5)).val + 1,
      (secondDualHom.toFun (2 : Fin 5)).val + 1),
    ((firstDualHom.toFun (3 : Fin 5)).val + 1,
      (secondDualHom.toFun (3 : Fin 5)).val + 1),
    ((firstDualHom.toFun (4 : Fin 5)).val + 1,
      (secondDualHom.toFun (4 : Fin 5)).val + 1)]

theorem dualDiagonalSignaturesOneBased_certificate :
    dualDiagonalSignaturesOneBased =
      [(1, 3), (2, 3), (1, 4), (3, 3), (5, 3)] := by
  decide

theorem dualPair_injective :
    Function.Injective fun value =>
      (firstDualHom.toFun value, secondDualHom.toFun value) := by
  intro left right
  revert left right
  decide

/-- The two separating homomorphisms embed `S5_848` into
`(S5_808^op)^2`. -/
def dualRootEmbedding :
    Embedding SemigroupBasis.CoRoots.S5_848.table.semigroup
      (table.semigroup.opposite.pi (Fin 2)) where
  toFun := fun value coordinate =>
    if coordinate = 0 then
      firstDualHom.toFun value
    else
      secondDualHom.toFun value
  map_mul := by
    intro left right
    funext coordinate
    exact by decide +revert
  injective := by
    intro left right equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

/-- Completeness for the first-occurrence dual-root basis on the
opposite of `S5_808`. -/
theorem canonicalOppositeBasisFor :
    BasisFor table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_848.basis :=
  SemigroupBasis.CoRoots.S5_848.representative_basis.inheritAlongPowerEmbedding
    dualRootEmbedding canonicalOppositeModels

/-- Unconditional opposite endpoint with the literal reversed basis. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis :=
  canonicalOppositeBasisFor.replace
    oppositeModels canonicalAxiomsDerive

/-- Unconditional representative endpoint with the exact catalogue basis. -/
theorem representative_basis :
    BasisFor table.semigroup basis := by
  have reversed := opposite_basis.oppositeReversed
  simpa [oppositeBasis] using reversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end SemigroupBasis.CoRoots.S5_808

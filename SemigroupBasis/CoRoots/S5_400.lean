import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_400

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
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
def xyxwy : Word Nat := w 0 [1, 0, 3, 1]
def yxxwy : Word Nat := w 1 [0, 0, 3, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyxzwz : Word Nat := w 0 [1, 0, 2, 3, 2]
def xyzxwz : Word Nat := w 0 [1, 2, 0, 3, 2]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzwxz : Word Nat := w 0 [1, 2, 3, 0, 2]
def xyzwzx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xyzxwy : Word Nat := w 0 [1, 2, 0, 3, 1]
def yxzxwy : Word Nat := w 1 [0, 2, 0, 3, 1]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def yxzxy : Word Nat := w 1 [0, 2, 0, 1]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xzwxz : Word Nat := w 0 [2, 3, 0, 2]
def xzwzx : Word Nat := w 0 [2, 3, 2, 0]
def xzzx : Word Nat := w 0 [2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def firstDeletionLaw : Identity Nat := ⟨xxzwz, xzxwz⟩
def leftDeletionLaw : Identity Nat := ⟨xxzx, xzx⟩
def squareInterchangeLaw : Identity Nat := ⟨xxzz, xzxz⟩
def rightExpansionLaw : Identity Nat := ⟨xyx, xyxx⟩
def rightContextSwapLaw : Identity Nat := ⟨xyxwy, yxxwy⟩
def shortSwapLaw : Identity Nat := ⟨xyxy, yxxy⟩
def mixedDeletionLaw : Identity Nat := ⟨xyxzwz, xyzxwz⟩
def middleDeletionLaw : Identity Nat := ⟨xyxzx, xyzx⟩
def doubledSuffixLaw : Identity Nat := ⟨xyxzz, xyzxz⟩
def longRotationLaw : Identity Nat := ⟨xyzwxz, xyzwzx⟩
def longContextSwapLaw : Identity Nat := ⟨xyzxwy, yxzxwy⟩
def terminalContextSwapLaw : Identity Nat := ⟨xyzxy, yxzxy⟩
def terminalSquareLaw : Identity Nat := ⟨xyzxz, xyzzx⟩
def shortRotationLaw : Identity Nat := ⟨xzwxz, xzwzx⟩
def alternatingSquareLaw : Identity Nat := ⟨xzxz, xzzx⟩

/-- The exact ordered deletion-closure basis shared by catalogue
`S5_400` and `S5_840`. -/
def basis : List (Identity Nat) :=
  [powerLaw, firstDeletionLaw, leftDeletionLaw, squareInterchangeLaw,
    rightExpansionLaw, rightContextSwapLaw, shortSwapLaw,
    mixedDeletionLaw, middleDeletionLaw, doubledSuffixLaw,
    longRotationLaw, longContextSwapLaw, terminalContextSwapLaw,
    terminalSquareLaw, shortRotationLaw, alternatingSquareLaw]

/-- The four laws printed in Edmunds Proposition 3.1(i), before closure
under deletion of variables. -/
def publishedCoreBasis : List (Identity Nat) :=
  [middleDeletionLaw, mixedDeletionLaw, longRotationLaw,
    longContextSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

/-- Convert exhaustive checks on the four displayed variables into a
`Models` theorem over the repository's infinite variable type. -/
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
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Historical tables and exact catalogue identifications -/

/-- Edmunds' `M6` multiplication in historical order `0, 1, a, b, c`.
The nonidentity star table is `000/00b/a0c`. -/
def publishedM6Mul (left right : Fin 5) : Fin 5 :=
  if left = 0 then 0
  else if right = 0 then 0
  else if left = 1 then right
  else if right = 1 then left
  else if left = 2 then 0
  else if left = 3 then
    if right = 4 then 3 else 0
  else if right = 2 then 2
  else if right = 4 then 4
  else 0

def publishedM6Table : FiniteTable where
  order := 5
  mul := publishedM6Mul
  assoc := by decide

/-- Edmunds' `M19` multiplication in historical order `0, 1, a, b, c`.
The nonidentity star table is `00a/ab0/00c`. -/
def publishedM19Mul (left right : Fin 5) : Fin 5 :=
  if left = 0 then 0
  else if right = 0 then 0
  else if left = 1 then right
  else if right = 1 then left
  else if left = 2 then
    if right = 4 then 2 else 0
  else if left = 3 then
    if right = 2 then 2
    else if right = 3 then 3
    else 0
  else if right = 4 then 4
  else 0

def publishedM19Table : FiniteTable where
  order := 5
  mul := publishedM19Mul
  assoc := by decide

/-- Relabel historical order `0, 1, a, b, c` into the Smallsemi order.
In one-based notation this is `[1, 5, 2, 3, 4]`. -/
def historicalToCatalogueValue (value : Fin 5) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 4
  else if value = 2 then 1
  else if value = 3 then 2
  else 3

def catalogueToHistoricalValue (value : Fin 5) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 3
  else if value = 3 then 4
  else 1

def historicalToCatalogueValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (historicalToCatalogueValue value).val + 1

theorem historicalToCatalogueValuesOneBased_certificate :
    historicalToCatalogueValuesOneBased = [1, 5, 2, 3, 4] := by
  decide

@[simp]
theorem catalogueToHistorical_historicalToCatalogue (value : Fin 5) :
    catalogueToHistoricalValue (historicalToCatalogueValue value) =
      value := by
  decide +revert

@[simp]
theorem historicalToCatalogue_catalogueToHistorical (value : Fin 5) :
    historicalToCatalogueValue (catalogueToHistoricalValue value) =
      value := by
  decide +revert

def publishedM6ToCatalogue :
    Embedding publishedM6Table.semigroup
      Generated.Catalogue.S5_400.table.semigroup where
  toFun := historicalToCatalogueValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg catalogueToHistoricalValue equality
    simpa using inverseEquality

def catalogueToPublishedM6 :
    Embedding Generated.Catalogue.S5_400.table.semigroup
      publishedM6Table.semigroup where
  toFun := catalogueToHistoricalValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg historicalToCatalogueValue equality
    simpa using inverseEquality

def publishedM19ToCatalogue :
    Embedding publishedM19Table.semigroup
      Generated.Catalogue.S5_840.table.semigroup where
  toFun := historicalToCatalogueValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg catalogueToHistoricalValue equality
    simpa using inverseEquality

def catalogueToPublishedM19 :
    Embedding Generated.Catalogue.S5_840.table.semigroup
      publishedM19Table.semigroup where
  toFun := catalogueToHistoricalValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg historicalToCatalogueValue equality
    simpa using inverseEquality

set_option maxHeartbeats 2000000 in
theorem publishedM6Models :
    Models publishedM6Table.semigroup basis :=
  models_of_finite_checks publishedM6Table (by decide)

set_option maxHeartbeats 2000000 in
theorem catalogueS5_400Models :
    Models Generated.Catalogue.S5_400.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_400.table (by decide)

set_option maxHeartbeats 2000000 in
theorem publishedM19Models :
    Models publishedM19Table.semigroup basis :=
  models_of_finite_checks publishedM19Table (by decide)

set_option maxHeartbeats 2000000 in
theorem catalogueS5_840Models :
    Models Generated.Catalogue.S5_840.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_840.table (by decide)

/-! ## Exact formal boundary of the published completeness argument -/

/-- The unformalized global content of Edmunds Proposition 3.1(i) for
`M6`. This is a proposition, not an axiom or theorem. -/
def M6CompletenessObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy publishedM6Table.semigroup →
      Derives basis identity.lhs identity.rhs

/-- The unformalized global content of Edmunds Proposition 3.1(i) for
`M19`. This is a proposition, not an axiom or theorem. -/
def M19CompletenessObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy publishedM19Table.semigroup →
      Derives basis identity.lhs identity.rhs

theorem publishedM6BasisFor_of_completeness
    (complete : M6CompletenessObligation) :
    BasisFor publishedM6Table.semigroup basis :=
  ⟨publishedM6Models, complete⟩

theorem catalogueS5_400BasisFor_of_publishedCompleteness
    (complete : M6CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_400.table.semigroup basis :=
  (publishedM6BasisFor_of_completeness complete).inheritAlongEmbedding
    publishedM6ToCatalogue catalogueS5_400Models

theorem publishedM19BasisFor_of_completeness
    (complete : M19CompletenessObligation) :
    BasisFor publishedM19Table.semigroup basis :=
  ⟨publishedM19Models, complete⟩

theorem catalogueS5_840BasisFor_of_publishedCompleteness
    (complete : M19CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_840.table.semigroup basis :=
  (publishedM19BasisFor_of_completeness complete).inheritAlongEmbedding
    publishedM19ToCatalogue catalogueS5_840Models

end SemigroupBasis.CoRoots.S5_400

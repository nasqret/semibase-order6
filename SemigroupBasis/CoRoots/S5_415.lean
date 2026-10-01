import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Nonfinite.GraphParity
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxyx : Word Nat := w 0 [1, 0, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def sandwichLaw : Identity Nat := ⟨xyx, xyxyx⟩
def squareCommutationLaw : Identity Nat := ⟨xxyy, yyxx⟩

/-- Trahtman's published three-identity basis candidate for the
five-element Brandt semigroup `B₂`. -/
def basis : List (Identity Nat) :=
  [powerLaw, sandwichLaw, squareCommutationLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def expectedOppositeBasis : List (Identity Nat) :=
  [powerLaw, sandwichLaw, ⟨yyxx, xxyy⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

/-!
The zero-based catalogue labels are

* `0 = 0`,
* `1 = e₁₂`,
* `2 = e₂₁`,
* `3 = e₁₁`,
* `4 = e₂₂`.
-/

def firstCoordinate (value : Fin 5) : Fin 2 :=
  if value = 1 ∨ value = 3 then 0 else 1

def finalCoordinate (value : Fin 5) : Fin 2 :=
  if value = 2 ∨ value = 3 then 0 else 1

def coordinateValue (first final : Fin 2) : Fin 5 :=
  if first = 0 then
    if final = 0 then 3 else 1
  else
    if final = 0 then 2 else 4

@[simp]
theorem firstCoordinate_coordinateValue (first final : Fin 2) :
    firstCoordinate (coordinateValue first final) = first := by
  decide +revert

@[simp]
theorem finalCoordinate_coordinateValue (first final : Fin 2) :
    finalCoordinate (coordinateValue first final) = final := by
  decide +revert

theorem coordinateValue_ne_zero (first final : Fin 2) :
    coordinateValue first final ≠ (0 : Fin 5) := by
  decide +revert

theorem coordinateValue_eq
    (value : Fin 5) (nonzero : value ≠ 0) :
    coordinateValue (firstCoordinate value) (finalCoordinate value) =
      value := by
  decide +revert

/-- Matrix-unit multiplication reconstructed independently of the generated
catalogue source. -/
def publishedBrandtMul (left right : Fin 5) : Fin 5 :=
  if left = 0 ∨ right = 0 then 0
  else if finalCoordinate left = firstCoordinate right then
    coordinateValue (firstCoordinate left) (finalCoordinate right)
  else
    0

def publishedBrandtTable : FiniteTable where
  order := 5
  mul := publishedBrandtMul
  assoc := by decide

theorem publishedBrandtMul_eq_catalogue (left right : Fin 5) :
    publishedBrandtMul left right =
      Generated.Catalogue.S5_415.mul left right := by
  decide +revert

/-- Exact matrix-unit-to-Smallsemi table identification. -/
theorem publishedBrandtTable_eq_catalogue :
    publishedBrandtTable =
      Generated.Catalogue.S5_415.table := by
  unfold publishedBrandtTable Generated.Catalogue.S5_415.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  exact publishedBrandtMul_eq_catalogue left right

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteSandwichLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 0]⟩⟩

def finiteSquareCommutationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteSandwichLaw_map :
    finiteSandwichLaw.map Fin.val = sandwichLaw := rfl

theorem finiteSquareCommutationLaw_map :
    finiteSquareCommutationLaw.map Fin.val =
      squareCommutationLaw := rfl

/-- Direct finite verification of the three displayed laws. -/
theorem publishedBrandtModels :
    Models publishedBrandtTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact publishedBrandtTable.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteSandwichLaw_map]
    exact publishedBrandtTable.checkIdentityNat_sound
      finiteSandwichLaw (by decide)
  · rw [← finiteSquareCommutationLaw_map]
    exact publishedBrandtTable.checkIdentityNat_sound
      finiteSquareCommutationLaw (by decide)

theorem catalogueModels :
    Models Generated.Catalogue.S5_415.table.semigroup basis := by
  rw [← publishedBrandtTable_eq_catalogue]
  exact publishedBrandtModels

theorem catalogueOppositeModels :
    Models Generated.Catalogue.S5_415.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using catalogueModels.oppositeReversed

/-- Transposition of matrix units, in zero-based catalogue labels. -/
def transposeValue (value : Fin 5) : Fin 5 :=
  if value = 1 then 2
  else if value = 2 then 1
  else value

def transposeValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 => (transposeValue value).val + 1

theorem transposeValuesOneBased_certificate :
    transposeValuesOneBased = [1, 3, 2, 4, 5] := by
  decide

@[simp]
theorem transposeValue_involutive (value : Fin 5) :
    transposeValue (transposeValue value) = value := by
  decide +revert

/-- The audited transposition anti-isomorphism `B₂ᵒᵖ ↪ B₂`. -/
def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_415.table.semigroup.opposite
      Generated.Catalogue.S5_415.table.semigroup where
  toFun := transposeValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have := congrArg transposeValue equality
    simpa using this

/-- The inverse direction of the same transposition isomorphism. -/
def selfDualReverseEmbedding :
    Embedding Generated.Catalogue.S5_415.table.semigroup
      Generated.Catalogue.S5_415.table.semigroup.opposite where
  toFun := transposeValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have := congrArg transposeValue equality
    simpa using this

/-- The representative and its opposite have exactly the same identities. -/
theorem sameIdentityTheory_opposite :
    SameIdentityTheory
      Generated.Catalogue.S5_415.table.semigroup
      Generated.Catalogue.S5_415.table.semigroup.opposite := by
  intro identity
  constructor
  · exact selfDualEmbedding.pullback_identity identity
  · exact selfDualReverseEmbedding.pullback_identity identity

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem powerLaw_mem : powerLaw ∈ basis := by
  simp [basis]

private theorem sandwichLaw_mem : sandwichLaw ∈ basis := by
  simp [basis]

private theorem squareCommutationLaw_mem :
    squareCommutationLaw ∈ basis := by
  simp [basis]

/-- Substitute an arbitrary nonempty word into `x² = x³`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Substitute arbitrary nonempty words into `xyx = xyxyx`. -/
theorem derivesSandwichExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ v) ++ u) := by
  have base : Derives basis xyx xyxyx :=
    Derives.fromBasis (e := sandwichLaw) sandwichLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [sandwichLaw, xyx, xyxyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesSandwichContraction (u v : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) :=
  (derivesSandwichExpansion u v).symm

/-- Substitute arbitrary nonempty words into `x²y² = y²x²`. -/
theorem derivesSquareCommutation (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  have base : Derives basis xxyy yyxx :=
    Derives.fromBasis
      (e := squareCommutationLaw) squareCommutationLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [squareCommutationLaw, xxyy, yyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Volkov's explicit graph-switch consequence
`xyxzx = xzxyx`. The derivation expands both sandwiches, commutes the
two square blocks, and contracts both sandwiches. -/
theorem derivesGraphSwitch (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have expandV :=
    Derives.appendRight (derivesSandwichExpansion u v) (z ++ u)
  have expandZ :=
    Derives.prepend (((u ++ v) ++ u) ++ v)
      (derivesSandwichExpansion u z)
  have commute :=
    Derives.appendRight
      (derivesSquareCommutation (u ++ v) (u ++ z)) u
  have contractZ :=
    Derives.appendRight (derivesSandwichContraction u z)
      (((v ++ u) ++ v) ++ u)
  have contractV :=
    Derives.prepend (u ++ z)
      (derivesSandwichContraction u v)
  apply Derives.trans
  · simpa [Word.append_assoc] using expandV
  · apply Derives.trans
    · simpa [Word.append_assoc] using expandZ
    · apply Derives.trans
      · simpa [Word.append_assoc] using commute
      · apply Derives.trans
        · simpa [Word.append_assoc] using contractZ
        · simpa [Word.append_assoc] using contractV

theorem derivesPublishedGraphSwitch :
    Derives basis xyxzx xzxyx := by
  simpa [xyxzx, xzxyx, w, Word.append, Word.singleton,
    Word.append_assoc] using
      derivesGraphSwitch (Word.singleton 0)
        (Word.singleton 1) (Word.singleton 2)

end SemigroupBasis.CoRoots.S5_415

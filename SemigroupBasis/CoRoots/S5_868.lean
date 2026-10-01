import SemigroupBasis.Examples.AC2Nonfinite
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxyx : Word Nat := w 0 [1, 0, 1, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
def xyxzxyx : Word Nat := w 0 [1, 0, 2, 0, 1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def sandwichLaw : Identity Nat := ⟨xyx, xyxyx⟩
def graphSwitchLaw : Identity Nat := ⟨xyxzx, xzxyx⟩

/-- Trahtman's exact irreducible basis for the five-element zero-simple
semigroup represented by catalogue class `S5_868`. -/
def basis : List (Identity Nat) :=
  [powerLaw, sandwichLaw, graphSwitchLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def expectedOppositeBasis : List (Identity Nat) :=
  [powerLaw, sandwichLaw, ⟨xzxyx, xyxzx⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

/-!
The existing `A₂` table in `Examples.AC2Nonfinite` is byte-for-byte the
catalogue table. Its source order is `0, p, pq, q, qp`. Trahtman's published
generators use the equally valid assignment

* `0 = 0`,
* `a = qp = 4`,
* `b = p = 1`,
* `ab = q = 3`,
* `ba = pq = 2`.

The following constants use zero-based Lean labels; the certificate list is
one-based, matching the research metadata and promotion script.
-/

def zero : Fin 5 := 0
def publishedA : Fin 5 := 4
def publishedB : Fin 5 := 1
def publishedAB : Fin 5 := 3
def publishedBA : Fin 5 := 2

def presentationValuesOneBased : List Nat :=
  [zero.val + 1, publishedA.val + 1, publishedB.val + 1,
    publishedAB.val + 1, publishedBA.val + 1]

theorem presentationValuesOneBased_certificate :
    presentationValuesOneBased = [1, 5, 2, 4, 3] := by
  decide

/-- Kernel-checkable version of the presentation checks performed by
`scripts/promote_trahtman_zero_simple_semigroup.py`. -/
theorem publishedPresentation_relations :
    SemigroupBasis.Examples.AC2.a2Mul publishedA publishedA = publishedA ∧
    SemigroupBasis.Examples.AC2.a2Mul publishedB publishedB = zero ∧
    SemigroupBasis.Examples.AC2.a2Mul
        (SemigroupBasis.Examples.AC2.a2Mul publishedA publishedB)
        publishedA = publishedA ∧
    SemigroupBasis.Examples.AC2.a2Mul
        (SemigroupBasis.Examples.AC2.a2Mul publishedB publishedA)
        publishedB = publishedB ∧
    SemigroupBasis.Examples.AC2.a2Mul publishedA publishedB =
      publishedAB ∧
    SemigroupBasis.Examples.AC2.a2Mul publishedB publishedA =
      publishedBA ∧
    (∀ value : Fin 5,
      SemigroupBasis.Examples.AC2.a2Mul zero value = zero ∧
        SemigroupBasis.Examples.AC2.a2Mul value zero = zero) := by
  decide

theorem a2Mul_eq_catalogue (left right : Fin 5) :
    SemigroupBasis.Examples.AC2.a2Mul left right =
      Generated.Catalogue.S5_868.mul left right := by
  decide +revert

/-- Exact identification of the published five-element `A₂` table with
Smallsemi catalogue representative `S5_868`. -/
theorem a2Table_eq_catalogue :
    SemigroupBasis.Examples.AC2.a2Table =
      Generated.Catalogue.S5_868.table := by
  unfold SemigroupBasis.Examples.AC2.a2Table
    Generated.Catalogue.S5_868.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  exact a2Mul_eq_catalogue left right

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteSandwichLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 0]⟩⟩

def finiteGraphSwitchLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [2, 0, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteSandwichLaw_map :
    finiteSandwichLaw.map Fin.val = sandwichLaw := rfl

theorem finiteGraphSwitchLaw_map :
    finiteGraphSwitchLaw.map Fin.val = graphSwitchLaw := rfl

/-- Direct finite verification that the exact table models all three
published laws. -/
theorem publishedA2Models :
    Models SemigroupBasis.Examples.AC2.a2Table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact
      SemigroupBasis.Examples.AC2.a2Table.checkIdentityNat_sound
        finitePowerLaw (by decide)
  · rw [← finiteSandwichLaw_map]
    exact
      SemigroupBasis.Examples.AC2.a2Table.checkIdentityNat_sound
        finiteSandwichLaw (by decide)
  · rw [← finiteGraphSwitchLaw_map]
    exact
      SemigroupBasis.Examples.AC2.a2Table.checkIdentityNat_sound
        finiteGraphSwitchLaw (by decide)

theorem catalogueModels :
    Models Generated.Catalogue.S5_868.table.semigroup basis := by
  rw [← a2Table_eq_catalogue]
  exact publishedA2Models

theorem catalogueOppositeModels :
    Models Generated.Catalogue.S5_868.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using catalogueModels.oppositeReversed

/-! ## Explicit instances of the three graph rewrites -/

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

private theorem graphSwitchLaw_mem : graphSwitchLaw ∈ basis := by
  simp [basis]

/-- Substitute an arbitrary nonempty word into `x² = x³`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base
      (instantiateThreeWords u (Word.singleton 1) (Word.singleton 2))
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract three consecutive copies of a nonempty block to two. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Substitute arbitrary nonempty words into `xyx = xyxyx`. This duplicates
an anchored closed walk. -/
theorem derivesSandwichExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ v) ++ u) := by
  have base : Derives basis xyx xyxyx :=
    Derives.fromBasis (e := sandwichLaw) sandwichLaw_mem
  have substituted :=
    Derives.subst base
      (instantiateThreeWords u v (Word.singleton 2))
  simpa [sandwichLaw, xyx, xyxyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Remove one repeated anchored loop, the reverse use of
`xyx = xyxyx`. -/
theorem derivesSandwichContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) :=
  (derivesSandwichExpansion u v).symm

/-- Substitute arbitrary nonempty words into `xyxzx = xzxyx`. This swaps
two anchored closed walks. -/
theorem derivesAnchoredLoopSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have base : Derives basis xyxzx xzxyx :=
    Derives.fromBasis (e := graphSwitchLaw) graphSwitchLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [graphSwitchLaw, xyxzx, xzxyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Trahtman's derived contraction
`xyxzxyx = xyxzx`, with arbitrary nonempty blocks substituted for the
variables. The first switch moves the repeated `y`-loop next to its earlier
copy, the sandwich law contracts it, and the reverse switch restores the
original loop order. -/
theorem derivesAnchoredLoopContraction (u v z : Word Nat) :
    Derives basis
      ((((((u ++ v) ++ u) ++ z) ++ u) ++ v) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have first :=
    Derives.appendRight (derivesAnchoredLoopSwap u v z) (v ++ u)
  have second :=
    Derives.prepend (u ++ z) (derivesSandwichContraction u v)
  have third :=
    Derives.symm (derivesAnchoredLoopSwap u v z)
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · simpa [Word.append_assoc] using third

theorem derivesPublishedAnchoredLoopContraction :
    Derives basis xyxzxyx xyxzx := by
  simpa [xyxzxyx, xyxzx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      derivesAnchoredLoopContraction
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

/-- One of the two longer bounded-candidate laws eliminated by Trahtman's
irreducible basis: `x²yx = xyx²`. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) := by
  have expand :=
    Derives.appendRight (derivesPowerExpansion u) (v ++ u)
  have swap := derivesAnchoredLoopSwap u u v
  have contract :=
    Derives.prepend (u ++ v)
      (Derives.symm (derivesPowerExpansion u))
  apply Derives.trans
  · simpa [Word.append_assoc] using expand
  · apply Derives.trans
    · simpa [Word.append_assoc] using swap
    · simpa [Word.append_assoc] using contract

theorem derivesPublishedEndpointTransfer :
    Derives basis xxyx xyxx := by
  simpa [xxyx, xyxx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      derivesEndpointTransfer (Word.singleton 0) (Word.singleton 1)

/-! ## Self-duality -/

/-- Transposition of the Rees coordinates. It swaps catalogue values `2`
and `3`, fixing `0`, `1`, and `4`. -/
def transposeValue (value : Fin 5) : Fin 5 :=
  if value = 2 then 3
  else if value = 3 then 2
  else value

def transposeValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 => (transposeValue value).val + 1

theorem transposeValuesOneBased_certificate :
    transposeValuesOneBased = [1, 2, 4, 3, 5] := by
  decide

@[simp]
theorem transposeValue_involutive (value : Fin 5) :
    transposeValue (transposeValue value) = value := by
  decide +revert

/-- The concrete anti-isomorphism from `S5_868ᵒᵖ` to `S5_868`. -/
def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_868.table.semigroup.opposite
      Generated.Catalogue.S5_868.table.semigroup where
  toFun := transposeValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg transposeValue equality
    simpa using inverseEquality

/-- The inverse anti-isomorphism, exposed separately so both identity-theory
inclusions are kernel-visible. -/
def selfDualEmbeddingReverse :
    Embedding Generated.Catalogue.S5_868.table.semigroup
      Generated.Catalogue.S5_868.table.semigroup.opposite where
  toFun := transposeValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg transposeValue equality
    simpa using inverseEquality

theorem sameIdentityTheory_opposite :
    SameIdentityTheory
      Generated.Catalogue.S5_868.table.semigroup
      Generated.Catalogue.S5_868.table.semigroup.opposite := by
  intro identity
  constructor
  · exact selfDualEmbedding.pullback_identity identity
  · exact selfDualEmbeddingReverse.pullback_identity identity

end SemigroupBasis.CoRoots.S5_868

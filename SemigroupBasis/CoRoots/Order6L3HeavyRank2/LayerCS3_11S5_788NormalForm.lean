import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788Derivations
import SemigroupBasis.CoRoots.S5_441ExactCutAlignment

/-!
# Deterministic C2 parity/separator/initial render

The semantic normal list retains every exact unique separator.  Within each
nonempty support gap it retains its first-occurrence anchor at both endpoints;
the interior contains that anchor once exactly when its multiplicity is odd.
Every other supported letter appears once for odd multiplicity or twice for
positive even multiplicity.  The endpoint anchor is essential: without it,
the former unanchored render turns `xxyx` into `xy` and creates two new exact
cuts rejected by `S5_788`.  Reachability is proved separately; this module
isolates the arbitrary-word uniqueness calculation.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis
open SemigroupBasis.Examples

/-- Render one supported letter from its pointwise parity coordinate. -/
def parityMultiplicityBlock
    (parity : Nat → Nat) (letter : Nat) : List Nat :=
  if parity letter = 0 then [letter, letter] else [letter]

/-- Render a separator-free support gap while retaining its first letter at
both endpoints.  The endpoint pair prevents the introduction of new exact
cuts; the optional interior anchor corrects its parity. -/
def renderParitySeparatorInitialGap
    (initials : List Nat) (parity : Nat → Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  match initials.filter fun letter =>
      decide (letter ∈ segment.quadratic) with
  | [] => []
  | anchor :: remaining =>
      [anchor] ++
        (if parity anchor = 0 then [] else [anchor]) ++
        remaining.flatMap (parityMultiplicityBlock parity) ++
        [anchor]

/-- Render one anchored exact-cut support segment in restricted initial
order, retaining its original optional separator. -/
def renderParitySeparatorInitialSegment
    (initials : List Nat) (parity : Nat → Nat)
    (segment : UniqueSeparatorCanonicalSegment) : List Nat :=
  renderParitySeparatorInitialGap initials parity segment ++
    segment.separator.toList

/-- The deterministic list representative of the exact C2 descriptor. -/
def paritySeparatorInitialNormalList (word : Word Nat) : List Nat :=
  (SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton word.toList).flatMap
    (renderParitySeparatorInitialSegment
      (firstOccurrenceSequence word.toList)
      (fun letter => word.toList.count letter % 2))

/-- Permanent regression for the falsified unanchored candidate: `xxyx`
must retain its closing `x`, rather than collapsing to `xy`. -/
theorem paritySeparatorInitialNormalList_xxyx_regression :
    paritySeparatorInitialNormalList (Word.mk 0 [0, 1, 0]) =
      [0, 0, 1, 0] := by
  simp [paritySeparatorInitialNormalList,
    renderParitySeparatorInitialSegment,
    renderParitySeparatorInitialGap, parityMultiplicityBlock,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment,
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition,
    SemigroupBasis.CoRoots.S5_441.exactCutScanner,
    SemigroupBasis.CoRoots.S5_441.exactCutSupportsDisjointBool,
    connectedComponentSortedSupport,
    connectedComponentDistinctSupport,
    firstOccurrenceSequence, Word.toList, List.mergeSort]

/-- Every genuine C2 displayed-law derivation preserves the complete
right-factor exact-cut skeleton.  The repaired render's reachability proof
must therefore discharge this invariant rather than silently assume it. -/
theorem exactCutSupportSkeleton_eq_of_target_derives
    {left right : Word Nat}
    (derivation : Derives targetBasis left right) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton left.toList =
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton right.toList := by
  let identity : Identity Nat := ⟨left, right⟩
  have valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup := by
    intro valuation
    exact Derives.sound targetModelsRight derivation valuation
  have same :=
    SemigroupBasis.CoRoots.S5_788FamilyInvariant.S5_788.valid_sameSignature
      identity valid
  exact
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
      same.support same.exactCuts

/-- The exact factor signature uniquely determines the C2 normal list. -/
theorem paritySeparatorInitialNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameParitySeparatorInitialSignature left right) :
    paritySeparatorInitialNormalList left =
      paritySeparatorInitialNormalList right := by
  have skeletonEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton left.toList =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton right.toList :=
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
      same.support same.exactCuts
  have parityEq :
      (fun letter => left.toList.count letter % 2) =
        (fun letter => right.toList.count letter % 2) := by
    funext letter
    exact same.parity letter
  unfold paritySeparatorInitialNormalList
  rw [same.initials, skeletonEq, parityEq]

/-- Factor validity therefore fixes the same deterministic C2 normal list. -/
theorem paritySeparatorInitialNormalList_eq_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup) :
    paritySeparatorInitialNormalList identity.lhs =
      paritySeparatorInitialNormalList identity.rhs :=
  paritySeparatorInitialNormalList_eq_of_sameSignature
    (sameSignature_of_factor_valid identity leftValid rightValid)

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

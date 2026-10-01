import SemigroupBasis.CoRoots.S5_400
import SemigroupBasis.CoRoots.S5_793Invariant
import SemigroupBasis.CoRoots.S5_794Derivations
import SemigroupBasis.CoRoots.S5_841QuadraticSwap
import SemigroupBasis.Examples.UniqueSeparatorFourSortDerives

namespace SemigroupBasis.CoRoots.S5_400

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives :
    List (Identity Nat) → List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives

/-! ## Replaying the two deletion-closure halves -/

/-- The twelve `M14` deletion laws are a literal sublist, up to definitional
equality of the separately named word constants, of the sixteen-law system. -/
private theorem m14BasisSubset
    {identity : Identity Nat}
    (member : identity ∈ SemigroupBasis.CoRoots.S5_794.basis) :
    identity ∈ basis := by
  simp only [SemigroupBasis.CoRoots.S5_794.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The twelve `M20` deletion laws are the complementary literal sublist of
the sixteen-law system. -/
private theorem m20BasisSubset
    {identity : Identity Nat}
    (member : identity ∈ SemigroupBasis.CoRoots.S5_841.basis) :
    identity ∈ basis := by
  simp only [SemigroupBasis.CoRoots.S5_841.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem transportM14Derives
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_794.basis left right) :
    Derives basis left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (m14BasisSubset member)

private theorem transportM20Derives
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_841.basis left right) :
    Derives basis left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (m20BasisSubset member)

private theorem transportListDerives
    {source : List (Identity Nat)}
    (axiomDerives :
      ∀ identity : Identity Nat, identity ∈ source →
        Derives basis identity.lhs identity.rhs)
    {left right : List Nat}
    (derivation : ListDerives source left right) :
    ListDerives basis left right := by
  cases derivation with
  | empty => exact .empty
  | words wordDerivation =>
      exact .words (wordDerivation.transport axiomDerives)

private theorem transportM14ListDerives
    {left right : List Nat}
    (derivation :
      ListDerives SemigroupBasis.CoRoots.S5_794.basis left right) :
    ListDerives basis left right :=
  transportListDerives
    (fun identity member => Derives.fromBasis (m14BasisSubset member))
    derivation

private theorem transportM20ListDerives
    {left right : List Nat}
    (derivation :
      ListDerives SemigroupBasis.CoRoots.S5_841.basis left right) :
    ListDerives basis left right :=
  transportListDerives
    (fun identity member => Derives.fromBasis (m20BasisSubset member))
    derivation

/-- Edmunds' repeated use of `xyxzx = xyzx`, including all empty-gap
deletions, retains exactly the first and last occurrence of each variable. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    ListDerives basis letters (uniqueSeparatorEndpointCap letters) :=
  transportM20ListDerives
    (SemigroupBasis.CoRoots.S5_841.listDerivesTwoLimitedReduction letters)

/-- The four `L6` deletion cases, replayed from the `M20` half. -/
theorem listDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    ListDerives basis
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) :=
  transportM20ListDerives
    (SemigroupBasis.CoRoots.S5_841.listDerivesL6 x y middle tail)

/-- The four `L7` deletion cases, replayed from the `M14` half. -/
theorem listDerivesL7
    (x y : Nat) (left right : List Nat) :
    ListDerives basis
      ([x] ++ left ++ [y, x] ++ right ++ [y])
      ([x] ++ left ++ [x, y] ++ right ++ [y]) :=
  transportM14ListDerives
    (SemigroupBasis.CoRoots.S5_794.listDerivesL7 x y left right)

/-- The four `L8` deletion cases, replayed from the `M20` half. -/
theorem listDerivesL8
    (x y : Nat) (left middle : List Nat) :
    ListDerives basis
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) :=
  transportM20ListDerives
    (SemigroupBasis.CoRoots.S5_841.listDerivesL8 x y left middle)

/-! ## The six quadratic swap positions -/

abbrev QuadraticSwapPosition :
    Nat → Nat → List Nat → List Nat → Prop :=
  UniqueSeparatorAdjacentQuadraticPosition

/-- Each of the six possible positions of the other occurrences is handled by
one of Edmunds' `L6`, `L7`, or `L8` deletion families. -/
theorem listDerivesAdjacentOfPosition
    {x y : Nat} {pre post : List Nat}
    (position : QuadraticSwapPosition x y pre post) :
    ListDerives basis
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) := by
  cases position with
  | futureXY middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        (listDerivesL6 x y middle between).context pre after
  | futureYX middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        (listDerivesL6 y x middle between).symm.context pre after
  | straddleXY before left right after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        (listDerivesL7 x y left right).symm.context before after
  | straddleYX before left right after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        (listDerivesL7 y x left right).context before after
  | pastXY before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        (listDerivesL8 x y left middle).context before post
  | pastYX before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        (listDerivesL8 y x left middle).symm.context before post

/-- Adjacent distinct globally quadratic letters can always be interchanged.
This is the formal six-case step in Edmunds' canonical-form argument. -/
theorem listDerivesAdjacentQuadraticSwap
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2) :
    ListDerives basis
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) :=
  listDerivesAdjacentOfPosition
    (uniqueSeparatorAdjacentQuadraticPosition_of_counts
      different xQuadratic yQuadratic)

/-- Any permutation of one quadratic block is a derivation. The proof is the
permutation induction implicit in Edmunds' phrase "successive interchange of
adjacent letters". -/
theorem listDerivesQuadraticPermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ∀ (pre post : List Nat),
      (∀ letter ∈ source,
        (pre ++ source ++ post).count letter = 2) →
      ListDerives basis
        (pre ++ source ++ post)
        (pre ++ target ++ post) := by
  induction permutation with
  | nil =>
      intro pre post _
      simpa using
        S5_107.ListDerives.refl (basis := basis) (pre ++ post)
  | @cons letter source target permutation induction =>
      intro pre post quadratic
      have tailQuadratic :
          ∀ selected ∈ source,
            ((pre ++ [letter]) ++ source ++ post).count selected = 2 := by
        intro selected member
        have count := quadratic selected (List.mem_cons_of_mem letter member)
        simpa [List.append_assoc] using count
      simpa [List.append_assoc] using
        induction (pre ++ [letter]) post tailQuadratic
  | swap x y rest =>
      intro pre post quadratic
      by_cases equal : y = x
      · subst y
        simpa [List.append_assoc] using
          S5_107.ListDerives.refl (basis := basis)
            (pre ++ x :: x :: rest ++ post)
      · have yQuadratic :
            (pre ++ (y :: x :: (rest ++ post))).count y = 2 := by
          simpa [List.append_assoc] using quadratic y (by simp)
        have xQuadratic :
            (pre ++ (y :: x :: (rest ++ post))).count x = 2 := by
          simpa [List.append_assoc] using quadratic x (by simp)
        simpa [List.append_assoc] using
          listDerivesAdjacentQuadraticSwap
            (pre := pre) (post := rest ++ post)
            equal yQuadratic xQuadratic
  | @trans source middle target first second firstInduction secondInduction =>
      intro pre post quadratic
      have firstStep := firstInduction pre post quadratic
      have middleQuadratic :
          ∀ letter ∈ middle,
            (pre ++ middle ++ post).count letter = 2 := by
        intro letter member
        have sourceMember : letter ∈ source := first.mem_iff.mpr member
        have sourceCount := quadratic letter sourceMember
        have countEquality :
            (pre ++ source ++ post).count letter =
              (pre ++ middle ++ post).count letter := by
          simp only [List.count_append]
          rw [first.count letter]
        rw [← countEquality]
        exact sourceCount
      exact firstStep.trans
        (secondInduction pre post middleQuadratic)

/-! ## Deterministic canonical blocks -/

/-- Sort every globally quadratic block while retaining every globally linear
letter in place. -/
def canonicalSegments (letters : List Nat) :
    List UniqueSeparatorSquareSegment :=
  uniqueSeparatorSortSquareSegments
    (uniqueSeparatorSplitLinear (uniqueSeparatorEndpointCap letters))

/-- Edmunds' canonical list: retain first and last occurrences, split at
linear letters, then sort each intervening quadratic block. -/
def canonicalList (letters : List Nat) : List Nat :=
  uniqueSeparatorRenderSquareSegments (canonicalSegments letters)

private theorem listDerivesSortSegment
    (segment : UniqueSeparatorSquareSegment)
    (pre post : List Nat)
    (quadratic :
      ∀ letter ∈ segment.quadratic,
        (pre ++ segment.render ++ post).count letter = 2) :
    ListDerives basis
      (pre ++ segment.render ++ post)
      (pre ++
        (uniqueSeparatorSortSquareSegment segment).render ++ post) := by
  have blockDerivation :=
    listDerivesQuadraticPermutation
      (uniqueSeparatorSortQuadratic_perm segment.quadratic).symm
      pre (segment.separator.toList ++ post)
      (by
        intro letter member
        simpa [UniqueSeparatorSquareSegment.render,
          List.append_assoc] using quadratic letter member)
  simpa [UniqueSeparatorSquareSegment.render,
    uniqueSeparatorSortSquareSegment,
    List.append_assoc] using blockDerivation

private theorem listDerivesSortSegmentsInContext :
    ∀ (segments : List UniqueSeparatorSquareSegment)
      (pre post : List Nat),
      (∀ segment ∈ segments, ∀ letter ∈ segment.quadratic,
        (pre ++
          uniqueSeparatorRenderSquareSegments segments ++ post).count
            letter = 2) →
      ListDerives basis
        (pre ++ uniqueSeparatorRenderSquareSegments segments ++ post)
        (pre ++
          uniqueSeparatorRenderSquareSegments
            (uniqueSeparatorSortSquareSegments segments) ++ post)
  | [], pre, post, _ => by
      simpa [uniqueSeparatorSortSquareSegments,
        uniqueSeparatorRenderSquareSegments] using
          S5_107.ListDerives.refl (basis := basis) (pre ++ post)
  | segment :: rest, pre, post, quadratic => by
      let sortedSegment := uniqueSeparatorSortSquareSegment segment
      have segmentQuadratic :
          ∀ letter ∈ segment.quadratic,
            (pre ++ segment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post)).count
                letter = 2 := by
        intro letter member
        simpa [uniqueSeparatorRenderSquareSegments,
          List.append_assoc] using
            quadratic segment (by simp) letter member
      have firstStep :
          ListDerives basis
            (pre ++ segment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post))
            (pre ++ sortedSegment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post)) := by
        simpa [sortedSegment] using
          listDerivesSortSegment segment pre
            (uniqueSeparatorRenderSquareSegments rest ++ post)
            segmentQuadratic
      have restQuadratic :
          ∀ candidate ∈ rest, ∀ letter ∈ candidate.quadratic,
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count
                letter = 2 := by
        intro candidate candidateMember letter member
        have originalCount :
            (pre ++ segment.render ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count
                letter = 2 := by
          simpa [uniqueSeparatorRenderSquareSegments,
            List.append_assoc] using
              quadratic candidate (by simp [candidateMember]) letter member
        have countEquality :
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count
                letter =
              (pre ++ segment.render ++
                uniqueSeparatorRenderSquareSegments rest ++ post).count
                  letter := by
          simp only [List.count_append]
          rw [show sortedSegment.render.count letter =
              segment.render.count letter by
            exact
              (uniqueSeparatorSortSquareSegment_render_perm segment).count
                letter]
        exact countEquality.trans originalCount
      have restStep :=
        listDerivesSortSegmentsInContext
          rest (pre ++ sortedSegment.render) post restQuadratic
      have firstStep' :
          ListDerives basis
            (pre ++ segment.render ++
              uniqueSeparatorRenderSquareSegments rest ++ post)
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post) := by
        simpa [List.append_assoc] using firstStep
      simpa [sortedSegment, uniqueSeparatorSortSquareSegments,
        uniqueSeparatorRenderSquareSegments,
        List.append_assoc] using firstStep'.trans restStep

/-- Every two-limited word derives to the result of sorting all of its
quadratic blocks. -/
theorem listDerivesSortSplitLinear
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters) :
    ListDerives basis letters
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments
          (uniqueSeparatorSplitLinear letters))) := by
  have derivation :=
    listDerivesSortSegmentsInContext
      (uniqueSeparatorSplitLinear letters) [] []
      (by
        intro segment segmentMember letter member
        rw [uniqueSeparatorRender_splitLinear letters]
        simpa using uniqueSeparatorSplitLinear_quadratic_count_two
          letters limited segment segmentMember letter member)
  simpa [uniqueSeparatorRender_splitLinear letters] using derivation

/-- The complete common normalization half of Proposition 3.1(i). -/
theorem listDerivesCanonical (letters : List Nat) :
    ListDerives basis letters (canonicalList letters) := by
  exact (listDerivesEndpointCap letters).trans <| by
    simpa [canonicalList, canonicalSegments] using
      listDerivesSortSplitLinear
        (uniqueSeparatorEndpointCap letters)
        (uniqueSeparatorEndpointCap_twoLimited letters)

/-- Equality of the deterministic canonical lists is sufficient for a word
derivation. This isolates table separation from the shared syntactic replay. -/
theorem derivesOfCanonicalListEq
    {left right : Word Nat}
    (equal : canonicalList left.toList = canonicalList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          obtain
            ⟨leftNormalHead, leftNormalTail, leftShape, leftDerivation⟩ :=
            (listDerivesCanonical (leftHead :: leftTail)).from_cons
          obtain
            ⟨rightNormalHead, rightNormalTail, rightShape,
              rightDerivation⟩ :=
            (listDerivesCanonical (rightHead :: rightTail)).from_cons
          have normalWordsEqual :
              S5_107.listWordOfCons leftNormalHead leftNormalTail =
                S5_107.listWordOfCons rightNormalHead rightNormalTail := by
            apply Word.toList_injective
            simpa [S5_107.listWordOfCons, Word.toList,
              ← leftShape, ← rightShape] using equal
          cases normalWordsEqual
          exact leftDerivation.trans rightDerivation.symm

/-! ## Remaining table-separation boundary -/

/-! The five inequalities used by Edmunds are packaged here through the
direct and opposite `S4_71` subsemigroups. The direct factor records capped
multiplicity, the order of globally linear variables, and last-occurrence
gaps. The opposite factor records the corresponding first-occurrence gaps. -/

/-- The `S4_71` submonoid `{0,a,c,1}` of historical `M6`, in catalogue
coordinates. -/
def m6S4_71Embedding :
    Embedding Generated.S4_71.table.semigroup
      publishedM6Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨4, by decide⟩
    else ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The opposite `S4_71` submonoid `{0,b,c,1}` of historical `M6`. -/
def m6S4_71OppositeEmbedding :
    Embedding Generated.S4_71.table.semigroup.opposite
      publishedM6Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨3, by decide⟩
    else if value.val = 2 then ⟨4, by decide⟩
    else ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The `S4_71` submonoid `{0,a,b,1}` of historical `M19`. -/
def m19S4_71Embedding :
    Embedding Generated.S4_71.table.semigroup
      publishedM19Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The opposite `S4_71` submonoid `{0,a,c,1}` of historical `M19`. -/
def m19S4_71OppositeEmbedding :
    Embedding Generated.S4_71.table.semigroup.opposite
      publishedM19Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨4, by decide⟩
    else ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem m6Valid_s4_71
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM6Table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  m6S4_71Embedding.pullback_identity identity valid

theorem m6Valid_s4_71Opposite
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM6Table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup.opposite :=
  m6S4_71OppositeEmbedding.pullback_identity identity valid

theorem m19Valid_s4_71
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM19Table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  m19S4_71Embedding.pullback_identity identity valid

theorem m19Valid_s4_71Opposite
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM19Table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup.opposite :=
  m19S4_71OppositeEmbedding.pullback_identity identity valid

/-- The exact occurrence data determining Edmunds' sorted quadratic-block
canonical form. `firstGap` is expressed as a last-gap statement after word
reversal. -/
structure SameCanonicalSignature (left right : Word Nat) : Prop where
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleSequence :
    ∀ x y,
      S5_793Invariant.SimplePrecedes left x y ↔
        S5_793Invariant.SimplePrecedes right x y
  lastGap :
    ∀ x y,
      S5_793Invariant.MultipleLastBeforeSimple left x y ↔
        S5_793Invariant.MultipleLastBeforeSimple right x y
  firstGap :
    ∀ x y,
      S5_793Invariant.MultipleLastBeforeSimple left.reverse x y ↔
        S5_793Invariant.MultipleLastBeforeSimple right.reverse x y

/-- Direct and opposite `S4_71` validity imply the complete canonical
signature used by Proposition 3.1(i). -/
theorem sameCanonicalSignature_of_s4_71_factors
    (identity : Identity Nat)
    (directValid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (oppositeValid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup.opposite) :
    SameCanonicalSignature identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity directValid letter
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.S4_71.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity Generated.S4_71.table.semigroup).mp oppositeValid
  have reversedCapped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.reversed.lhs letter =
          S5_107.cappedMultiplicity identity.reversed.rhs letter :=
    fun letter =>
      S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity.reversed reversedValid letter
  refine ⟨capped, ?_, ?_, ?_⟩
  · intro x y
    exact S5_793Invariant.s4_71Valid_simplePrecedes
      identity directValid capped x y
  · intro x y
    exact S5_793Invariant.s4_71Valid_multipleLastBeforeSimple
      identity directValid capped x y
  · intro x y
    simpa [Identity.reversed] using
      (S5_793Invariant.s4_71Valid_multipleLastBeforeSimple
        identity.reversed reversedValid reversedCapped x y)

theorem m6Valid_sameCanonicalSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM6Table.semigroup) :
    SameCanonicalSignature identity.lhs identity.rhs :=
  sameCanonicalSignature_of_s4_71_factors identity
    (m6Valid_s4_71 identity valid)
    (m6Valid_s4_71Opposite identity valid)

theorem m19Valid_sameCanonicalSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM19Table.semigroup) :
    SameCanonicalSignature identity.lhs identity.rhs :=
  sameCanonicalSignature_of_s4_71_factors identity
    (m19Valid_s4_71 identity valid)
    (m19Valid_s4_71Opposite identity valid)

/-- The single remaining combinatorial theorem: capped multiplicities, the
ordered linear sequence, and all first/last quadratic gaps determine the
sorted canonical list. -/
def CanonicalSignatureSufficiencyObligation : Prop :=
  ∀ {left right : Word Nat},
    SameCanonicalSignature left right →
      canonicalList left.toList = canonicalList right.toList

/-- A table has Edmunds' canonical uniqueness property when every identity
valid in the table has equal deterministic canonical lists. -/
def CanonicalUniquenessFor {S : Type} (semigroup : Semigroup S) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy semigroup →
      canonicalList identity.lhs.toList =
        canonicalList identity.rhs.toList

/-- The remaining `M6` content is now only the uniqueness of canonical forms,
corresponding to the five explicit nonidentities at the end of Edmunds'
Proposition 3.1(i) proof. -/
def M6CanonicalUniquenessObligation : Prop :=
  CanonicalUniquenessFor publishedM6Table.semigroup

/-- The analogous remaining table-separation statement for `M19`. -/
def M19CanonicalUniquenessObligation : Prop :=
  CanonicalUniquenessFor publishedM19Table.semigroup

theorem m6CanonicalUniqueness_of_signatureSufficiency
    (sufficient : CanonicalSignatureSufficiencyObligation) :
    M6CanonicalUniquenessObligation := by
  intro identity valid
  exact sufficient (m6Valid_sameCanonicalSignature identity valid)

theorem m19CanonicalUniqueness_of_signatureSufficiency
    (sufficient : CanonicalSignatureSufficiencyObligation) :
    M19CanonicalUniquenessObligation := by
  intro identity valid
  exact sufficient (m19Valid_sameCanonicalSignature identity valid)

theorem m6Completeness_of_canonicalUniqueness
    (unique : M6CanonicalUniquenessObligation) :
    M6CompletenessObligation := by
  intro identity valid
  exact derivesOfCanonicalListEq (unique identity valid)

theorem m19Completeness_of_canonicalUniqueness
    (unique : M19CanonicalUniquenessObligation) :
    M19CompletenessObligation := by
  intro identity valid
  exact derivesOfCanonicalListEq (unique identity valid)

theorem m6Completeness_of_signatureSufficiency
    (sufficient : CanonicalSignatureSufficiencyObligation) :
    M6CompletenessObligation :=
  m6Completeness_of_canonicalUniqueness
    (m6CanonicalUniqueness_of_signatureSufficiency sufficient)

theorem m19Completeness_of_signatureSufficiency
    (sufficient : CanonicalSignatureSufficiencyObligation) :
    M19CompletenessObligation :=
  m19Completeness_of_canonicalUniqueness
    (m19CanonicalUniqueness_of_signatureSufficiency sufficient)

end SemigroupBasis.CoRoots.S5_400

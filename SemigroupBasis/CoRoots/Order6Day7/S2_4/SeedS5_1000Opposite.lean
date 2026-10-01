import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank007
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_1000Invariant
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Examples.CommutativePositiveModThreeFour

/-!
# An unrestricted `S2_4 × S5_1000ᵒᵖ` family seed

The rank-007 shell authenticates only finite soundness and split-subdirect
maps.  Its missing unrestricted argument is supplied here: the left-zero
factor fixes the initial variable, while the opposite `S5_1000` factor
separates support, multiplicity modulo three, and the globally simple initial
variable.  The two displayed contextual laws normalize the entire tail to its
positive modulo-three multiset without changing the initial variable.

Both staged six-element classes consequently receive unconditional endpoints.
The quotient-normalizer adapter is applied only after independent unrestricted
factor-intersection completeness; transport keeps all semantic implications
and displayed-law derivations explicit.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank007.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed `xy = xyyyy` expands a nonempty block behind its prefix. -/
theorem derivesTailExpansion (stem repeated : Word Nat) :
    Derives basis
      (stem ++ repeated)
      ((((stem ++ repeated) ++ repeated) ++ repeated) ++ repeated) := by
  have primitive :
      Derives basis (Word.mk 0 [1]) (Word.mk 0 [1, 1, 1, 1]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree stem repeated repeated)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyz = xzy` swaps arbitrary nonempty suffix blocks. -/
theorem derivesSuffixSwap (stem first second : Word Nat) :
    Derives basis
      ((stem ++ first) ++ second)
      ((stem ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree stem first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Replay the independently complete positive-modulo-three calculus strictly
behind a fixed nonempty prefix.  Arbitrary substitutions remain explicit. -/
theorem liftPositiveModThree
    {left right : Word Nat}
    (derivation : Derives commutativePositiveModThreeBasis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [commutativePositiveModThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [positiveModThreePowerLaw, positiveModThreeX,
          positiveModThreeXXXX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesTailExpansion stem (substitution 0)
      · simpa [positiveModThreeCommutativityLaw, positiveModThreeXY,
          positiveModThreeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesSuffixSwap stem (substitution 0) (substitution 1)
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction stem substitution)
  | trans _ _ first second =>
      exact (first stem substitution).trans (second stem substitution)
  | prepend left _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (stem ++ left.bind substitution) substitution
  | appendRight _ right induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction stem substitution) (right.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction stem (fun letter => (next letter).bind substitution)

/-- Every permutation of the tail preserves and fixes the initial variable. -/
theorem derivesTailPermutation
    (head : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis (Word.mk head left) (Word.mk head right) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      have suffix := induction (head := letter)
      simpa [Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap first second suffix =>
      cases suffix with
      | nil =>
          simpa [Word.singleton, Word.append, Word.append_assoc] using
            derivesSuffixSwap
              (Word.singleton head)
              (Word.singleton second)
              (Word.singleton first)
      | cons next rest =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap
                (Word.singleton head)
                (Word.singleton second)
                (Word.singleton first))
              (Word.mk next rest)
          simpa [Word.singleton, Word.append, Word.append_assoc] using swapped
  | trans _ _ first second =>
      exact (first (head := head)).trans (second (head := head))

/-- Canonical reachable word: fixed head and positive-modulo-three tail. -/
def normal (word : Word Nat) : Word Nat :=
  ⟨word.head, positiveModThreeReduce word.tail⟩

/-- Reachability is syntactic and uses no factor-separation assumption. -/
theorem derives_normal (word : Word Nat) :
    Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons first rest =>
          let suffix : Word Nat := ⟨first, rest⟩
          have suffixNormal := positiveModThreeDerivesNormal suffix
          change
            match positiveModThreeReduce (first :: rest) with
            | [] => False
            | next :: reduced =>
                Derives commutativePositiveModThreeBasis suffix
                  ⟨next, reduced⟩ at suffixNormal
          cases reducedEq : positiveModThreeReduce (first :: rest) with
          | nil =>
              rw [reducedEq] at suffixNormal
              exact False.elim suffixNormal
          | cons next reduced =>
              rw [reducedEq] at suffixNormal
              have lifted :=
                liftPositiveModThree suffixNormal
                  (Word.singleton head) Word.singleton
              rw [bind_singleton, bind_singleton] at lifted
              simpa [normal, suffix, Word.append, Word.singleton,
                reducedEq] using lifted

/-- Validity in the exact left-zero factor fixes the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Opposite-table validity is direct-table validity of the reversed words. -/
theorem rightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_1000.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_1000.table.semigroup.opposite
    at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_1000.table.semigroup).mp valid

/-- The reviewed direct-table signature yields unrestricted support equality. -/
theorem rightValid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (selected : Nat) :
    selected ∈ identity.lhs.toList ↔ selected ∈ identity.rhs.toList := by
  have signature :=
    SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1000.valid_sameSignature
      identity.reversed (rightValid_reversed identity valid)
  simpa [Identity.reversed, Word.toList_reverse] using
    signature.support selected

/-- The cyclic-three embedding yields unrestricted multiplicity residues. -/
theorem rightValid_modThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (selected : Nat) :
    identity.lhs.toList.count selected % 3 =
      identity.rhs.toList.count selected % 3 := by
  have signature :=
    SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1000.valid_sameSignature
      identity.reversed (rightValid_reversed identity valid)
  simpa [Identity.reversed, Word.toList_reverse, List.count_reverse] using
    signature.positiveMultiplicityModThree selected

/-- Pull back along the actual final-marker embedding and then reverse; this
is a genuine unrestricted theory implication, not a finite-table stamp. -/
theorem rightValid_initialMarker
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup.opposite := by
  have reversedMarker :=
    SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1000.finalMarkerEmbedding.pullback_identity
      identity.reversed (rightValid_reversed identity valid)
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      finalMarkerThree.semigroup).mpr reversedMarker

/-- The opposite final-marker factor detects exactly a globally simple head. -/
theorem rightValid_simpleInitial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (selected : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial identity.lhs selected ↔
      SemigroupBasis.CoRoots.S5_107.SimpleInitial identity.rhs selected :=
  SemigroupBasis.CoRoots.S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
    identity (rightValid_initialMarker identity valid) selected

/-- Equal head and globally simple-head semantics recover exact tail support. -/
theorem tailSupport_of_factorValid
    (identity : Identity Nat)
    (heads : identity.lhs.head = identity.rhs.head)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ selected, selected ∈ identity.lhs.tail ↔
      selected ∈ identity.rhs.tail := by
  intro selected
  by_cases isHead : selected = identity.lhs.head
  · subst selected
    have simple := rightValid_simpleInitial identity valid identity.lhs.head
    have absent :
        identity.lhs.head ∉ identity.lhs.tail ↔
          identity.lhs.head ∉ identity.rhs.tail := by
      simpa [SemigroupBasis.CoRoots.S5_107.SimpleInitial,
        SemigroupBasis.CoRoots.S5_107.SimpleIn, Word.toList,
        heads, List.count_eq_zero] using simple
    constructor
    · intro member
      apply Decidable.byContradiction
      intro missing
      exact (absent.mpr missing) member
    · intro member
      apply Decidable.byContradiction
      intro missing
      exact (absent.mp missing) member
  · have isNotRightHead : selected ≠ identity.rhs.head := by
      intro equal
      exact isHead (equal.trans heads.symm)
    have wholeSupport := rightValid_support identity valid selected
    simpa [Word.toList, isHead, isNotRightHead] using wholeSupport

/-- Removing the same literal head preserves equality of modulo-three counts. -/
theorem tailModThree_of_factorValid
    (identity : Identity Nat)
    (heads : identity.lhs.head = identity.rhs.head)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ selected,
      identity.lhs.tail.count selected % 3 =
        identity.rhs.tail.count selected % 3 := by
  intro selected
  have wholeResidue := rightValid_modThree identity valid selected
  simp only [Word.toList] at wholeResidue
  by_cases isHead : selected = identity.lhs.head
  · subst selected
    rw [heads] at wholeResidue ⊢
    simp only [List.count_cons_self] at wholeResidue
    omega
  · have isNotRightHead : selected ≠ identity.rhs.head := by
      intro equal
      exact isHead (equal.trans heads.symm)
    rw [List.count_cons_of_ne (Ne.symm isHead),
      List.count_cons_of_ne (Ne.symm isNotRightHead)] at wholeResidue
    exact wholeResidue

/-- Independent unrestricted completeness for the exact four displayed laws. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have reducedPermutation := positiveModThreeReduce_perm
    (tailSupport_of_factorValid identity heads rightValid)
    (tailModThree_of_factorValid identity heads rightValid)
  have normalizedMiddle :
      Derives basis (normal identity.lhs) (normal identity.rhs) := by
    simpa [normal, heads] using
      derivesTailPermutation identity.lhs.head reducedPermutation
  exact (derives_normal identity.lhs).trans <|
    normalizedMiddle.trans (derives_normal identity.rhs).symm

/-- The reviewed pair structure is constructed only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Package the completed pair theorem as a reusable certified seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_14920_representative_basis :
    BasisFor S6_14920.table.semigroup basis :=
  S6_14920.representative_basis_of_normalizer normalizer

theorem s6_14920_opposite_basis :
    BasisFor S6_14920.table.semigroup.opposite (reversedBasis basis) :=
  S6_14920.opposite_basis_of_normalizer normalizer

theorem s6_14924_representative_basis :
    BasisFor S6_14924.table.semigroup basis :=
  S6_14924.representative_basis_of_normalizer normalizer

theorem s6_14924_opposite_basis :
    BasisFor S6_14924.table.semigroup.opposite (reversedBasis basis) :=
  S6_14924.opposite_basis_of_normalizer normalizer

/-- Reuse the kernel-reviewed transport without manufacturing any theory
implication or displayed-law derivation. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank007.Seed

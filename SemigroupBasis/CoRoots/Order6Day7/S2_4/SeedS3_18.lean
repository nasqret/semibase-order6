import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank070
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.Generated.S3_18

/-!
# An unrestricted `S2_4 × S3_18` family seed

The exact `S3_18` catalogue factor is the cyclic group of order three. Its
independently complete semigroup presentation has two laws: commutativity
and cancellation of a cube before a nonempty suffix. Both laws are replayed
behind arbitrary nonempty contexts directly from the authenticated rank-070
displayed basis.

The actual left-zero factor independently fixes the initial variable. Adding
exactly three copies of that shared head preserves the cyclic-three exponent
vector and is derived from the actual displayed `x = xxxx` law, including
singleton words. The complete cyclic-group derivation can therefore be lifted
between the two triple-prefixed words and the added heads removed on both
sides. The finitely refuted rank-007 right-factor theory implication is never
used or manufactured.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank070.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | marker + 3 => Word.singleton (marker + 3)

/-- The staged `x = xyyy` inserts exactly one suffix cube. -/
theorem derivesCubeInsertion (stem block : Word Nat) :
    Derives basis
      stem
      (((stem ++ block) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 []) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree stem block block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The staged `xyz = xzy` swaps arbitrary nonempty suffix blocks. -/
theorem derivesSuffixSwap (stem first second : Word Nat) :
    Derives basis
      ((stem ++ first) ++ second)
      ((stem ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree stem first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Append a genuine nonempty suffix to `x = xyyy`, obtaining the
contextual cyclic-group cancellation law. -/
theorem derivesContextualCubeCancellation
    (stem block final : Word Nat) :
    Derives basis
      ((((stem ++ block) ++ block) ++ block) ++ final)
      (stem ++ final) :=
  (Derives.appendRight (derivesCubeInsertion stem block) final).symm

/-- The separate staged `x = xxxx` inserts three copies of any fixed
nonempty block. -/
theorem derivesPowerPeriod (block : Word Nat) :
    Derives basis
      block
      (((block ++ block) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 []) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree block block block)
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

/-- Replay both independently complete cyclic-three axioms behind any
fixed nonempty context, with all simultaneous substitutions explicit. -/
theorem liftCyclicThree
    {left right : Word Nat}
    (derivation : Derives cyclicThreeBasis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [cyclicThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [cyclicThreeCommutativityLaw, cyclicThreeXY,
          cyclicThreeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesSuffixSwap stem (substitution 0) (substitution 1)
      · simpa [cyclicThreeCancellationLaw, cyclicThreeXXXY,
          cyclicThreeY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualCubeCancellation
            stem (substitution 0) (substitution 1)
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

/-- Adding three copies of a word's actual initial variable preserves both
the left-zero head and every cyclic-three residue, even for singletons. -/
theorem derivesTripleHeadInsertion (word : Word Nat) :
    Derives basis
      word
      (((Word.singleton word.head ++ Word.singleton word.head) ++
          Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [Word.singleton, Word.append] using
            derivesPowerPeriod (Word.singleton head)
      | cons first rest =>
          have inserted :=
            Derives.appendRight
              (derivesPowerPeriod (Word.singleton head))
              (Word.mk first rest)
          simpa [Word.singleton, Word.append,
            Word.append_assoc] using inserted

/-- Identify the actual staged catalogue table with the independently
certified cyclic group; this is a table equality, not a theory guess. -/
theorem rightTable_eq_cyclicThree : rightTable = cyclicThree :=
  SemigroupBasis.Generated.S3_18.table_eq_canonical_catalogue.symm.trans
    SemigroupBasis.Generated.S3_18.table_eq_catalogue_model

/-- Actual right-factor validity is unrestricted cyclic-group validity. -/
theorem rightValid_cyclicThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy cyclicThree.semigroup := by
  rw [rightTable_eq_cyclicThree] at valid
  exact valid

/-- The actual three-element group fixes every variable multiplicity
modulo three over unrestricted natural-number alphabets. -/
theorem rightValid_modThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup)
    (selected : Nat) :
    identity.lhs.toList.count selected % 3 =
      identity.rhs.toList.count selected % 3 :=
  cyclicThreeValid_mod_eq identity
    (rightValid_cyclicThree identity valid) selected

/-- Validity in the exact `S2_4` left-zero factor fixes the first variable. -/
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

/-- Independent unrestricted pair completeness from the actual cyclic-group
basis, the common left-zero head, and honest triple-head insertion. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have groupValid := rightValid_cyclicThree identity rightValid
  have lower := cyclicThreeBasis_complete.2 identity groupValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  let fixed := Word.singleton leftHead
  let triple := (fixed ++ fixed) ++ fixed
  have lifted := liftCyclicThree lower triple Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  have leftInserted :=
    derivesTripleHeadInsertion (Word.mk leftHead leftTail)
  have rightInserted :=
    derivesTripleHeadInsertion (Word.mk leftHead rightTail)
  exact leftInserted.trans (lifted.trans rightInserted.symm)

/-- Construct the reviewed pair structure only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable cyclic-three rank-070 seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_15959_representative_basis :
    BasisFor S6_15959.table.semigroup basis :=
  S6_15959.representative_basis_of_normalizer normalizer

theorem s6_15959_opposite_basis :
    BasisFor S6_15959.table.semigroup.opposite (reversedBasis basis) :=
  S6_15959.opposite_basis_of_normalizer normalizer

/-- Further reviewed transport retains all explicit law derivations and both
independent unrestricted target-factor theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank070.Seed

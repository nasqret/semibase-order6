import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank056
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S6_9503

/-!
# An unrestricted `S2_4 × S5_506` family seed

The staged rank-056 file supplies only finite soundness and split-subdirect
maps.  This file independently proves the missing unrestricted intersection
completeness.  The positive-period-four first-occurrence normalizer supplies
reachable normal words; the additional `xyz = xzy` law makes their suffixes
interchangeable whenever the two factors enforce equal initial letters and
equal retained multiplicities.

The quotient-normalizer adapter is used only *after* this unrestricted
completeness theorem has been established.  Further transport retains explicit
law derivations and unrestricted factor-theory implications as premises.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank056.Seed

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

universe u v

/-- Validity in the exact left-zero factor determines the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy SemigroupBasis.Examples.leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [SemigroupBasis.Examples.leftZeroTwo_eval,
    SemigroupBasis.Examples.leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Both laws of the existing positive-period-four normalizer are displayed
literally in the authenticated rank-056 basis. -/
theorem sourceLawDerives
    (law : Identity Nat)
    (member : law ∈ SemigroupBasis.CoRoots.S6_9503.basis) :
    Derives basis law.lhs law.rhs := by
  simp only [SemigroupBasis.CoRoots.S6_9503.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · change Derives basis law00.lhs law00.rhs
    exact Derives.fromBasis (e := law00) (by simp [basis])
  · change Derives basis law01.lhs law01.rhs
    exact Derives.fromBasis (e := law01) (by simp [basis])

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The third displayed law swaps arbitrary nonempty suffix blocks. -/
theorem derivesSuffixSwap
    (stem first second : Word Nat) :
    Derives basis
      ((stem ++ first) ++ second)
      ((stem ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree stem first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Every permutation strictly after the initial variable is derivable. -/
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

/-- Reuse the already-proved positive-period-four normalizer; no factor
separation is inferred from its reachability theorem. -/
theorem derivesSourceNormal (word : Word Nat) :
    ∃ normalized : Word Nat,
      normalized.toList =
          SemigroupBasis.CoRoots.S6_9503.normalList word.toList ∧
        Derives basis word normalized := by
  cases word with
  | mk head tail =>
      have listed :=
        SemigroupBasis.CoRoots.S6_9503.derivesNormalize (head :: tail)
      obtain ⟨normalHead, normalTail, normalList, derivation⟩ :=
        ListDerives.from_cons listed
      refine ⟨Word.mk normalHead normalTail, normalList.symm, ?_⟩
      exact derivation.transport sourceLawDerives

/-- The two exact factors enforce equal retained positive-period-four counts. -/
theorem rightValid_retainedCounts
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ selected,
      SemigroupBasis.CoRoots.S6_9503.retainedExponent
          (identity.lhs.toList.count selected) =
        SemigroupBasis.CoRoots.S6_9503.retainedExponent
          (identity.rhs.toList.count selected) := by
  have familyValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup := by
    simpa [rightTable,
      SemigroupBasis.CoRoots.S5_505Family.S5_506.table] using valid
  exact SemigroupBasis.CoRoots.S6_9503.retainedExponent_eq_of_samePositiveModFour
    (SemigroupBasis.CoRoots.S5_505Family.S5_506.valid_samePositiveModFour
      identity familyValid)

/-- Genuine unrestricted factor-pair completeness for the authenticated
three-law rank-056 basis. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftNormal, leftNormalList, leftDerivation⟩ :=
    derivesSourceNormal identity.lhs
  obtain ⟨rightNormal, rightNormalList, rightDerivation⟩ :=
    derivesSourceNormal identity.rhs
  have originalHeads := leftValid_head identity leftValid
  have normalizedLeftHead :=
    leftValid_head (Identity.mk identity.lhs leftNormal)
      (fun valuation => Derives.sound leftModels leftDerivation valuation)
  have normalizedRightHead :=
    leftValid_head (Identity.mk identity.rhs rightNormal)
      (fun valuation => Derives.sound leftModels rightDerivation valuation)
  have normalHeads : leftNormal.head = rightNormal.head :=
    normalizedLeftHead.symm.trans
      (originalHeads.trans normalizedRightHead)
  have normalCounts (selected : Nat) :
      leftNormal.toList.count selected =
        rightNormal.toList.count selected := by
    rw [leftNormalList, rightNormalList,
      SemigroupBasis.CoRoots.S6_9503.normalList_count,
      SemigroupBasis.CoRoots.S6_9503.normalList_count]
    exact rightValid_retainedCounts identity rightValid selected
  cases leftNormal with
  | mk leftHead leftTail =>
      cases rightNormal with
      | mk rightHead rightTail =>
          change leftHead = rightHead at normalHeads
          subst rightHead
          have tailPermutation : leftTail.Perm rightTail := by
            rw [List.perm_iff_count]
            intro selected
            have sameCounts := normalCounts selected
            change
              (leftHead :: leftTail).count selected =
                (leftHead :: rightTail).count selected at sameCounts
            simp only [List.count_cons] at sameCounts
            omega
          exact leftDerivation.trans <|
            (derivesTailPermutation leftHead tailPermutation).trans
              rightDerivation.symm

/-- This structure exists only after the independent unrestricted theorem. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- The quotient adapter packages an already-established unrestricted seed;
it does not supply or assume its own completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The staged rank-056 representative now has an unconditional endpoint. -/
theorem representative_basis :
    BasisFor S6_9501.table.semigroup basis :=
  S6_9501.representative_basis_of_normalizer normalizer

/-- The exact opposite-orientation endpoint follows from the same seed. -/
theorem opposite_basis :
    BasisFor S6_9501.table.semigroup.opposite (reversedBasis basis) :=
  S6_9501.opposite_basis_of_normalizer normalizer

/-- Reuse the reviewed common transport, retaining every displayed-law
derivation and unrestricted semantic implication as an explicit premise. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank056.Seed

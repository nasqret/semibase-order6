import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank015
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_520Family

/-!
# An unrestricted `S2_4 × S5_522ᵒᵖ` family seed

The staged rank-015 shell contains only finite soundness and two authenticated
split-subdirect maps.  The independently complete `S5_522` calculus proves
that every valid reversed identity is either literally equal or has at least
three letters on both sides.  Its six reversed basis laws can all be replayed
behind a fixed initial variable using the displayed transfer, contraction,
repeated-deletion, and insertion-swap laws.

On the long stratum, `xxyz = xyz` removes the temporary initial variable from
both endpoints.  Literal identities need no transport.  This establishes
unrestricted factor-intersection completeness before quotient packaging and
supplies both orientations for both authenticated six-element classes.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank015.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed `xxx = xxxx` expands a triple block. -/
theorem derivesLongPowerExpansion (first : Word Nat) :
    Derives basis
      ((first ++ first) ++ first)
      (((first ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxy = xyy` transfers a repeated block. -/
theorem derivesTransfer (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxyz = xyz` removes a repeated initial block from every
three-block word. -/
theorem derivesHeadContraction
    (first second third : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyxz = xyz` erases an interior repeat of the initial block. -/
theorem derivesRepeatedDeletion
    (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law06) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyz = xzyz` swaps two suffix blocks while retaining a
duplicate of the terminal block. -/
theorem derivesInsertionSwap
    (first second third : Word Nat) :
    Derives basis
      ((first ++ second) ++ third)
      (((first ++ third) ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1, 2]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary interior blocks commute between unchanged nonempty endpoints. -/
theorem derivesInteriorSwap
    (initial first second final : Word Nat) :
    Derives basis
      (((initial ++ first) ++ second) ++ final)
      (((initial ++ second) ++ first) ++ final) := by
  have insertion :=
    Derives.appendRight
      (derivesInsertionSwap initial first second) final
  have deletion :
      Derives basis
        ((((initial ++ second) ++ first) ++ second) ++ final)
        (((initial ++ second) ++ first) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.prepend initial
        (derivesRepeatedDeletion second first final)
  exact insertion.trans deletion

/-- Duplicate a nonempty interior block while preserving both contexts. -/
theorem derivesInteriorDuplication
    (initial repeated final : Word Nat) :
    Derives basis
      ((initial ++ repeated) ++ final)
      (((initial ++ repeated) ++ repeated) ++ final) := by
  have expand :=
    (derivesHeadContraction initial repeated final).symm
  have transfer :=
    Derives.appendRight (derivesTransfer initial repeated) final
  exact expand.trans transfer

/-- Duplicate the terminal block of any three-block word. -/
theorem derivesFinalDuplication
    (initial middle final : Word Nat) :
    Derives basis
      ((initial ++ middle) ++ final)
      (((initial ++ middle) ++ final) ++ final) := by
  exact
    (derivesInsertionSwap initial middle final).trans
      (derivesInteriorSwap initial final middle final)

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

/-- Replay all six independently certified reversed lower-factor laws behind
a fixed nonempty initial block, with arbitrary substitutions explicit. -/
theorem liftS5_520Opposite
    {left right : Word Nat}
    (derivation :
      Derives
        (reversedBasis SemigroupBasis.CoRoots.S5_520.basis)
        left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [reversedBasis, SemigroupBasis.CoRoots.S5_520.basis,
        List.map, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · change
          Derives basis
            (stem ++ (Word.mk 0 [0, 0]).bind substitution)
            (stem ++ (Word.mk 0 [0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesLongPowerExpansion (substitution 0))
      · change
          Derives basis
            (stem ++ (Word.mk 1 [0, 0]).bind substitution)
            (stem ++ (Word.mk 0 [1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesInteriorSwap stem
            (substitution 1) (substitution 0) (substitution 0)
      · change
          Derives basis
            (stem ++ (Word.mk 1 [0, 0]).bind substitution)
            (stem ++ (Word.mk 1 [1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesTransfer
              (substitution 1) (substitution 0)).symm
      · change
          Derives basis
            (stem ++ (Word.mk 1 [0, 0]).bind substitution)
            (stem ++ (Word.mk 1 [0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesInteriorDuplication
            (stem ++ substitution 1)
            (substitution 0) (substitution 0)
      · change
          Derives basis
            (stem ++ (Word.mk 2 [1, 0]).bind substitution)
            (stem ++ (Word.mk 1 [2, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesInteriorSwap stem
            (substitution 2) (substitution 1) (substitution 0)
      · change
          Derives basis
            (stem ++ (Word.mk 2 [1, 0]).bind substitution)
            (stem ++ (Word.mk 2 [1, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesFinalDuplication
            (stem ++ substitution 2)
            (substitution 1) (substitution 0)
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

/-- Opposite-table validity is independently certified direct-table validity
of the reversed words. -/
theorem rightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_522.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_522.table.semigroup.opposite
    at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_522.table.semigroup).mp valid

/-- Genuine unrestricted pair completeness. The reviewed exact-class theorem
handles literal words and guarantees both nontrivial endpoints are long enough
for the displayed temporary-head contraction. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have reversedValid := rightValid_reversed identity rightValid
  have lowerDirect :=
    SemigroupBasis.CoRoots.S5_520Family.S5_522.basis_complete.2
      identity.reversed reversedValid
  have exactClass :=
    SemigroupBasis.CoRoots.S5_520.derives_iff_exactBasisClass.mp
      lowerDirect
  rcases exactClass with equal | ⟨leftReversedLong,
    rightReversedLong, _, _⟩
  · have unreversed := congrArg Word.reverse equal
    have same : identity.lhs = identity.rhs := by
      simpa [Identity.reversed] using unreversed
    rw [same]
    exact Derives.refl _
  · have leftLong : 3 ≤ identity.lhs.toList.length := by
      simpa [Identity.reversed, Word.toList_reverse] using leftReversedLong
    have rightLong : 3 ≤ identity.rhs.toList.length := by
      simpa [Identity.reversed, Word.toList_reverse] using rightReversedLong
    have lowerOpposite :
        Derives
          (reversedBasis SemigroupBasis.CoRoots.S5_520.basis)
          identity.lhs identity.rhs := by
      simpa [Identity.reversed] using lowerDirect.reverse
    have heads := leftValid_head identity leftValid
    cases identity with
    | mk left right =>
        cases left with
        | mk head leftTail =>
            cases right with
            | mk rightHead rightTail =>
                change head = rightHead at heads
                subst rightHead
                cases leftTail with
                | nil =>
                    simp [Word.toList] at leftLong
                | cons first leftRest =>
                    cases leftRest with
                    | nil =>
                        simp [Word.toList] at leftLong
                    | cons second leftMore =>
                        cases rightTail with
                        | nil =>
                            simp [Word.toList] at rightLong
                        | cons other rightRest =>
                            cases rightRest with
                            | nil =>
                                simp [Word.toList] at rightLong
                            | cons last rightMore =>
                                let leftSuffix : Word Nat :=
                                  ⟨second, leftMore⟩
                                let rightSuffix : Word Nat :=
                                  ⟨last, rightMore⟩
                                have lifted :=
                                  liftS5_520Opposite lowerOpposite
                                    (Word.singleton head) Word.singleton
                                rw [bind_singleton,
                                  bind_singleton] at lifted
                                have leftCollapse :=
                                  derivesHeadContraction
                                    (Word.singleton head)
                                    (Word.singleton first)
                                    leftSuffix
                                have rightCollapse :=
                                  derivesHeadContraction
                                    (Word.singleton head)
                                    (Word.singleton other)
                                    rightSuffix
                                simpa [leftSuffix, rightSuffix,
                                  Word.append, Word.singleton,
                                  Word.append_assoc] using
                                  leftCollapse.symm.trans
                                    (lifted.trans rightCollapse)

/-- Build the reviewed pair structure only after unrestricted proof. -/
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

theorem s6_9677_representative_basis :
    BasisFor S6_9677.table.semigroup basis :=
  S6_9677.representative_basis_of_normalizer normalizer

theorem s6_9677_opposite_basis :
    BasisFor S6_9677.table.semigroup.opposite (reversedBasis basis) :=
  S6_9677.opposite_basis_of_normalizer normalizer

theorem s6_9696_representative_basis :
    BasisFor S6_9696.table.semigroup basis :=
  S6_9696.representative_basis_of_normalizer normalizer

theorem s6_9696_opposite_basis :
    BasisFor S6_9696.table.semigroup.opposite (reversedBasis basis) :=
  S6_9696.opposite_basis_of_normalizer normalizer

/-- Reuse reviewed transport only with explicit law derivations and genuine
unrestricted factor-theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank015.Seed

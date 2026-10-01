import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_203Family

/-!
# An unrestricted `S2_4 × S5_203` family seed

The independent ten-law `S5_203` endpoint supplies a genuine derivation for
every identity valid in the actual right factor. All ten lower-factor laws
can be replayed behind an arbitrary nonempty initial context: the two
head-changing laws require explicit three-step contextual switch and
square-suffix-swap derivations from the authenticated rank-044 laws.

A structural induction on the lower derivation proves that it is either
literally reflexive or both endpoints have length at least three. In the
nontrivial stratum, the actual left-zero factor fixes the common first letter
and the staged `xxyz = xyz` law cancels the temporary initial context on both
sides. Unrestricted pair completeness is thus established before packaging a
quotient normalizer or transporting it.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The authenticated `xxx = xxxx` expands a triple block. -/
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

/-- The authenticated `xxxy = xxy` removes an initial third copy. -/
theorem derivesTriplePrefixContraction
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ first) ++ second)
      ((first ++ first) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xxyx = xyx` removes an initial repeated endpoint. -/
theorem derivesInitialContraction
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ first)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xxyy = xyy` removes a repeated first block. -/
theorem derivesPairedPrefixContraction
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ second)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xxyz = xyz` cancels a temporary initial block. -/
theorem derivesHeadContraction
    (first second third : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyx = xyxx` repeats the final endpoint. -/
theorem derivesFinalEndpointExpansion
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      (((first ++ second) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyx = xyyx` repeats the interior block. -/
theorem derivesMiddleExpansion
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      (((first ++ second) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyx = xyyy` changes to a triple final block. -/
theorem derivesTerminalCube
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      (((first ++ second) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := law08) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The staged `xyxzz = xyzz` removes an initial copy before a square. -/
theorem derivesSquareSuffixContraction
    (first second third : Word Nat) :
    Derives basis
      ((((first ++ second) ++ first) ++ third) ++ third)
      (((first ++ second) ++ third) ++ third) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The staged `xyzx = xyzy` retargets a returning endpoint. -/
theorem derivesTerminalRetarget
    (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ first)
      (((first ++ second) ++ third) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [1, 2, 1]) :=
    Derives.fromBasis (e := law10) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The staged `xyzx = xzyx` swaps the middle blocks before a return. -/
theorem derivesMiddleSwapWithReturn
    (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := law11) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Replay the lower `xyx = yxy` law only behind a fixed nonempty stem. -/
theorem derivesContextualAlternatingSwitch
    (stem first second : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ first)
      (((stem ++ second) ++ first) ++ second) := by
  exact
    (derivesTerminalRetarget stem first second).symm.trans <|
      (derivesMiddleSwapWithReturn stem first second).trans
        (derivesTerminalRetarget stem second first)

/-- Replay the lower `xyx = xyyxx` law from two genuine staged laws. -/
theorem derivesDoublePairExpansion
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      ((((first ++ second) ++ second) ++ first) ++ first) := by
  exact (derivesMiddleExpansion first second).trans <| by
    simpa [Word.append_assoc] using
      derivesFinalEndpointExpansion first (second ++ second)

/-- Replay the head-changing square-suffix law behind a fixed stem:
`pabcc ← pabpcc → pbapcc → pbacc`. -/
theorem derivesContextualSquareSuffixSwap
    (stem first second final : Word Nat) :
    Derives basis
      ((((stem ++ first) ++ second) ++ final) ++ final)
      ((((stem ++ second) ++ first) ++ final) ++ final) := by
  have insert :=
    (derivesSquareSuffixContraction stem (first ++ second) final).symm
  have swap :=
    Derives.appendRight
      (derivesMiddleSwapWithReturn stem first second)
      (final ++ final)
  have remove :=
    derivesSquareSuffixContraction stem (second ++ first) final
  have firstStep :
      Derives basis
        ((((stem ++ first) ++ second) ++ final) ++ final)
        (((((stem ++ first) ++ second) ++ stem) ++ final) ++ final) := by
    simpa [Word.append_assoc] using insert
  have secondStep :
      Derives basis
        (((((stem ++ first) ++ second) ++ stem) ++ final) ++ final)
        (((((stem ++ second) ++ first) ++ stem) ++ final) ++ final) := by
    simpa [Word.append_assoc] using swap
  have thirdStep :
      Derives basis
        (((((stem ++ second) ++ first) ++ stem) ++ final) ++ final)
        ((((stem ++ second) ++ first) ++ final) ++ final) := by
    simpa [Word.append_assoc] using remove
  exact firstStep.trans (secondStep.trans thirdStep)

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

/-- Replay every independently certified lower-factor consequence behind an
arbitrary nonempty first context, with all substitutions explicit. -/
theorem liftS5_203
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_203.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_203.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesLongPowerExpansion (substitution 0))
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesTriplePrefixContraction
              (substitution 0) (substitution 1)).symm
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 0]).bind substitution)
          (stem ++ (Word.mk 1 [0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualAlternatingSwitch
            stem (substitution 0) (substitution 1)
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesInitialContraction
              (substitution 0) (substitution 1)).symm
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 0]).bind substitution)
          (stem ++ (Word.mk 0 [1, 1, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesTerminalCube
              (substitution 0) (substitution 1))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 0]).bind substitution)
          (stem ++ (Word.mk 0 [1, 1, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesDoublePairExpansion
              (substitution 0) (substitution 1))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPairedPrefixContraction
              (substitution 0) (substitution 1)).symm
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesHeadContraction
              (substitution 0) (substitution 1)
              (substitution 2)).symm
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2, 0]).bind substitution)
          (stem ++ (Word.mk 0 [1, 2, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesTerminalRetarget
              (substitution 0) (substitution 1)
              (substitution 2))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2, 2]).bind substitution)
          (stem ++ (Word.mk 1 [0, 2, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualSquareSuffixSwap
            stem (substitution 0) (substitution 1)
            (substitution 2)
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

private def ShortLong (left right : Word Nat) : Prop :=
  left = right ∨
    (3 ≤ left.toList.length ∧ 3 ≤ right.toList.length)

private theorem wordLengthPositive (word : Word Nat) :
    1 ≤ word.toList.length := by
  cases word
  simp [Word.toList]

private theorem listLength_le_flatMapWords
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter =>
        (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest induction =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have positive := wordLengthPositive (substitution letter)
      omega

private theorem bind_preservesLength
    (word : Word Nat) (substitution : Nat → Word Nat)
    {bound : Nat} (long : bound ≤ word.toList.length) :
    bound ≤ (word.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (listLength_le_flatMapWords word.toList substitution)

/-- Every genuine ten-law lower derivation is literal or stays entirely in
the length-at-least-three stratum. -/
theorem lowerDerivation_shortOrLong
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_203.basis left right) :
    ShortLong left right := by
  induction derivation with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_203.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        exact Or.inr ⟨by decide, by decide⟩
  | refl =>
      exact Or.inl rfl
  | symm _ induction =>
      rcases induction with equal | long
      · exact Or.inl equal.symm
      · exact Or.inr ⟨long.2, long.1⟩
  | trans _ _ first second =>
      rcases first with equal | firstLong
      · subst_vars
        exact second
      · rcases second with equal | secondLong
        · subst_vars
          exact Or.inr firstLong
        · exact Or.inr ⟨firstLong.1, secondLong.2⟩
  | prepend stem _ induction =>
      rcases induction with equal | long
      · exact Or.inl (congrArg (fun word => stem ++ word) equal)
      · apply Or.inr
        constructor <;>
          rw [Word.toList_append, List.length_append] <;>
          omega
  | appendRight _ suffix induction =>
      rcases induction with equal | long
      · exact Or.inl (congrArg (fun word => word ++ suffix) equal)
      · apply Or.inr
        constructor <;>
          rw [Word.toList_append, List.length_append] <;>
          omega
  | subst _ substitution induction =>
      rcases induction with equal | long
      · exact Or.inl
          (congrArg (fun word => word.bind substitution) equal)
      · exact Or.inr
          ⟨bind_preservesLength _ substitution long.1,
            bind_preservesLength _ substitution long.2⟩

/-- Validity in the actual left-zero factor fixes the first variable. -/
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

/-- Genuine unrestricted factor-pair completeness, proved before any
quotient-normalizer packaging. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have actualRight :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_203.table.semigroup := by
    simpa [rightTable, SemigroupBasis.CoRoots.S5_203.table] using
      rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_203Family.S5_203.basisFor.2
      identity actualRight
  rcases lowerDerivation_shortOrLong lower with equal | long
  · rw [equal]
    exact Derives.refl _
  · have heads := leftValid_head identity leftValid
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
                    simp [Word.toList] at long
                | cons first leftRest =>
                    cases leftRest with
                    | nil =>
                        simp [Word.toList] at long
                    | cons second leftMore =>
                        cases rightTail with
                        | nil =>
                            simp [Word.toList] at long
                        | cons other rightRest =>
                            cases rightRest with
                            | nil =>
                                simp [Word.toList] at long
                            | cons last rightMore =>
                                let leftSuffix : Word Nat :=
                                  ⟨second, leftMore⟩
                                let rightSuffix : Word Nat :=
                                  ⟨last, rightMore⟩
                                have lifted :=
                                  liftS5_203 lower
                                    (Word.singleton head)
                                    Word.singleton
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

/-- Package the genuine pair theorem as a reusable certified seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_5577_representative_basis :
    BasisFor S6_5577.table.semigroup basis :=
  S6_5577.representative_basis_of_normalizer normalizer

theorem s6_5577_opposite_basis :
    BasisFor S6_5577.table.semigroup.opposite (reversedBasis basis) :=
  S6_5577.opposite_basis_of_normalizer normalizer

/-- Reuse reviewed transport only with explicit law derivations and genuine
unrestricted implications for both actual target factors. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.Seed

import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank048
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# An unrestricted `S2_4 × S5_240` family seed

The independently certified three-law `S5_240` basis supplies an unrestricted
lower-factor derivation. Every one of its laws is replayed behind a fixed
nonempty context using authenticated rank-048 displayed laws. The actual
left-zero factor fixes the common first variable.

Temporary-head contraction is valid only for words with at least three
letters. Singleton identities are therefore separated explicitly, globally
simple distinct two-letter words are fixed by the certified penultimate-pair
invariant, and repeated two-letter words are handled by the actual square
law. These genuine short-word branches establish unrestricted completeness
before quotient packaging.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank048.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed `xx = xxx` expands a genuine two-letter square. -/
theorem derivesPowerExpansion
    (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxyz = xyz` contracts only a three-block suffix. -/
theorem derivesHeadContraction
    (first second third : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyzz = xzyy` replays the lower marker switch only
behind its required fixed nonempty first context. -/
theorem derivesContextualMarkerSwitch
    (stem first second : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ second)
      (((stem ++ second) ++ first) ++ first) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1, 2, 2]) (Word.mk 0 [2, 1, 1]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
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

/-- Replay every independently certified lower consequence behind an
arbitrary genuine first context, with all substitutions explicit. -/
theorem liftS5_240
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_240.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_240.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change Derives basis
          (stem ++ (Word.mk 0 [0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPowerExpansion (substitution 0))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 1]).bind substitution)
          (stem ++ (Word.mk 1 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualMarkerSwitch
            stem (substitution 0) (substitution 1)
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesHeadContraction
              (substitution 0) (substitution 1)
              (substitution 2)).symm
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

/-- The reviewed singleton signature is exactly the empty-tail stratum. -/
theorem singleton_iff_tail_nil
    (word : Word Nat) :
    IsSingletonWord word ↔ word.tail = [] := by
  constructor
  · intro singleton
    cases split : terminalSplit word with
    | singleton final =>
        have rendered := terminalSplit_renderList word
        rw [split] at rendered
        have tails := congrArg List.tail rendered
        simpa [TerminalSplit.renderList, Word.toList] using tails.symm
    | pair stem penultimate final =>
        simp [IsSingletonWord, split] at singleton
  · intro empty
    cases word with
    | mk head tail =>
        change tail = [] at empty
        subst tail
        change True
        trivial

/-- A globally simple distinct terminal pair starting with the common head
cannot hide a nonempty earlier stem. -/
theorem simpleDoubleton_rigid
    (head marker : Nat)
    (word : Word Nat)
    (sameHead : word.head = head)
    (pair :
      SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
        word head marker) :
    word = Word.mk head [marker] := by
  cases split : terminalSplit word with
  | singleton final =>
      simp [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
        split] at pair
  | pair stem penultimate final =>
      have parts :
          penultimate = head ∧ final = marker ∧
            head ∉ stem ∧ marker ≠ head := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
          split] using pair
      have rendered := terminalSplit_renderList word
      rw [split] at rendered
      cases stem with
      | nil =>
          apply Word.toList_injective
          simpa [TerminalSplit.renderList, Word.toList,
            parts.1, parts.2.1] using rendered.symm
      | cons first rest =>
          have firstHead : first = word.head := by
            have compared := congrArg List.head? rendered
            simpa [TerminalSplit.renderList, Word.toList] using compared
          have present : head ∈ first :: rest := by
            simp [firstHead, sameHead]
          exact (parts.2.2.1 present).elim

/-- Validity in the actual left-zero factor fixes the initial variable. -/
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

/-- Genuine unrestricted pair completeness with explicit singleton, distinct
doubleton, repeated-doubleton, and long-word branches. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have actualRight :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup := by
    simpa [rightTable] using rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_240.basis_complete.2
      identity actualRight
  have same :=
    SemigroupBasis.CoRoots.S5_240.valid_signature
      identity actualRight
  have heads := leftValid_head identity leftValid
  have singletonIff : identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
    constructor
    · intro empty
      exact (singleton_iff_tail_nil identity.rhs).mp <|
        same.singleton.mp <|
          (singleton_iff_tail_nil identity.lhs).mpr empty
    · intro empty
      exact (singleton_iff_tail_nil identity.lhs).mp <|
        same.singleton.mpr <|
          (singleton_iff_tail_nil identity.rhs).mpr empty
  cases identity with
  | mk left right =>
      cases left with
      | mk head leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change head = rightHead at heads
              subst rightHead
              change leftTail = [] ↔ rightTail = [] at singletonIff
              cases leftTail with
              | nil =>
                  have rightNil : rightTail = [] := singletonIff.mp rfl
                  subst rightTail
                  exact Derives.refl _
              | cons leftSecond leftRest =>
                  cases rightTail with
                  | nil =>
                      have impossible :
                          leftSecond :: leftRest = [] :=
                        singletonIff.mpr rfl
                      simp at impossible
                  | cons rightSecond rightRest =>
                      have lifted :=
                        liftS5_240 lower
                          (Word.singleton head) Word.singleton
                      rw [bind_singleton, bind_singleton] at lifted
                      cases leftRest with
                      | nil =>
                          by_cases different : head ≠ leftSecond
                          · have leftSplit :
                                terminalSplit
                                  (Word.mk head [leftSecond]) =
                                  .pair [] head leftSecond := by
                                rfl
                            have leftPair :
                                SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                                  (Word.mk head [leftSecond])
                                  head leftSecond := by
                                simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                                  leftSplit] using
                                  Ne.symm different
                            have rightPair :=
                              (same.simplePenultimatePair
                                head leftSecond).mp leftPair
                            have rigid :=
                              simpleDoubleton_rigid
                                head leftSecond
                                (Word.mk head (rightSecond :: rightRest))
                                rfl rightPair
                            rw [rigid]
                            exact Derives.refl _
                          · have equal : leftSecond = head :=
                              (Classical.byContradiction different).symm
                            subst leftSecond
                            cases rightRest with
                            | nil =>
                                have belongs :
                                    rightSecond ∈
                                      (Word.mk head [head]).toList :=
                                  (same.support rightSecond).mpr <| by
                                    simp [Word.toList]
                                have rightEqual : rightSecond = head := by
                                  simpa [Word.toList] using belongs
                                subst rightSecond
                                exact Derives.refl _
                            | cons rightThird rightMore =>
                                let rightSuffix : Word Nat :=
                                  ⟨rightThird, rightMore⟩
                                have rightCollapse :=
                                  derivesHeadContraction
                                    (Word.singleton head)
                                    (Word.singleton rightSecond)
                                    rightSuffix
                                have squareExpand :=
                                  derivesPowerExpansion
                                    (Word.singleton head)
                                simpa [rightSuffix, Word.append,
                                  Word.singleton, Word.append_assoc] using
                                  squareExpand.trans
                                    (lifted.trans rightCollapse)
                      | cons leftThird leftMore =>
                          let leftSuffix : Word Nat :=
                            ⟨leftThird, leftMore⟩
                          have leftCollapse :=
                            derivesHeadContraction
                              (Word.singleton head)
                              (Word.singleton leftSecond)
                              leftSuffix
                          cases rightRest with
                          | nil =>
                              by_cases different : head ≠ rightSecond
                              · have rightSplit :
                                    terminalSplit
                                      (Word.mk head [rightSecond]) =
                                      .pair [] head rightSecond := by
                                    rfl
                                have rightPair :
                                    SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                                      (Word.mk head [rightSecond])
                                      head rightSecond := by
                                    simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                                      rightSplit] using
                                      Ne.symm different
                                have leftPair :=
                                  (same.simplePenultimatePair
                                    head rightSecond).mpr rightPair
                                have rigid :=
                                  simpleDoubleton_rigid
                                    head rightSecond
                                    (Word.mk head
                                      (leftSecond :: leftThird :: leftMore))
                                    rfl leftPair
                                rw [rigid]
                                exact Derives.refl _
                              · have equal : rightSecond = head :=
                                  (Classical.byContradiction different).symm
                                subst rightSecond
                                have squareExpand :=
                                  derivesPowerExpansion
                                    (Word.singleton head)
                                simpa [leftSuffix, Word.append,
                                  Word.singleton, Word.append_assoc] using
                                  leftCollapse.symm.trans
                                    (lifted.trans squareExpand.symm)
                          | cons rightThird rightMore =>
                              let rightSuffix : Word Nat :=
                                ⟨rightThird, rightMore⟩
                              have rightCollapse :=
                                derivesHeadContraction
                                  (Word.singleton head)
                                  (Word.singleton rightSecond)
                                  rightSuffix
                              simpa [leftSuffix, rightSuffix, Word.append,
                                Word.singleton, Word.append_assoc] using
                                leftCollapse.symm.trans
                                  (lifted.trans rightCollapse)

/-- Assemble the reviewed factor pair only after unrestricted completeness. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-048 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_6165_representative_basis :
    BasisFor S6_6165.table.semigroup basis :=
  S6_6165.representative_basis_of_normalizer normalizer

theorem s6_6165_opposite_basis :
    BasisFor S6_6165.table.semigroup.opposite (reversedBasis basis) :=
  S6_6165.opposite_basis_of_normalizer normalizer

/-- Reviewed transport keeps explicit law derivations and independently
established unrestricted validity implications for both target factors. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank048.Seed

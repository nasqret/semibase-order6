import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank045
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_207Family

/-!
# An unrestricted `S2_4 × S5_207` family seed

The independently complete direct `S5_207` basis has five laws, two of which
change their first variable. The authenticated rank-045 presentation directly
replays both laws behind an arbitrary nonempty context. A structural induction
also proves every nontrivial lower derivation remains in the length-at-least-
three stratum.

The actual five-state marker signature separates the two remaining cases. If
the common left-zero head recurs before the final variable, the displayed
prefix contraction permits a temporary duplicate head after an explicit
middle permutation. If it does not recur, the full marker signature honestly
descends to both suffixes, whose independent lower-factor completeness can be
replayed without adding a temporary head. No finite-table separation or
opposite-factor transport is inferred.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank045.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture

universe u v

private def instantiateFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | marker + 4 => Word.singleton (marker + 4)

/-- The displayed `xxx = xxxx` expands a triple nonempty block. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      ((first ++ first) ++ first)
      (((first ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour first first first first)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxxy = xxy` inserts a third prefix copy. -/
theorem derivesPrefixMultiplicityExpansion
    (first final : Word Nat) :
    Derives basis
      ((first ++ first) ++ final)
      (((first ++ first) ++ first) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [0, 0, 1]) :=
    (Derives.fromBasis (e := law01) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive
      (instantiateFour first final final final)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyzy = xzyy` contextualizes the lower
head-changing `xyx = yxx` law. -/
theorem derivesContextualTerminalRotation
    (stem first second : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ first)
      (((stem ++ second) ++ first) ++ first) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1, 2, 1]) (Word.mk 0 [2, 1, 1]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour stem first second second)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `abcd = acbd` contextualizes the lower
head-changing `xyz = yxz` law. -/
theorem derivesContextualPrefixSwap
    (stem first second final : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ final)
      (((stem ++ second) ++ first) ++ final) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1, 2, 3]) (Word.mk 0 [2, 1, 3]) :=
    Derives.fromBasis (e := law08) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour stem first second final)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The lower doubled-final switch is displayed literally. -/
theorem derivesDoubledFinalSwitch
    (first second : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ second) ++ first)
      ((((first ++ first) ++ second) ++ second) ++ second) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0, 1, 1, 0])
        (Word.mk 0 [0, 1, 1, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateFour first second second second)
  simpa [instantiateFour, Word.bind, Word.append, Word.singleton,
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

/-- Replay all five independently complete lower laws behind any genuine
nonempty initial context, including arbitrary simultaneous substitutions. -/
theorem liftS5_207
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_207.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_207.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPowerExpansion (substitution 0))
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPrefixMultiplicityExpansion
              (substitution 0) (substitution 1))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 0]).bind substitution)
          (stem ++ (Word.mk 1 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualTerminalRotation
            stem (substitution 0) (substitution 1)
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 1 [0, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualPrefixSwap
            stem (substitution 0) (substitution 1) (substitution 2)
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 1, 1, 0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 1, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesDoubledFinalSwitch
              (substitution 0) (substitution 1))
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

/-- Each nontrivial independently certified five-law derivation stays in
the length-at-least-three stratum. -/
theorem lowerDerivation_shortOrLong
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_207.basis left right) :
    ShortLong left right := by
  induction derivation with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_207.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
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

/-- Every permutation strictly between a fixed initial and a fixed final
variable is obtained from genuine lower derivations in context. -/
theorem derivesMiddlePermutation
    (head final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfPrefixFinal (head :: left) final)
      (wordOfPrefixFinal (head :: right) final) := by
  have lower :=
    SemigroupBasis.CoRoots.S5_207.derivesPrefixPermutation
      permutation final
  have lifted :=
    liftS5_207 lower (Word.singleton head) Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  simpa only [wordOfPrefixFinal_cons] using lifted

/-- If the actual head already appears in the nonfinal middle, expose one
copy, use `xxy = xxxy`, and restore the original middle permutation. -/
theorem derivesDuplicateRepeatedHead
    (head final : Nat) (middle : List Nat)
    (present : head ∈ middle) :
    Derives basis
      (wordOfPrefixFinal (head :: middle) final)
      (Word.singleton head ++
        wordOfPrefixFinal (head :: middle) final) := by
  let remainder := middle.erase head
  have expose : middle.Perm (head :: remainder) := by
    simpa [remainder] using List.perm_cons_erase present
  have arrange := derivesMiddlePermutation head final expose
  have duplicate :
      Derives basis
        (wordOfPrefixFinal (head :: head :: remainder) final)
        (wordOfPrefixFinal (head :: head :: head :: remainder) final) := by
    simpa [wordOfPrefixFinal_cons, Word.append_assoc] using
      derivesPrefixMultiplicityExpansion
        (Word.singleton head)
        (wordOfPrefixFinal remainder final)
  have restore :=
    derivesMiddlePermutation head final
      (List.Perm.cons head expose)
  simpa only [wordOfPrefixFinal_cons] using
    arrange.trans (duplicate.trans restore.symm)

/-- Convenient unsplit form of the repeated-head duplication lemma. -/
theorem derivesDuplicateInitial
    (head : Nat) (suffix : Word Nat)
    (present : head ∈ (splitPrefixFinal suffix).1) :
    Derives basis
      (Word.singleton head ++ suffix)
      (Word.singleton head ++
        (Word.singleton head ++ suffix)) := by
  have duplicate :=
    derivesDuplicateRepeatedHead
      head (splitPrefixFinal suffix).2
      (splitPrefixFinal suffix).1 present
  simpa only [wordOfPrefixFinal_cons,
    wordOfPrefixFinal_split] using duplicate

private theorem prefixHeadRepresentation
    (head : Nat) (suffix : Word Nat) :
    Word.singleton head ++ suffix =
      wordOfPrefixFinal
        (head :: (splitPrefixFinal suffix).1)
        (splitPrefixFinal suffix).2 := by
  rw [wordOfPrefixFinal_cons, wordOfPrefixFinal_split]

/-- The genuine five-state signature detects whether the shared initial
variable occurs again before the literal final variable. -/
theorem sharedHeadPrefixMembership
    (head : Nat) (left right : Word Nat)
    (same : SameMarkerSignature
      (Word.singleton head ++ left)
      (Word.singleton head ++ right)) :
    head ∈ (splitPrefixFinal left).1 ↔
      head ∈ (splitPrefixFinal right).1 := by
  let leftSplit := splitPrefixFinal left
  let rightSplit := splitPrefixFinal right
  have states := same head
  rw [prefixHeadRepresentation, prefixHeadRepresentation,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal]
    at states
  have capped :
      Nat.min ((head :: leftSplit.1).count head) 2 =
        Nat.min ((head :: rightSplit.1).count head) 2 := by
    have extracted := congrArg prefixMultiplicityOfState states
    change
      prefixMultiplicityOfState
          (markerStateFrom ((head :: leftSplit.1).count head)
            (leftSplit.2 == head)) =
        prefixMultiplicityOfState
          (markerStateFrom ((head :: rightSplit.1).count head)
            (rightSplit.2 == head)) at extracted
    rw [prefixMultiplicity_markerStateFrom,
      prefixMultiplicity_markerStateFrom] at extracted
    exact extracted
  simp only [List.count_cons_self] at capped
  have zeroIff :
      leftSplit.1.count head = 0 ↔
        rightSplit.1.count head = 0 := by
    simp only [Nat.min_def] at capped
    split at capped <;> split at capped <;> omega
  have membership : head ∈ leftSplit.1 ↔ head ∈ rightSplit.1 := by
    constructor
    · intro leftPresent
      apply Decidable.byContradiction
      intro rightAbsent
      have rightZero := List.count_eq_zero.mpr rightAbsent
      exact
        (List.count_eq_zero.mp (zeroIff.mpr rightZero)) leftPresent
    · intro rightPresent
      apply Decidable.byContradiction
      intro leftAbsent
      have leftZero := List.count_eq_zero.mpr leftAbsent
      exact
        (List.count_eq_zero.mp (zeroIff.mp leftZero)) rightPresent
  simpa [leftSplit, rightSplit] using membership

/-- When the common head is absent from both nonfinal suffix prefixes, its
single initial occurrence can be removed from the exact marker signature. -/
theorem sameMarkerSuffixOfSimplePrefixHead
    (head : Nat) (left right : Word Nat)
    (leftAbsent : head ∉ (splitPrefixFinal left).1)
    (rightAbsent : head ∉ (splitPrefixFinal right).1)
    (same : SameMarkerSignature
      (Word.singleton head ++ left)
      (Word.singleton head ++ right)) :
    SameMarkerSignature left right := by
  intro tested
  let leftSplit := splitPrefixFinal left
  let rightSplit := splitPrefixFinal right
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = left :=
    wordOfPrefixFinal_split left
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = right :=
    wordOfPrefixFinal_split right
  have fullState := same tested
  rw [prefixHeadRepresentation, prefixHeadRepresentation,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal]
    at fullState
  rw [← leftReconstruct, ← rightReconstruct,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal]
  by_cases sameHead : tested = head
  · subst tested
    have leftZero : leftSplit.1.count head = 0 :=
      List.count_eq_zero.mpr (by simpa [leftSplit] using leftAbsent)
    have rightZero : rightSplit.1.count head = 0 :=
      List.count_eq_zero.mpr (by simpa [rightSplit] using rightAbsent)
    cases leftFlag : leftSplit.2 == head <;>
      cases rightFlag : rightSplit.2 == head <;>
        simp [leftSplit, rightSplit, splitMarkerState,
          markerStateFrom, leftZero, rightZero, leftFlag, rightFlag]
          at fullState ⊢
  · simpa [leftSplit, rightSplit, splitMarkerState,
      List.count_cons_of_ne (Ne.symm sameHead)] using fullState

/-- Validity in the exact left-zero factor fixes the first variable. -/
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

/-- Independent unrestricted intersection completeness for the exact
sixteen-law rank-045 basis and both actual factors. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have actualRight :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_207.table.semigroup := by
    simpa [rightTable, SemigroupBasis.CoRoots.S5_207.table] using
      rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_207Family.S5_207.basisFor.2
      identity actualRight
  have signature :=
    SemigroupBasis.CoRoots.S5_207.valid_sameMarkerSignature
      identity actualRight
  rcases lowerDerivation_shortOrLong lower with equal | long
  · rw [equal]
    exact Derives.refl _
  · have heads := leftValid_head identity leftValid
    rcases identity with
      ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
    change leftHead = rightHead at heads
    subst rightHead
    cases leftTail with
    | nil =>
        simp [Word.toList] at long
    | cons leftNext leftRest =>
        cases rightTail with
        | nil =>
            simp [Word.toList] at long
        | cons rightNext rightRest =>
            let leftSuffix : Word Nat := ⟨leftNext, leftRest⟩
            let rightSuffix : Word Nat := ⟨rightNext, rightRest⟩
            have suffixShared :
                SameMarkerSignature
                  (Word.singleton leftHead ++ leftSuffix)
                  (Word.singleton leftHead ++ rightSuffix) := by
              simpa [leftSuffix, rightSuffix,
                Word.singleton, Word.append] using signature
            have membership :=
              sharedHeadPrefixMembership
                leftHead leftSuffix rightSuffix suffixShared
            by_cases repeated :
                leftHead ∈ (splitPrefixFinal leftSuffix).1
            · have rightRepeated := membership.mp repeated
              have leftDuplicate :=
                derivesDuplicateInitial leftHead leftSuffix repeated
              have rightDuplicate :=
                derivesDuplicateInitial leftHead rightSuffix rightRepeated
              have lifted :=
                liftS5_207 lower
                  (Word.singleton leftHead) Word.singleton
              rw [bind_singleton, bind_singleton] at lifted
              simpa [leftSuffix, rightSuffix,
                Word.singleton, Word.append, Word.append_assoc] using
                leftDuplicate.trans (lifted.trans rightDuplicate.symm)
            · have rightAbsent :
                  leftHead ∉ (splitPrefixFinal rightSuffix).1 := by
                intro present
                exact repeated (membership.mpr present)
              have suffixSignature :=
                sameMarkerSuffixOfSimplePrefixHead
                  leftHead leftSuffix rightSuffix
                  repeated rightAbsent suffixShared
              have suffixLower :=
                SemigroupBasis.CoRoots.S5_207.derivesOfSameMarkerSignature
                  leftSuffix rightSuffix suffixSignature
              have lifted :=
                liftS5_207 suffixLower
                  (Word.singleton leftHead) Word.singleton
              rw [bind_singleton, bind_singleton] at lifted
              simpa [leftSuffix, rightSuffix,
                Word.singleton, Word.append] using lifted

/-- The reviewed pair structure follows only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable direct-factor rank-045 seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_5596_representative_basis :
    BasisFor S6_5596.table.semigroup basis :=
  S6_5596.representative_basis_of_normalizer normalizer

theorem s6_5596_opposite_basis :
    BasisFor S6_5596.table.semigroup.opposite (reversedBasis basis) :=
  S6_5596.opposite_basis_of_normalizer normalizer

/-- Reuse the reviewed transport only with explicit displayed-law
derivations and both genuine unrestricted factor-theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank045.Seed

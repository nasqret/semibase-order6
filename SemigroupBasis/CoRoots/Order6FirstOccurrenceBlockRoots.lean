import SemigroupBasis.CoRoots.Order6Class105TraceRoots
import SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots
import SemigroupBasis.CoRoots.Order6ThresholdFour
import SemigroupBasis.CoRoots.S5_345Factors

namespace SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

universe u

/-! ## Exact two-law presentations -/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]

def thresholdFourPowerLaw : Identity Nat := ⟨xxxx, xxxxx⟩
def periodTwoFromThreePowerLaw : Identity Nat := ⟨xxx, xxxxx⟩
def periodThreeFromTwoPowerLaw : Identity Nat := ⟨xx, xxxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def reversedGatherLaw : Identity Nat := ⟨yxx, xyx⟩

def thresholdFourBasis : List (Identity Nat) :=
  [thresholdFourPowerLaw, gatherLaw]

def periodTwoFromThreeBasis : List (Identity Nat) :=
  [periodTwoFromThreePowerLaw, gatherLaw]

def periodThreeFromTwoBasis : List (Identity Nat) :=
  [periodThreeFromTwoPowerLaw, gatherLaw]

def thresholdFourOppositeBasis : List (Identity Nat) :=
  [thresholdFourPowerLaw, reversedGatherLaw]

def periodTwoFromThreeOppositeBasis : List (Identity Nat) :=
  [periodTwoFromThreePowerLaw, reversedGatherLaw]

def periodThreeFromTwoOppositeBasis : List (Identity Nat) :=
  [periodThreeFromTwoPowerLaw, reversedGatherLaw]

theorem reversedBasis_thresholdFourBasis :
    reversedBasis thresholdFourBasis = thresholdFourOppositeBasis := by
  decide

theorem reversedBasis_periodTwoFromThreeBasis :
    reversedBasis periodTwoFromThreeBasis =
      periodTwoFromThreeOppositeBasis := by
  decide

theorem reversedBasis_periodThreeFromTwoBasis :
    reversedBasis periodThreeFromTwoBasis =
      periodThreeFromTwoOppositeBasis := by
  decide

/-! `S6_9503` is intentionally absent. Its law `x = xxxxx` has positive
period four from index one, which is not represented by
`RetainedStateFour.Profile`; adding it here would silently identify the wrong
exponent states. -/

/-! ## The shared two-law derivations -/

private def renameTwo (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n + 2 => n + 2

private theorem derivesGatherWords
    {basis : List (Identity Nat)} (member : gatherLaw ∈ basis)
    (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have base : Derives basis xyx xxy :=
    (Derives.fromBasis (e := gatherLaw) member).symm
  have substituted := Derives.subst base (fun
    | 0 => u
    | 1 => v
    | n + 2 => Word.singleton (n + 2))
  simpa [gatherLaw, xxy, xyx, w, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem gatherOneDerivable
    {basis : List (Identity Nat)} (member : gatherLaw ∈ basis) :
    SemigroupBasis.RetainedStateFour.GatherOneDerivable basis := by
  intro x middle suffix
  cases middle with
  | nil =>
      exact ListDerives.refl _
  | cons y ys =>
      let middleWord := listWordOfCons y ys
      have core := derivesGatherWords member (Word.singleton x) middleWord
      have coreList := ListDerives.ofWord core
      simpa [middleWord, listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using coreList.append suffix

theorem thresholdFourFiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      thresholdFourBasis .thresholdFour := by
  intro x
  have base : Derives thresholdFourBasis xxxxx xxxx :=
    (Derives.fromBasis (e := thresholdFourPowerLaw) (by
      simp [thresholdFourBasis])).symm
  have renamed := base.rename (renameTwo x x)
  simpa [thresholdFourPowerLaw, xxxx, xxxxx, w, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

theorem periodTwoFromThreeFiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      periodTwoFromThreeBasis .periodTwoFromThree := by
  intro x
  have base : Derives periodTwoFromThreeBasis xxxxx xxx :=
    (Derives.fromBasis (e := periodTwoFromThreePowerLaw) (by
      simp [periodTwoFromThreeBasis])).symm
  have renamed := base.rename (renameTwo x x)
  simpa [periodTwoFromThreePowerLaw, xxx, xxxxx, w, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

theorem periodThreeFromTwoFiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      periodThreeFromTwoBasis .periodThreeFromTwo := by
  intro x
  have base : Derives periodThreeFromTwoBasis xxxxx xx :=
    (Derives.fromBasis (e := periodThreeFromTwoPowerLaw) (by
      simp [periodThreeFromTwoBasis])).symm
  have renamed := base.rename (renameTwo x x)
  simpa [periodThreeFromTwoPowerLaw, xx, xxxxx, w, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

/-! ## First-occurrence block combinatorics -/

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat) (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬ keep selected) (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

private theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

private theorem filter_ne_length_lt_cons (x : Nat) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).length <
      (x :: xs).length := by
  have bound :
      (xs.filter (fun y => decide (y ≠ x))).length ≤ xs.length :=
    List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le bound

theorem normalizeBlocks_labelMap
    (profile : SemigroupBasis.RetainedStateFour.Profile) :
    ∀ letters : List Nat,
      (SemigroupBasis.RetainedStateFour.normalizeBlocks profile letters).map
          SemigroupBasis.RetainedStateFour.Block.label =
        firstOccurrenceSequence letters
  | [] => by
      simp [SemigroupBasis.RetainedStateFour.normalizeBlocks,
        firstOccurrenceSequence]
  | x :: xs => by
      simp only [SemigroupBasis.RetainedStateFour.normalizeBlocks,
        List.map_cons, SemigroupBasis.RetainedStateFour.Block.label,
        firstOccurrenceSequence]
      rw [normalizeBlocks_labelMap profile
          (xs.filter (fun y => decide (y ≠ x))),
        firstOccurrenceSequence_filter]
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

theorem sameStateMap_of_exponents
    {profile : SemigroupBasis.RetainedStateFour.Profile}
    {left right : List Nat}
    (exponents : ∀ z,
      profile.exponent (left.count z) =
        profile.exponent (right.count z)) :
    SemigroupBasis.RetainedStateFour.SameStateMap
      (SemigroupBasis.RetainedStateFour.normalizeBlocks profile left)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks profile right) := by
  intro block
  rw [Order6Class105TraceRoots.mem_normalizeBlocks_iff,
    Order6Class105TraceRoots.mem_normalizeBlocks_iff]
  have stateEq :
      profile.state (left.count block.label) =
        profile.state (right.count block.label) := by
    unfold SemigroupBasis.RetainedStateFour.Profile.state
    congr 1
    exact exponents block.label
  constructor
  · rintro ⟨leftMember, blockState⟩
    have leftPositive : 0 < left.count block.label :=
      List.count_pos_iff.mpr leftMember
    have rightPositive : 0 < right.count block.label := by
      have rightExponentPositive :
          0 < profile.exponent (right.count block.label) := by
        rw [← exponents block.label]
        exact profile.exponent_pos leftPositive
      cases rightCount : right.count block.label with
      | zero => simp [rightCount] at rightExponentPositive
      | succ n => omega
    exact ⟨List.count_pos_iff.mp rightPositive,
      blockState.trans stateEq⟩
  · rintro ⟨rightMember, blockState⟩
    have rightPositive : 0 < right.count block.label :=
      List.count_pos_iff.mpr rightMember
    have leftPositive : 0 < left.count block.label := by
      have leftExponentPositive :
          0 < profile.exponent (left.count block.label) := by
        rw [exponents block.label]
        exact profile.exponent_pos rightPositive
      cases leftCount : left.count block.label with
      | zero => simp [leftCount] at leftExponentPositive
      | succ n => omega
    exact ⟨List.count_pos_iff.mp leftPositive,
      blockState.trans stateEq.symm⟩

private theorem eq_of_mem_of_mem_of_map_nodup
    {entries : List α} {project : α → β} {first second : α}
    (mappedNodup : (entries.map project).Nodup)
    (firstMember : first ∈ entries)
    (secondMember : second ∈ entries)
    (projectedEqual : project first = project second) :
    first = second := by
  induction entries with
  | nil =>
      simp at firstMember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headNotMapped, tailMappedNodup⟩
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with rfl | firstTail
      · rcases secondMember with rfl | secondTail
        · rfl
        · exfalso
          apply headNotMapped
          exact List.mem_map.mpr
            ⟨second, secondTail, projectedEqual.symm⟩
      · rcases secondMember with rfl | secondTail
        · exfalso
          apply headNotMapped
          exact List.mem_map.mpr
            ⟨first, firstTail, projectedEqual⟩
        · exact inductionHypothesis tailMappedNodup
            firstTail secondTail

private theorem blocks_eq_of_sameStateMap_of_labelMap_eq :
    ∀ {source target :
        List SemigroupBasis.RetainedStateFour.Block},
      SemigroupBasis.RetainedStateFour.LabelsNodup source →
      SemigroupBasis.RetainedStateFour.LabelsNodup target →
      SemigroupBasis.RetainedStateFour.SameStateMap source target →
      source.map SemigroupBasis.RetainedStateFour.Block.label =
        target.map SemigroupBasis.RetainedStateFour.Block.label →
      source = target
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, labelsEqual => by
      simp at labelsEqual
  | _ :: _, [], _, _, _, labelsEqual => by
      simp at labelsEqual
  | head :: tail, targetHead :: targetTail,
      sourceLabels, targetLabels, sameState, labelsEqual => by
      have headLabels : head.label = targetHead.label := by
        injection labelsEqual
      have headInTarget : head ∈ targetHead :: targetTail :=
        (sameState head).mp (List.Mem.head tail)
      have headsEqual : head = targetHead :=
        eq_of_mem_of_mem_of_map_nodup targetLabels
          headInTarget (List.Mem.head targetTail) headLabels
      subst targetHead
      have sourceParts :
          head.label ∉
              tail.map SemigroupBasis.RetainedStateFour.Block.label ∧
            (tail.map
              SemigroupBasis.RetainedStateFour.Block.label).Nodup := by
        simpa [SemigroupBasis.RetainedStateFour.LabelsNodup] using
          sourceLabels
      have targetParts :
          head.label ∉
              targetTail.map
                SemigroupBasis.RetainedStateFour.Block.label ∧
            (targetTail.map
              SemigroupBasis.RetainedStateFour.Block.label).Nodup := by
        simpa [SemigroupBasis.RetainedStateFour.LabelsNodup] using
          targetLabels
      have headNotTail : head ∉ tail := by
        intro member
        exact sourceParts.1 <|
          List.mem_map.mpr ⟨head, member, rfl⟩
      have headNotTargetTail : head ∉ targetTail := by
        intro member
        exact targetParts.1 <|
          List.mem_map.mpr ⟨head, member, rfl⟩
      have tailSameState :
          SemigroupBasis.RetainedStateFour.SameStateMap
            tail targetTail := by
        intro block
        by_cases blockEq : block = head
        · subst block
          exact iff_of_false headNotTail headNotTargetTail
        · have full := sameState block
          simpa [blockEq] using full
      have tailLabelsEqual :
          tail.map SemigroupBasis.RetainedStateFour.Block.label =
            targetTail.map
              SemigroupBasis.RetainedStateFour.Block.label := by
        injection labelsEqual
      have tailEqual :=
        blocks_eq_of_sameStateMap_of_labelMap_eq
          (source := tail) (target := targetTail)
          sourceParts.2 targetParts.2 tailSameState tailLabelsEqual
      exact congrArg (List.cons head) tailEqual

def noBlocksCommute (_ _ : Nat) : Prop := False

private theorem blocks_nodup
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (labelsNodup :
      SemigroupBasis.RetainedStateFour.LabelsNodup blocks) :
    blocks.Nodup := by
  induction blocks with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have mapped :
          (head.label ::
            tail.map SemigroupBasis.RetainedStateFour.Block.label).Nodup := by
        simpa [SemigroupBasis.RetainedStateFour.LabelsNodup] using
          labelsNodup
      have parts := List.nodup_cons.mp mapped
      apply List.nodup_cons.mpr
      constructor
      · intro member
        exact parts.1 (List.mem_map.mpr ⟨head, member, rfl⟩)
      · exact inductionHypothesis parts.2

private theorem translateSwapClosure
    {independent :
      SemigroupBasis.RetainedStateFour.Block →
        SemigroupBasis.RetainedStateFour.Block → Prop}
    {source target : List SemigroupBasis.RetainedStateFour.Block}
    (derivation :
      SemigroupBasis.BlockTrace.SwapClosure independent source target) :
    SemigroupBasis.RetainedStateFour.SwapClosure
      independent source target := by
  induction derivation with
  | refl blocks =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.refl blocks
  | @trans source middle target first second ihFirst ihSecond =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.trans
        ihFirst ihSecond
  | @cons head source target tailDerivation inductionHypothesis =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.cons
        head inductionHypothesis
  | swap left right suffix allowed =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.swap
        left right suffix allowed

theorem noSwapTraceOrderComplete :
    SemigroupBasis.RetainedStateFour.TraceOrderComplete
      noBlocksCommute := by
  intro source target sourceLabels targetLabels sameState dependentOrder
  have sourceNodup : source.Nodup := blocks_nodup sourceLabels
  have targetNodup : target.Nodup := blocks_nodup targetLabels
  have permutation : source.Perm target :=
    SemigroupBasis.BlockTrace.perm_of_nodup_mem_iff
      sourceNodup targetNodup sameState
  have generic :
      SemigroupBasis.BlockTrace.SwapClosure
        (SemigroupBasis.RetainedStateFour.BlocksIndependent
          noBlocksCommute) source target :=
    SemigroupBasis.BlockTrace.SwapClosure.of_perm_of_dependent_order
      sourceNodup targetNodup permutation (by
        intro left right leftMember rightMember blocked
        simpa [SemigroupBasis.BlockTrace.Precedes,
          SemigroupBasis.RetainedStateFour.Precedes] using
            dependentOrder left right leftMember rightMember blocked)
  exact translateSwapClosure generic

private theorem noSwapAdjacentDerivable
    (basis : List (Identity Nat)) :
    SemigroupBasis.RetainedStateFour.AdjacentSwapDerivable
      basis noBlocksCommute := by
  intro left right allowed
  exact False.elim <| by
    simpa [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      noBlocksCommute] using allowed

/-- Unrestricted first-occurrence-block completeness for every profile
already represented by `RetainedStateFour.Profile`. Equal exponent states
give the same labelled blocks, and equal first-occurrence sequences fix every
pair order. Since no block pair commutes, the trace replay uses no swaps. -/
theorem basisFor_of_firstOccurrenceBlockInvariants
    {S : Type u} (candidate : Semigroup S)
    (basis : List (Identity Nat))
    (profile : SemigroupBasis.RetainedStateFour.Profile)
    (models : Models candidate basis)
    (gatherOne :
      SemigroupBasis.RetainedStateFour.GatherOneDerivable basis)
    (reduceFive :
      SemigroupBasis.RetainedStateFour.FiveReductionDerivable
        basis profile)
    (validFirstOccurrences : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList)
    (validExponents : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        ∀ letter,
          profile.exponent (identity.lhs.toList.count letter) =
            profile.exponent (identity.rhs.toList.count letter)) :
    BasisFor candidate basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have sameState :=
    sameStateMap_of_exponents (validExponents identity valid)
  have labelMapsEqual :
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.lhs.toList).map
            SemigroupBasis.RetainedStateFour.Block.label =
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.rhs.toList).map
            SemigroupBasis.RetainedStateFour.Block.label := by
    rw [normalizeBlocks_labelMap, normalizeBlocks_labelMap]
    exact validFirstOccurrences identity valid
  have normalBlocksEqual :
      SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.lhs.toList =
        SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.rhs.toList :=
    blocks_eq_of_sameStateMap_of_labelMap_eq
      (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
        profile identity.lhs.toList)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
        profile identity.rhs.toList)
      sameState labelMapsEqual
  have dependentOrder :
      SemigroupBasis.RetainedStateFour.SameDependentOrder
        noBlocksCommute
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.lhs.toList)
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          profile identity.rhs.toList) := by
    intro left right leftMember rightMember blocked
    rw [normalBlocksEqual]
  have listed :=
    SemigroupBasis.RetainedStateFour.derivesOfTrace_of_laws
      gatherOne reduceFive noSwapTraceOrderComplete
      sameState dependentOrder (noSwapAdjacentDerivable basis)
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              exact listed.toWord

/-! ## Finite semantic helpers -/

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis (basis : List (Identity Nat)) :
    List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem models_of_finite_checks
    (candidate : FiniteTable) (basis : List (Identity Nat))
    (roundTrip : basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true)
    (checked :
      (finiteBasis basis).all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

private def exponentValuation
    {S : Type u} (target identity : S) (selected : Nat) : Nat → S :=
  fun letter => if letter = selected then target else identity

private theorem exponentValuationFold
    {S : Type u} (G : Semigroup S) (state : Nat → S)
    (target identity : S)
    (mulTarget : ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity : ∀ n, G.mul (state n) identity = state n)
    (selected : Nat) (letters : List Nat) (acc : Nat) :
    letters.foldl
        (fun current letter =>
          G.mul current
            (exponentValuation target identity selected letter))
        (state acc) =
      state (acc + letters.count selected) := by
  induction letters generalizing acc with
  | nil => simp
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [List.count_cons_self]
        rw [show exponentValuation target identity selected selected =
            target by simp [exponentValuation]]
        rw [mulTarget, inductionHypothesis]
        congr 1
        omega
      · rw [List.count_cons_of_ne equal]
        rw [show exponentValuation target identity selected letter =
            identity by simp [exponentValuation, equal]]
        rw [mulIdentity, inductionHypothesis]

private theorem evalExponentValuation
    {S : Type u} (G : Semigroup S) (state : Nat → S)
    (target identity : S)
    (stateZero : state 0 = identity)
    (stateOne : state 1 = target)
    (mulTarget : ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity : ∀ n, G.mul (state n) identity = state n)
    (selected : Nat) (word : Word Nat) :
    G.eval (exponentValuation target identity selected) word =
      state (word.toList.count selected) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              G.mul current
                (exponentValuation target identity selected letter))
            (exponentValuation target identity selected head) =
          state ((head :: tail).count selected)
      by_cases headEqual : head = selected
      · subst head
        rw [List.count_cons_self]
        rw [show exponentValuation target identity selected selected =
            state 1 by simp [exponentValuation, stateOne]]
        rw [exponentValuationFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega
      · rw [List.count_cons_of_ne headEqual]
        rw [show exponentValuation target identity selected head =
            state 0 by
          simp [exponentValuation, headEqual, stateZero]]
        rw [exponentValuationFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-! ## `S6_5690`: threshold four -/

namespace S6_5690

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,3,1,2],[1,1,1,1,1,3],
  [1,3,1,2,1,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 2 0 1 b else
      if a = 2 then row6 0 0 0 0 0 2 b else
        if a = 3 then row6 0 2 0 1 0 3 b else
          if a = 4 then row6 4 4 4 4 4 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "81e8bf8c17086e03417a7f8a961d8bbaefb880a1d415ebf35bf2e51ebbb9673c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup thresholdFourBasis :=
  models_of_finite_checks table thresholdFourBasis (by decide) (by decide)

def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem validFirstOccurrenceSequence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity (firstOccurrenceEmbedding.pullback_identity identity valid)

def exponentEmbedding :
    Embedding SemigroupBasis.CoRoots.S5_217.table.semigroup
      table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.thresholdFour.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.thresholdFour.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.CoRoots.S5_217.valid_capped_count identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup thresholdFourBasis :=
  basisFor_of_firstOccurrenceBlockInvariants
    table.semigroup thresholdFourBasis .thresholdFour models
    (gatherOneDerivable (by simp [thresholdFourBasis]))
    thresholdFourFiveReductionDerivable
    validFirstOccurrenceSequence validExponents

theorem opposite_basis :
    BasisFor table.semigroup.opposite thresholdFourOppositeBasis := by
  rw [← reversedBasis_thresholdFourBasis]
  exact representative_basis.oppositeReversed

end S6_5690

/-! ## `S6_9597`: period two from index three -/

namespace S6_9597

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,2,2,1],[1,1,2,3,3,1],
  [1,2,3,4,5,6],[1,2,3,5,4,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 1 1 0 b else
      if a = 2 then row6 0 0 1 2 2 0 b else
        if a = 3 then row6 0 1 2 3 4 5 b else
          if a = 4 then row6 0 1 2 4 3 5 b else
            row6 5 5 5 5 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "761d93889c2908b6632ce217d9bfe548b72cc8a950b2b4a09483043ee7800ebf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup periodTwoFromThreeBasis :=
  models_of_finite_checks
    table periodTwoFromThreeBasis (by decide) (by decide)

def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem validFirstOccurrenceSequence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity (firstOccurrenceEmbedding.pullback_identity identity valid)

private def thresholdState (n : Nat) : Fin 6 :=
  if n = 0 then 3 else if n = 1 then 2 else
    if n = 2 then 1 else 0

private def parityState (n : Nat) : Fin 6 :=
  if n % 2 = 0 then 3 else 4

private theorem mulIdentity (value : Fin 6) :
    table.semigroup.mul value (3 : Fin 6) = value := by
  exact by decide +revert

private theorem thresholdMulTarget (n : Nat) :
    table.semigroup.mul (thresholdState n) (2 : Fin 6) =
      thresholdState (n + 1) := by
  by_cases nZero : n = 0
  · subst n
    rfl
  · by_cases nOne : n = 1
    · subst n
      rfl
    · by_cases nTwo : n = 2
      · subst n
        rfl
      · simp [table, FiniteTable.semigroup, mul, row6,
          thresholdState, nZero, nOne, nTwo,
          show n + 1 ≠ 0 by omega,
          show n + 1 ≠ 1 by omega,
          show n + 1 ≠ 2 by omega]

private theorem parityMulTarget (n : Nat) :
    table.semigroup.mul (parityState n) (4 : Fin 6) =
      parityState (n + 1) := by
  by_cases even : n % 2 = 0
  · have nextOdd : (n + 1) % 2 = 1 := by omega
    simp [table, FiniteTable.semigroup, mul, row6,
      parityState, even, nextOdd]
  · have odd : n % 2 = 1 := by omega
    have nextEven : (n + 1) % 2 = 0 := by omega
    simp [table, FiniteTable.semigroup, mul, row6,
      parityState, even, odd, nextEven]

private theorem evalThreshold (letter : Nat) (word : Word Nat) :
    table.semigroup.eval
        (exponentValuation (2 : Fin 6) (3 : Fin 6) letter) word =
      thresholdState (word.toList.count letter) :=
  evalExponentValuation table.semigroup thresholdState
    (2 : Fin 6) (3 : Fin 6) (by rfl) (by rfl)
    thresholdMulTarget (fun n => mulIdentity (thresholdState n))
    letter word

private theorem evalParity (letter : Nat) (word : Word Nat) :
    table.semigroup.eval
        (exponentValuation (4 : Fin 6) (3 : Fin 6) letter) word =
      parityState (word.toList.count letter) :=
  evalExponentValuation table.semigroup parityState
    (4 : Fin 6) (3 : Fin 6) (by rfl) (by rfl)
    parityMulTarget (fun n => mulIdentity (parityState n))
    letter word

private def exponentCode (threshold parity : Fin 6) : Nat :=
  if threshold = 3 then 0 else if threshold = 2 then 1 else
    if threshold = 1 then 2 else if parity = 4 then 3 else 4

private theorem exponentCodeStates (n : Nat) :
    exponentCode (thresholdState n) (parityState n) =
      periodTwoFromThreeExponent n := by
  by_cases nZero : n = 0
  · subst n
    rfl
  · by_cases nOne : n = 1
    · subst n
      rfl
    · by_cases nTwo : n = 2
      · subst n
        rfl
      · have nAtLeastThree : 3 ≤ n := by omega
        by_cases even : n % 2 = 0
        · have nextOdd : (n + 1) % 2 = 1 := by omega
          simp [exponentCode, thresholdState, parityState,
            periodTwoFromThreeExponent, nZero, nOne, nTwo,
            even, nextOdd, show ¬ n < 3 by omega]
        · have odd : n % 2 = 1 := by omega
          have nextEven : (n + 1) % 2 = 0 := by omega
          simp [exponentCode, thresholdState, parityState,
            periodTwoFromThreeExponent, nZero, nOne, nTwo,
            even, odd, nextEven, show ¬ n < 3 by omega]

private theorem exponent_eq_of_states
    (m n : Nat)
    (thresholdEq : thresholdState m = thresholdState n)
    (parityEq : parityState m = parityState n) :
    periodTwoFromThreeExponent m = periodTwoFromThreeExponent n := by
  calc
    periodTwoFromThreeExponent m =
        exponentCode (thresholdState m) (parityState m) :=
      (exponentCodeStates m).symm
    _ = exponentCode (thresholdState n) (parityState n) := by
      rw [thresholdEq, parityEq]
    _ = periodTwoFromThreeExponent n := exponentCodeStates n

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  intro letter
  have thresholdEq :=
    valid (exponentValuation (2 : Fin 6) (3 : Fin 6) letter)
  have parityEq :=
    valid (exponentValuation (4 : Fin 6) (3 : Fin 6) letter)
  rw [evalThreshold, evalThreshold] at thresholdEq
  rw [evalParity, evalParity] at parityEq
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    exponent_eq_of_states _ _ thresholdEq parityEq

theorem representative_basis :
    BasisFor table.semigroup periodTwoFromThreeBasis :=
  basisFor_of_firstOccurrenceBlockInvariants
    table.semigroup periodTwoFromThreeBasis .periodTwoFromThree models
    (gatherOneDerivable (by simp [periodTwoFromThreeBasis]))
    periodTwoFromThreeFiveReductionDerivable
    validFirstOccurrenceSequence validExponents

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      periodTwoFromThreeOppositeBasis := by
  rw [← reversedBasis_periodTwoFromThreeBasis]
  exact representative_basis.oppositeReversed

end S6_9597

/-! ## `S6_14923`: period three from index two -/

namespace S6_14923

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,2,2,2],[3,3,3,3,3,3],
  [1,2,3,4,5,6],[1,2,3,5,6,4],[1,2,3,6,4,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 1 1 1 b else
      if a = 2 then row6 2 2 2 2 2 2 b else
        if a = 3 then row6 0 1 2 3 4 5 b else
          if a = 4 then row6 0 1 2 4 5 3 b else
            row6 0 1 2 5 3 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "28eb0645cbc4140493c3d85f418148a0016503422e889fb0effd2e8d7667a9a6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup periodThreeFromTwoBasis :=
  models_of_finite_checks
    table periodThreeFromTwoBasis (by decide) (by decide)

def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (3 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem validFirstOccurrenceSequence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity (firstOccurrenceEmbedding.pullback_identity identity valid)

private def thresholdState (n : Nat) : Fin 6 :=
  if n = 0 then 3 else if n = 1 then 1 else 0

private def periodState (n : Nat) : Fin 6 :=
  if n % 3 = 0 then 3 else if n % 3 = 1 then 4 else 5

private theorem mulIdentity (value : Fin 6) :
    table.semigroup.mul value (3 : Fin 6) = value := by
  exact by decide +revert

private theorem thresholdMulTarget (n : Nat) :
    table.semigroup.mul (thresholdState n) (1 : Fin 6) =
      thresholdState (n + 1) := by
  by_cases nZero : n = 0
  · subst n
    rfl
  · by_cases nOne : n = 1
    · subst n
      rfl
    · simp [table, FiniteTable.semigroup, mul, row6,
        thresholdState, nZero, nOne,
        show n + 1 ≠ 0 by omega,
        show n + 1 ≠ 1 by omega]

private theorem periodMulTarget (n : Nat) :
    table.semigroup.mul (periodState n) (4 : Fin 6) =
      periodState (n + 1) := by
  by_cases remainderZero : n % 3 = 0
  · have nextRemainder : (n + 1) % 3 = 1 := by omega
    simp [table, FiniteTable.semigroup, mul, row6,
      periodState, remainderZero, nextRemainder]
  · by_cases remainderOne : n % 3 = 1
    · have nextRemainder : (n + 1) % 3 = 2 := by omega
      simp [table, FiniteTable.semigroup, mul, row6,
        periodState, remainderZero, remainderOne, nextRemainder]
    · have remainderTwo : n % 3 = 2 := by omega
      have nextRemainder : (n + 1) % 3 = 0 := by omega
      simp [table, FiniteTable.semigroup, mul, row6,
        periodState, remainderZero, remainderOne,
        remainderTwo, nextRemainder]

private theorem evalThreshold (letter : Nat) (word : Word Nat) :
    table.semigroup.eval
        (exponentValuation (1 : Fin 6) (3 : Fin 6) letter) word =
      thresholdState (word.toList.count letter) :=
  evalExponentValuation table.semigroup thresholdState
    (1 : Fin 6) (3 : Fin 6) (by rfl) (by rfl)
    thresholdMulTarget (fun n => mulIdentity (thresholdState n))
    letter word

private theorem evalPeriod (letter : Nat) (word : Word Nat) :
    table.semigroup.eval
        (exponentValuation (4 : Fin 6) (3 : Fin 6) letter) word =
      periodState (word.toList.count letter) :=
  evalExponentValuation table.semigroup periodState
    (4 : Fin 6) (3 : Fin 6) (by rfl) (by rfl)
    periodMulTarget (fun n => mulIdentity (periodState n))
    letter word

private def exponentCode (threshold period : Fin 6) : Nat :=
  if threshold = 3 then 0 else if threshold = 1 then 1 else
    if period = 5 then 2 else if period = 3 then 3 else 4

private theorem exponentCodeStates (n : Nat) :
    exponentCode (thresholdState n) (periodState n) =
      periodThreeFromTwoExponent n := by
  by_cases nZero : n = 0
  · subst n
    rfl
  · by_cases nOne : n = 1
    · subst n
      rfl
    · have nAtLeastTwo : 2 ≤ n := by omega
      by_cases remainderZero : n % 3 = 0
      · have nextRemainder : (n + 1) % 3 = 1 := by omega
        simp [exponentCode, thresholdState, periodState,
          periodThreeFromTwoExponent, nZero, nOne,
          remainderZero, nextRemainder,
          show ¬ n < 2 by omega]
      · by_cases remainderOne : n % 3 = 1
        · have nextRemainder : (n + 1) % 3 = 2 := by omega
          simp [exponentCode, thresholdState, periodState,
            periodThreeFromTwoExponent, nZero, nOne,
            remainderZero, remainderOne, nextRemainder,
            show ¬ n < 2 by omega]
        · have remainderTwo : n % 3 = 2 := by omega
          have nextRemainder : (n + 1) % 3 = 0 := by omega
          simp [exponentCode, thresholdState, periodState,
            periodThreeFromTwoExponent, nZero, nOne,
            remainderZero, remainderOne, remainderTwo,
            nextRemainder, show ¬ n < 2 by omega]

private theorem exponent_eq_of_states
    (m n : Nat)
    (thresholdEq : thresholdState m = thresholdState n)
    (periodEq : periodState m = periodState n) :
    periodThreeFromTwoExponent m = periodThreeFromTwoExponent n := by
  calc
    periodThreeFromTwoExponent m =
        exponentCode (thresholdState m) (periodState m) :=
      (exponentCodeStates m).symm
    _ = exponentCode (thresholdState n) (periodState n) := by
      rw [thresholdEq, periodEq]
    _ = periodThreeFromTwoExponent n := exponentCodeStates n

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.rhs.toList.count letter) := by
  intro letter
  have thresholdEq :=
    valid (exponentValuation (1 : Fin 6) (3 : Fin 6) letter)
  have periodEq :=
    valid (exponentValuation (4 : Fin 6) (3 : Fin 6) letter)
  rw [evalThreshold, evalThreshold] at thresholdEq
  rw [evalPeriod, evalPeriod] at periodEq
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    exponent_eq_of_states _ _ thresholdEq periodEq

theorem representative_basis :
    BasisFor table.semigroup periodThreeFromTwoBasis :=
  basisFor_of_firstOccurrenceBlockInvariants
    table.semigroup periodThreeFromTwoBasis .periodThreeFromTwo models
    (gatherOneDerivable (by simp [periodThreeFromTwoBasis]))
    periodThreeFromTwoFiveReductionDerivable
    validFirstOccurrenceSequence validExponents

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      periodThreeFromTwoOppositeBasis := by
  rw [← reversedBasis_periodThreeFromTwoBasis]
  exact representative_basis.oppositeReversed

end S6_14923

end SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots

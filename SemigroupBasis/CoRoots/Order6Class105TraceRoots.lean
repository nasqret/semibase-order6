import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.Examples.CommutativePeriodTwoFromThreeOrderFive
import SemigroupBasis.FiniteNilpotent
import SemigroupBasis.FiniteReflection
import SemigroupBasis.RetainedStateFourNormalizer
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.Order6Class105TraceRoots

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

/-! ## The exact eleven-law trace basis -/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def yyx : Word Nat := w 1 [1, 0]
def xyyy : Word Nat := w 0 [1, 1, 1]
def yyyx : Word Nat := w 1 [1, 1, 0]
def xyyyy : Word Nat := w 0 [1, 1, 1, 1]
def yyyyx : Word Nat := w 1 [1, 1, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def yyyxx : Word Nat := w 1 [1, 1, 0, 0]
def xxyyyy : Word Nat := w 0 [0, 1, 1, 1, 1]
def yyyyxx : Word Nat := w 1 [1, 1, 1, 0, 0]
def xxxyyy : Word Nat := w 0 [0, 0, 1, 1, 1]
def yyyxxx : Word Nat := w 1 [1, 1, 0, 0, 0]
def xxxyyyy : Word Nat := w 0 [0, 0, 1, 1, 1, 1]
def yyyyxxx : Word Nat := w 1 [1, 1, 1, 0, 0, 0]
def xxxxyyyy : Word Nat := w 0 [0, 0, 0, 1, 1, 1, 1]
def yyyyxxxx : Word Nat := w 1 [1, 1, 1, 0, 0, 0, 0]

def powerLaw : Identity Nat := ⟨xxx, xxxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def swap12Law : Identity Nat := ⟨xyy, yyx⟩
def swap13Law : Identity Nat := ⟨xyyy, yyyx⟩
def swap14Law : Identity Nat := ⟨xyyyy, yyyyx⟩
def swap22Law : Identity Nat := ⟨xxyy, yyxx⟩
def swap23Law : Identity Nat := ⟨xxyyy, yyyxx⟩
def swap24Law : Identity Nat := ⟨xxyyyy, yyyyxx⟩
def swap33Law : Identity Nat := ⟨xxxyyy, yyyxxx⟩
def swap34Law : Identity Nat := ⟨xxxyyyy, yyyyxxx⟩
def swap44Law : Identity Nat := ⟨xxxxyyyy, yyyyxxxx⟩

/-- The accepted class-105 basis in catalogue orientation. Its only dependent
retained-state pair is `(1, 1)`. -/
def sourceBasis : List (Identity Nat) :=
  [powerLaw, swap44Law, swap33Law, swap34Law, gatherLaw,
    swap22Law, swap23Law, swap24Law, swap12Law, swap13Law, swap14Law]

private def renameTwo (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n + 2 => n + 2

private theorem derivesGatherWords (u v : Word Nat) :
    Derives sourceBasis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have base : Derives sourceBasis xyx xxy :=
    (Derives.fromBasis (e := gatherLaw) (by
      simp [sourceBasis])).symm
  have substituted := Derives.subst base (fun
    | 0 => u
    | 1 => v
    | n + 2 => Word.singleton (n + 2))
  simpa [gatherLaw, xxy, xyx, w, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem gatherOneDerivable : SemigroupBasis.RetainedStateFour.GatherOneDerivable sourceBasis := by
  intro x middle suffix
  cases middle with
  | nil =>
      exact ListDerives.refl _
  | cons y ys =>
      let middleWord := listWordOfCons y ys
      have core := derivesGatherWords (Word.singleton x) middleWord
      have coreList := ListDerives.ofWord core
      simpa [middleWord, listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using coreList.append suffix

theorem fiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable sourceBasis .periodTwoFromThree := by
  intro x
  have base : Derives sourceBasis xxxxx xxx :=
    (Derives.fromBasis (e := powerLaw) (by
      simp [sourceBasis])).symm
  have renamed := base.rename (renameTwo x x)
  simpa [powerLaw, xxx, xxxxx, w, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using ListDerives.ofWord renamed

private theorem derivesFromSource (identity : Identity Nat)
    (member : identity ∈ sourceBasis) :
    Derives sourceBasis identity.lhs identity.rhs :=
  Derives.fromBasis member

private theorem swap12 (x y : Nat) :
    ListDerives sourceBasis [x, y, y] [y, y, x] := by
  have renamed :=
    (derivesFromSource swap12Law (by decide)).rename (renameTwo x y)
  simpa [swap12Law, xyy, yyx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap13 (x y : Nat) :
    ListDerives sourceBasis [x, y, y, y] [y, y, y, x] := by
  have renamed :=
    (derivesFromSource swap13Law (by decide)).rename (renameTwo x y)
  simpa [swap13Law, xyyy, yyyx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap14 (x y : Nat) :
    ListDerives sourceBasis [x, y, y, y, y] [y, y, y, y, x] := by
  have renamed :=
    (derivesFromSource swap14Law (by decide)).rename (renameTwo x y)
  simpa [swap14Law, xyyyy, yyyyx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap22 (x y : Nat) :
    ListDerives sourceBasis [x, x, y, y] [y, y, x, x] := by
  have renamed :=
    (derivesFromSource swap22Law (by decide)).rename (renameTwo x y)
  simpa [swap22Law, xxyy, yyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap23 (x y : Nat) :
    ListDerives sourceBasis [x, x, y, y, y] [y, y, y, x, x] := by
  have renamed :=
    (derivesFromSource swap23Law (by decide)).rename (renameTwo x y)
  simpa [swap23Law, xxyyy, yyyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap24 (x y : Nat) :
    ListDerives sourceBasis [x, x, y, y, y, y] [y, y, y, y, x, x] := by
  have renamed :=
    (derivesFromSource swap24Law (by decide)).rename (renameTwo x y)
  simpa [swap24Law, xxyyyy, yyyyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap33 (x y : Nat) :
    ListDerives sourceBasis [x, x, x, y, y, y] [y, y, y, x, x, x] := by
  have renamed :=
    (derivesFromSource swap33Law (by decide)).rename (renameTwo x y)
  simpa [swap33Law, xxxyyy, yyyxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap34 (x y : Nat) :
    ListDerives sourceBasis [x, x, x, y, y, y, y]
      [y, y, y, y, x, x, x] := by
  have renamed :=
    (derivesFromSource swap34Law (by decide)).rename (renameTwo x y)
  simpa [swap34Law, xxxyyyy, yyyyxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap44 (x y : Nat) :
    ListDerives sourceBasis [x, x, x, x, y, y, y, y]
      [y, y, y, y, x, x, x, x] := by
  have renamed :=
    (derivesFromSource swap44Law (by decide)).rename (renameTwo x y)
  simpa [swap44Law, xxxxyyyy, yyyyxxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

def stateCommutes (left right : Nat) : Prop :=
  left ≠ 1 ∨ right ≠ 1

theorem adjacentSwapDerivable :
    SemigroupBasis.RetainedStateFour.AdjacentSwapDerivable sourceBasis stateCommutes := by
  rintro ⟨leftLabel, leftState⟩ ⟨rightLabel, rightState⟩ allowed
  cases leftState <;> cases rightState
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent, stateCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap12 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap13 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap14 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap12 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap22 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap23 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap24 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap13 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap23 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap33 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap34 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap14 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap24 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using (swap34 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using swap44 leftLabel rightLabel

/-! ## Generic state-four trace combinatorics -/

private theorem blocks_nodup {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (labelsNodup : SemigroupBasis.RetainedStateFour.LabelsNodup blocks) :
    blocks.Nodup := by
  induction blocks with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have mapped :
          (head.label :: tail.map SemigroupBasis.RetainedStateFour.Block.label).Nodup := by
        simpa [SemigroupBasis.RetainedStateFour.LabelsNodup] using labelsNodup
      have parts := List.nodup_cons.mp mapped
      apply List.nodup_cons.mpr
      constructor
      · intro member
        exact parts.1 (List.mem_map.mpr ⟨head, member, rfl⟩)
      · exact inductionHypothesis parts.2

private theorem translateSwapClosure
    {independent : SemigroupBasis.RetainedStateFour.Block → SemigroupBasis.RetainedStateFour.Block → Prop}
    {source target : List SemigroupBasis.RetainedStateFour.Block}
    (derivation : SemigroupBasis.BlockTrace.SwapClosure independent source target) :
    SemigroupBasis.RetainedStateFour.SwapClosure independent source target := by
  induction derivation with
  | refl blocks =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.refl blocks
  | @trans source middle target first second ihFirst ihSecond =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.trans ihFirst ihSecond
  | @cons head source target tailDerivation inductionHypothesis =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.cons head inductionHypothesis
  | swap left right suffix allowed =>
      exact SemigroupBasis.RetainedStateFour.SwapClosure.swap left right suffix allowed

theorem traceOrderComplete : SemigroupBasis.RetainedStateFour.TraceOrderComplete stateCommutes := by
  intro source target sourceLabels targetLabels sameState dependentOrder
  have sourceNodup : source.Nodup := blocks_nodup sourceLabels
  have targetNodup : target.Nodup := blocks_nodup targetLabels
  have permutation : source.Perm target :=
    SemigroupBasis.BlockTrace.perm_of_nodup_mem_iff sourceNodup targetNodup sameState
  have generic :
      SemigroupBasis.BlockTrace.SwapClosure (SemigroupBasis.RetainedStateFour.BlocksIndependent stateCommutes)
        source target :=
    SemigroupBasis.BlockTrace.SwapClosure.of_perm_of_dependent_order
      sourceNodup targetNodup permutation (by
        intro left right leftMember rightMember blocked
        simpa [SemigroupBasis.BlockTrace.Precedes, SemigroupBasis.RetainedStateFour.Precedes] using
          dependentOrder left right leftMember rightMember blocked)
  exact translateSwapClosure generic

/-! ## Capped multiplicities determine the retained-state map -/

private theorem filter_ne_length_lt_cons (x : Nat) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).length <
      (x :: xs).length := by
  have bound :
      (xs.filter (fun y => decide (y ≠ x))).length ≤ xs.length :=
    List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le bound

private theorem count_filter_ne_of_ne
    {x z : Nat} (different : z ≠ x) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons y ys inductionHypothesis =>
      by_cases yEq : y = x
      · subst y
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact inductionHypothesis
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [inductionHypothesis]

/-- A normalized block is completely characterized by its source label and
the profile state of that label's total multiplicity. -/
theorem mem_normalizeBlocks_iff (profile : SemigroupBasis.RetainedStateFour.Profile) :
    ∀ (letters : List Nat) (block : SemigroupBasis.RetainedStateFour.Block),
      block ∈ SemigroupBasis.RetainedStateFour.normalizeBlocks profile letters ↔
        block.label ∈ letters ∧
          block.state = profile.state (letters.count block.label)
  | [], block => by
      simp [SemigroupBasis.RetainedStateFour.normalizeBlocks]
  | x :: xs, block => by
      rw [SemigroupBasis.RetainedStateFour.normalizeBlocks]
      simp only [List.mem_cons]
      by_cases labelEq : block.label = x
      · constructor
        · rintro (headEq | tailMember)
          · subst block
            simp
          · have inFiltered :=
              SemigroupBasis.RetainedStateFour.label_mem_of_mem_normalizeBlocks profile tailMember
            have labelNe : block.label ≠ x := by
              simpa using (List.mem_filter.mp inFiltered).2
            exact False.elim (labelNe labelEq)
        · rintro ⟨_, stateEq⟩
          apply Or.inl
          cases block with
          | mk label state =>
              simp only [SemigroupBasis.RetainedStateFour.Block.label, SemigroupBasis.RetainedStateFour.Block.state] at labelEq stateEq ⊢
              subst label
              cases stateEq
              rfl
      · have inductionHypothesis :=
          mem_normalizeBlocks_iff profile
            (xs.filter (fun y => decide (y ≠ x))) block
        constructor
        · rintro (headEq | tailMember)
          · have labelsEqual := congrArg SemigroupBasis.RetainedStateFour.Block.label headEq
            exact False.elim (labelEq labelsEqual)
          · have tailData := inductionHypothesis.mp tailMember
            have inXs : block.label ∈ xs :=
              (List.mem_filter.mp tailData.1).1
            refine ⟨Or.inr inXs, ?_⟩
            have tailState := tailData.2
            rw [count_filter_ne_of_ne labelEq xs] at tailState
            simpa [List.count_cons_of_ne (Ne.symm labelEq)] using tailState
        · rintro ⟨sourceMember, stateEq⟩
          apply Or.inr
          apply inductionHypothesis.mpr
          have inXs : block.label ∈ xs := by
            simpa [labelEq] using sourceMember
          constructor
          · exact List.mem_filter.mpr ⟨inXs, by simpa using labelEq⟩
          · have sourceState :
                block.state = profile.state (xs.count block.label) := by
              simpa [List.count_cons_of_ne (Ne.symm labelEq)] using stateEq
            rw [count_filter_ne_of_ne labelEq xs]
            exact sourceState
termination_by
  letters _ => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

theorem sameStateMap_of_exponents
    {left right : List Nat}
    (exponents : ∀ z,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (left.count z) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (right.count z)) :
    SemigroupBasis.RetainedStateFour.SameStateMap
      (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree left)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree right) := by
  intro block
  rw [mem_normalizeBlocks_iff, mem_normalizeBlocks_iff]
  have stateEq :
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.state (left.count block.label) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.state (right.count block.label) := by
    unfold SemigroupBasis.RetainedStateFour.Profile.state
    congr 1
    exact exponents block.label
  constructor
  · rintro ⟨leftMember, blockState⟩
    have leftPositive : 0 < left.count block.label :=
      List.count_pos_iff.mpr leftMember
    have rightPositive : 0 < right.count block.label := by
      have rightExponentPositive :
          0 < SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
            (right.count block.label) := by
        rw [← exponents block.label]
        exact SemigroupBasis.RetainedStateFour.Profile.exponent_pos leftPositive
      cases rightCount : right.count block.label with
      | zero =>
          simp [rightCount] at rightExponentPositive
      | succ n =>
          omega
    exact ⟨List.count_pos_iff.mp rightPositive,
      blockState.trans stateEq⟩
  · rintro ⟨rightMember, blockState⟩
    have rightPositive : 0 < right.count block.label :=
      List.count_pos_iff.mpr rightMember
    have leftPositive : 0 < left.count block.label := by
      have leftExponentPositive :
          0 < SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
            (left.count block.label) := by
        rw [exponents block.label]
        exact SemigroupBasis.RetainedStateFour.Profile.exponent_pos rightPositive
      cases leftCount : left.count block.label with
      | zero =>
          simp [leftCount] at leftExponentPositive
      | succ n =>
          omega
    exact ⟨List.count_pos_iff.mp leftPositive,
      blockState.trans stateEq.symm⟩

/-! ## The two-singleton order separator -/

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
        · exact inductionHypothesis tailMappedNodup firstTail secondTail

private theorem not_precedes_self
    {block : SemigroupBasis.RetainedStateFour.Block} {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (nodup : blocks.Nodup) :
    ¬ SemigroupBasis.RetainedStateFour.Precedes block block blocks := by
  rintro ⟨before, after, shape, member⟩
  rw [shape] at nodup
  have suffixNodup : (block :: after).Nodup :=
    (List.nodup_append.mp nodup).2.1
  exact (List.nodup_cons.mp suffixNodup).1 member

private theorem precedes_or_reverse
    {left right : SemigroupBasis.RetainedStateFour.Block} {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (different : left ≠ right)
    (leftMember : left ∈ blocks) (rightMember : right ∈ blocks) :
    SemigroupBasis.RetainedStateFour.Precedes left right blocks ∨
      SemigroupBasis.RetainedStateFour.Precedes right left blocks := by
  induction blocks with
  | nil =>
      simp at leftMember
  | cons head tail inductionHypothesis =>
      by_cases headLeft : head = left
      · subst head
        left
        simpa [SemigroupBasis.RetainedStateFour.Precedes] using
          (SemigroupBasis.BlockTrace.precedes_cons_self
            (by simpa [Ne.symm different] using rightMember))
      · by_cases headRight : head = right
        · subst head
          right
          simpa [SemigroupBasis.RetainedStateFour.Precedes] using
            (SemigroupBasis.BlockTrace.precedes_cons_self
              (by simpa [different] using leftMember))
        · have leftTail : left ∈ tail := by
            have membershipCases : left = head ∨ left ∈ tail := by
              simpa using leftMember
            rcases membershipCases with leftHead | leftTail
            · exact False.elim (headLeft leftHead.symm)
            · exact leftTail
          have rightTail : right ∈ tail := by
            have membershipCases : right = head ∨ right ∈ tail := by
              simpa using rightMember
            rcases membershipCases with rightHead | rightTail
            · exact False.elim (headRight rightHead.symm)
            · exact rightTail
          rcases inductionHypothesis leftTail rightTail with
            forward | reverse
          · exact Or.inl <| by
              simpa [SemigroupBasis.RetainedStateFour.Precedes] using
                SemigroupBasis.BlockTrace.precedes_cons head (by
                  simpa [SemigroupBasis.RetainedStateFour.Precedes] using forward)
          · exact Or.inr <| by
              simpa [SemigroupBasis.RetainedStateFour.Precedes] using
                SemigroupBasis.BlockTrace.precedes_cons head (by
                  simpa [SemigroupBasis.RetainedStateFour.Precedes] using reverse)

private def pairFilter (left right : Nat) (letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (letter = left ∨ letter = right)

private def PairLabelsFree
    (left right : Nat) (blocks : List SemigroupBasis.RetainedStateFour.Block) : Prop :=
  ∀ block, block ∈ blocks →
    block.label ≠ left ∧ block.label ≠ right

private theorem pairFilter_renderBlocks_eq_nil
    {left right : Nat} {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (free : PairLabelsFree left right blocks) :
    pairFilter left right (SemigroupBasis.RetainedStateFour.renderBlocks blocks) = [] := by
  induction blocks with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      have headFree := free head (List.Mem.head tail)
      have tailFree : PairLabelsFree left right tail := by
        intro block member
        exact free block (List.Mem.tail head member)
      have headFilter : pairFilter left right head.render = [] := by
        simp [pairFilter, SemigroupBasis.RetainedStateFour.Block.render,
          SemigroupBasis.RetainedStateFour.State.render,
          headFree.1, headFree.2]
      have tailFilter := inductionHypothesis tailFree
      unfold SemigroupBasis.RetainedStateFour.renderBlocks
      simp only [List.flatMap_cons]
      unfold pairFilter at headFilter tailFilter ⊢
      rw [List.filter_append, headFilter]
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using tailFilter

private theorem pairFilter_renderBlocks_of_precedes
    {left right : SemigroupBasis.RetainedStateFour.Block} {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (labelsNodup : SemigroupBasis.RetainedStateFour.LabelsNodup blocks)
    (different : left ≠ right)
    (leftState : left.state = .one)
    (rightState : right.state = .one)
    (order : SemigroupBasis.RetainedStateFour.Precedes left right blocks) :
    pairFilter left.label right.label (SemigroupBasis.RetainedStateFour.renderBlocks blocks) =
      [left.label, right.label] := by
  obtain ⟨before, after, blocksShape, rightInAfter⟩ := order
  obtain ⟨middle, suffix, afterShape⟩ :=
    List.mem_iff_append.mp rightInAfter
  rw [afterShape] at blocksShape
  subst blocks
  have blocksNodup :
      (before ++ left :: (middle ++ right :: suffix)).Nodup :=
    blocks_nodup labelsNodup
  have firstSplit := List.nodup_append.mp blocksNodup
  have restNodup : (left :: (middle ++ right :: suffix)).Nodup :=
    firstSplit.2.1
  have beforeDisjoint := firstSplit.2.2
  have leftNotRest : left ∉ middle ++ right :: suffix :=
    (List.nodup_cons.mp restNodup).1
  have tailNodup : (middle ++ right :: suffix).Nodup :=
    (List.nodup_cons.mp restNodup).2
  have middleSplit := List.nodup_append.mp tailNodup
  have rightPartNodup : (right :: suffix).Nodup :=
    middleSplit.2.1
  have middleDisjoint := middleSplit.2.2
  have rightNotSuffix : right ∉ suffix :=
    (List.nodup_cons.mp rightPartNodup).1
  have leftMember :
      left ∈ before ++ left :: (middle ++ right :: suffix) := by
    simp
  have rightMember :
      right ∈ before ++ left :: (middle ++ right :: suffix) := by
    simp
  have beforeFree : PairLabelsFree left.label right.label before := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) :=
      List.mem_append_left _ member
    constructor
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEq
      subst block
      exact beforeDisjoint left member left (List.Mem.head _) rfl
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEq
      subst block
      exact beforeDisjoint right member right (by simp) rfl
  have middleFree : PairLabelsFree left.label right.label middle := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) := by
      simp only [List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (Or.inl member))
    constructor
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEq
      subst block
      exact leftNotRest (List.mem_append_left _ member)
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEq
      subst block
      exact middleDisjoint right member right (List.Mem.head _) rfl
  have suffixFree : PairLabelsFree left.label right.label suffix := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) := by
      simp only [List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr member)))
    constructor
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEq
      subst block
      exact leftNotRest <| List.mem_append_right middle
        (List.Mem.tail right member)
    · intro labelEq
      have blockEq := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEq
      subst block
      exact rightNotSuffix member
  have beforeFilter := pairFilter_renderBlocks_eq_nil beforeFree
  have middleFilter := pairFilter_renderBlocks_eq_nil middleFree
  have suffixFilter := pairFilter_renderBlocks_eq_nil suffixFree
  cases left with
  | mk leftLabel leftBlockState =>
      cases right with
      | mk rightLabel rightBlockState =>
          simp only [SemigroupBasis.RetainedStateFour.Block.state] at leftState rightState
          subst leftBlockState
          subst rightBlockState
          simp only [SemigroupBasis.RetainedStateFour.renderBlocks, List.flatMap_append,
            List.flatMap_cons, SemigroupBasis.RetainedStateFour.Block.render, SemigroupBasis.RetainedStateFour.State.render,
            SemigroupBasis.RetainedStateFour.State.exponent, List.replicate_one]
          simp only [pairFilter] at beforeFilter middleFilter suffixFilter ⊢
          have decideOr (letter : Nat) :
              decide (letter = leftLabel ∨ letter = rightLabel) =
                (decide (letter = leftLabel) ||
                  decide (letter = rightLabel)) := by
            by_cases leftEq : letter = leftLabel <;>
              by_cases rightEq : letter = rightLabel <;>
                simp [leftEq, rightEq]
          have beforeFilter' :
              List.filter
                  (fun letter =>
                    decide (letter = leftLabel) ||
                      decide (letter = rightLabel))
                  (before.flatMap
                    SemigroupBasis.RetainedStateFour.Block.render) = [] := by
            simpa only [SemigroupBasis.RetainedStateFour.renderBlocks,
              ← decideOr] using beforeFilter
          have middleFilter' :
              List.filter
                  (fun letter =>
                    decide (letter = leftLabel) ||
                      decide (letter = rightLabel))
                  (middle.flatMap
                    SemigroupBasis.RetainedStateFour.Block.render) = [] := by
            simpa only [SemigroupBasis.RetainedStateFour.renderBlocks,
              ← decideOr] using middleFilter
          have suffixFilter' :
              List.filter
                  (fun letter =>
                    decide (letter = leftLabel) ||
                      decide (letter = rightLabel))
                  (suffix.flatMap
                    SemigroupBasis.RetainedStateFour.Block.render) = [] := by
            simpa only [SemigroupBasis.RetainedStateFour.renderBlocks,
              ← decideOr] using suffixFilter
          simp [beforeFilter', middleFilter', suffixFilter']

private def listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (letters : List Nat) : S :=
  letters.foldl (fun current letter => G.mul current (valuation letter)) one

private theorem foldl_pairFilter
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (rightIdentity : ∀ value, G.mul value one = value)
    (left right : Nat)
    (outside : ∀ letter, letter ≠ left → letter ≠ right →
      valuation letter = one) :
    ∀ (letters : List Nat) (initial : S),
      letters.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        (pairFilter left right letters).foldl
          (fun current letter => G.mul current (valuation letter)) initial
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases letterLeft : letter = left
      · subst letter
        have inductionHypothesis :=
          foldl_pairFilter G one valuation rightIdentity left right outside
            rest (G.mul initial (valuation left))
        simpa [pairFilter] using inductionHypothesis
      · by_cases letterRight : letter = right
        · subst letter
          have inductionHypothesis :=
            foldl_pairFilter G one valuation rightIdentity left right outside
              rest (G.mul initial (valuation right))
          simpa [pairFilter, letterLeft] using inductionHypothesis
        · rw [show pairFilter left right (letter :: rest) =
              pairFilter left right rest by
            simp [pairFilter, letterLeft, letterRight]]
          simp only [List.foldl_cons]
          rw [outside letter letterLeft letterRight, rightIdentity]
          exact foldl_pairFilter G one valuation rightIdentity left right
            outside rest initial

private theorem listEval_pairFilter
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (rightIdentity : ∀ value, G.mul value one = value)
    (left right : Nat)
    (outside : ∀ letter, letter ≠ left → letter ≠ right →
      valuation letter = one)
    (letters : List Nat) :
    listEval G one valuation letters =
      listEval G one valuation (pairFilter left right letters) :=
  foldl_pairFilter G one valuation rightIdentity left right outside letters one

private theorem eval_eq_listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word = listEval G one valuation word.toList := by
  cases word with
  | mk head tail =>
      simp [Semigroup.eval, Word.toList, listEval, leftIdentity]

private theorem eval_eq_normalized
    (G : Semigroup S) (models : Models G sourceBasis)
    (one : S) (valuation : Nat → S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word =
      listEval G one valuation
        (SemigroupBasis.RetainedStateFour.renderBlocks
          (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree word.toList)) := by
  cases word with
  | mk head tail =>
      have normalized :=
        SemigroupBasis.RetainedStateFour.derivesNormalize_of_laws
          gatherOneDerivable fiveReductionDerivable (head :: tail)
      obtain ⟨rightHead, rightTail, targetShape, derivation⟩ :=
        normalized.from_cons
      calc
        G.eval valuation (Word.mk head tail) =
            G.eval valuation (listWordOfCons head tail) := rfl
        _ = G.eval valuation (listWordOfCons rightHead rightTail) :=
          derivation.sound models valuation
        _ = listEval G one valuation
            (listWordOfCons rightHead rightTail).toList :=
          eval_eq_listEval G one valuation leftIdentity _
        _ = listEval G one valuation
            (SemigroupBasis.RetainedStateFour.renderBlocks
              (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree
                (Word.mk head tail).toList)) := by
          change
            listEval G one valuation (rightHead :: rightTail) =
              listEval G one valuation
                (SemigroupBasis.RetainedStateFour.renderBlocks
                  (SemigroupBasis.RetainedStateFour.normalizeBlocks
                    .periodTwoFromThree (head :: tail)))
          rw [targetShape]

private theorem eval_of_normalized_precedes
    (G : Semigroup S) (models : Models G sourceBasis)
    (one leftValue rightValue : S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (rightIdentity : ∀ value, G.mul value one = value)
    (valuation : Nat → S) (word : Word Nat)
    {left right : SemigroupBasis.RetainedStateFour.Block}
    (different : left ≠ right)
    (leftState : left.state = .one)
    (rightState : right.state = .one)
    (order : SemigroupBasis.RetainedStateFour.Precedes left right
      (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree word.toList))
    (leftValueAt : valuation left.label = leftValue)
    (rightValueAt : valuation right.label = rightValue)
    (outside : ∀ letter, letter ≠ left.label → letter ≠ right.label →
      valuation letter = one) :
    G.eval valuation word = G.mul leftValue rightValue := by
  rw [eval_eq_normalized G models one valuation leftIdentity word]
  rw [listEval_pairFilter G one valuation rightIdentity
    left.label right.label outside]
  rw [pairFilter_renderBlocks_of_precedes
    (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup .periodTwoFromThree word.toList)
    different leftState rightState order]
  simp [listEval, leftValueAt, rightValueAt, leftIdentity]

private theorem dependentOrder_of_separator
    (G : Semigroup S) (models : Models G sourceBasis)
    (one firstValue secondValue : S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (rightIdentity : ∀ value, G.mul value one = value)
    (separated :
      G.mul firstValue secondValue ≠ G.mul secondValue firstValue)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (sameState :
      SemigroupBasis.RetainedStateFour.SameStateMap
        (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree identity.lhs.toList)
        (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree identity.rhs.toList)) :
    SemigroupBasis.RetainedStateFour.SameDependentOrder stateCommutes
      (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree identity.lhs.toList)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks .periodTwoFromThree identity.rhs.toList) := by
  intro left right leftMember rightMember blocked
  have sourceLabels :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup .periodTwoFromThree identity.lhs.toList
  have targetLabels :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup .periodTwoFromThree identity.rhs.toList
  have targetLeft := (sameState left).mp leftMember
  have targetRight := (sameState right).mp rightMember
  by_cases blocksEqual : left = right
  · subst right
    constructor
    · intro impossible
      exact False.elim <|
        not_precedes_self (blocks_nodup sourceLabels) impossible
    · intro impossible
      exact False.elim <|
        not_precedes_self (blocks_nodup targetLabels) impossible
  · have labelsDifferent : left.label ≠ right.label := by
      intro labelsEqual
      exact blocksEqual <|
        eq_of_mem_of_mem_of_map_nodup sourceLabels
          leftMember rightMember labelsEqual
    have blocked' :
        ¬(left.state.exponent ≠ 1 ∨ right.state.exponent ≠ 1) := by
      simpa [SemigroupBasis.RetainedStateFour.BlocksIndependent, stateCommutes] using blocked
    have leftExponent : left.state.exponent = 1 := by
      classical
      exact Classical.byContradiction fun different =>
        blocked' (Or.inl different)
    have rightExponent : right.state.exponent = 1 := by
      classical
      exact Classical.byContradiction fun different =>
        blocked' (Or.inr different)
    have leftState : left.state = .one := by
      cases stateShape : left.state <;>
        simp [SemigroupBasis.RetainedStateFour.State.exponent, stateShape] at leftExponent ⊢
    have rightState : right.state = .one := by
      cases stateShape : right.state <;>
        simp [SemigroupBasis.RetainedStateFour.State.exponent, stateShape] at rightExponent ⊢
    let valuation : Nat → S := fun letter =>
      if letter = left.label then firstValue
      else if letter = right.label then secondValue
      else one
    have valueAtLeft : valuation left.label = firstValue := by
      simp [valuation]
    have valueAtRight : valuation right.label = secondValue := by
      simp [valuation, Ne.symm labelsDifferent]
    have outside :
        ∀ letter, letter ≠ left.label → letter ≠ right.label →
          valuation letter = one := by
      intro letter letterLeft letterRight
      simp [valuation, letterLeft, letterRight]
    constructor
    · intro sourceOrder
      classical
      apply Classical.byContradiction
      intro targetNotForward
      have targetReverse :=
        (precedes_or_reverse blocksEqual targetLeft targetRight).resolve_left
          targetNotForward
      have sourceEvaluation :=
        eval_of_normalized_precedes G models
          one firstValue secondValue leftIdentity rightIdentity
          valuation identity.lhs blocksEqual leftState rightState sourceOrder
          valueAtLeft valueAtRight outside
      have targetEvaluation :=
        eval_of_normalized_precedes G models
          one secondValue firstValue leftIdentity rightIdentity
          valuation identity.rhs (Ne.symm blocksEqual) rightState leftState
          targetReverse valueAtRight valueAtLeft (by
            intro letter letterRight letterLeft
            exact outside letter letterLeft letterRight)
      apply separated
      calc
        G.mul firstValue secondValue = G.eval valuation identity.lhs :=
          sourceEvaluation.symm
        _ = G.eval valuation identity.rhs := valid valuation
        _ = G.mul secondValue firstValue := targetEvaluation
    · intro targetOrder
      classical
      apply Classical.byContradiction
      intro sourceNotForward
      have sourceReverse :=
        (precedes_or_reverse blocksEqual leftMember rightMember).resolve_left
          sourceNotForward
      have targetEvaluation :=
        eval_of_normalized_precedes G models
          one firstValue secondValue leftIdentity rightIdentity
          valuation identity.rhs blocksEqual leftState rightState targetOrder
          valueAtLeft valueAtRight outside
      have sourceEvaluation :=
        eval_of_normalized_precedes G models
          one secondValue firstValue leftIdentity rightIdentity
          valuation identity.lhs (Ne.symm blocksEqual) rightState leftState
          sourceReverse valueAtRight valueAtLeft (by
            intro letter letterRight letterLeft
            exact outside letter letterLeft letterRight)
      apply separated
      calc
        G.mul firstValue secondValue = G.eval valuation identity.rhs :=
          targetEvaluation.symm
        _ = G.eval valuation identity.lhs := (valid valuation).symm
        _ = G.mul secondValue firstValue := sourceEvaluation

/-! ## Exact order-six tables -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis : List (Identity (Fin 2)) :=
  sourceBasis.map fun identity => identity.map toFinTwo

private theorem sourceBasis_roundTrip_checked :
    sourceBasis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup sourceBasis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp sourceBasis_roundTrip_checked) identity member
  rw [restored] at finiteValid
  exact finiteValid

private theorem basisFor_of_exponent_trace
    (candidate : Semigroup S)
    (models : Models candidate sourceBasis)
    (one firstValue secondValue : S)
    (leftIdentity : ∀ value, candidate.mul one value = value)
    (rightIdentity : ∀ value, candidate.mul value one = value)
    (separated :
      candidate.mul firstValue secondValue ≠
        candidate.mul secondValue firstValue)
    (validExponents : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        ∀ letter,
          SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
              (identity.lhs.toList.count letter) =
            SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
              (identity.rhs.toList.count letter)) :
    BasisFor candidate sourceBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have sameState :=
    sameStateMap_of_exponents (validExponents identity valid)
  have dependentOrder :=
    dependentOrder_of_separator candidate models
      one firstValue secondValue leftIdentity rightIdentity
      separated identity valid sameState
  have listed :=
    SemigroupBasis.RetainedStateFour.derivesOfTrace_of_laws
      gatherOneDerivable fiveReductionDerivable traceOrderComplete
      sameState dependentOrder adjacentSwapDerivable
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              exact listed.toWord

namespace S6_2860

/-- Exact one-based catalogue table:
`[[1,1,1,4,1,1],[1,1,1,4,1,2],[1,1,1,4,1,3],
  [4,4,4,1,4,4],[1,1,2,4,2,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 3 0 0 b else
    if a = 1 then row6 0 0 0 3 0 1 b else
      if a = 2 then row6 0 0 0 3 0 2 b else
        if a = 3 then row6 3 3 3 0 3 3 b else
          if a = 4 then row6 0 0 1 3 1 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c79561c587a27984f2c9d0ae7d2788c6c505482a29938d18526b2d9f865c13ad"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_223.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (3 : Fin 6) else
          if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (5 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (5 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (2 : Fin 6) (4 : Fin 6) ≠
      table.semigroup.mul (4 : Fin 6) (2 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_223Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (5 : Fin 6) (2 : Fin 6) (4 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_2860

namespace S6_2896

/-- Exact one-based catalogue table:
`[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],
  [3,3,1,1,1,4],[3,3,1,2,2,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 2 2 0 b else
    if a = 1 then row6 0 0 2 2 2 1 b else
      if a = 2 then row6 2 2 0 0 0 2 b else
        if a = 3 then row6 2 2 0 0 0 3 b else
          if a = 4 then row6 2 2 0 1 1 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "23cc0555cc0926d88b6c4f569cd873226e040071d1cf757587d7115611ba9760"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_226.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (2 : Fin 6) else
          if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (5 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (5 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (3 : Fin 6) (4 : Fin 6) ≠
      table.semigroup.mul (4 : Fin 6) (3 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_226Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_2896

namespace S6_5303

/-- Exact one-based catalogue table:
`[[1,1,3,1,1,1],[1,1,3,1,1,2],[3,3,1,3,3,3],
  [1,1,3,2,1,4],[1,1,3,2,2,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 0 0 0 b else
    if a = 1 then row6 0 0 2 0 0 1 b else
      if a = 2 then row6 2 2 0 2 2 2 b else
        if a = 3 then row6 0 0 2 1 0 3 b else
          if a = 4 then row6 0 0 2 1 1 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3013d74cb2d87b4cd51bba913778f7636173687e9c794cd3d1c35baa0ed6b6ee"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_223.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (2 : Fin 6) else
          if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (5 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (5 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (3 : Fin 6) (4 : Fin 6) ≠
      table.semigroup.mul (4 : Fin 6) (3 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_223Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_5303

namespace S6_5317

/-- Exact one-based catalogue table:
`[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],
  [3,3,1,2,1,4],[3,3,1,2,2,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 2 2 0 b else
    if a = 1 then row6 0 0 2 2 2 1 b else
      if a = 2 then row6 2 2 0 0 0 2 b else
        if a = 3 then row6 2 2 0 1 0 3 b else
          if a = 4 then row6 2 2 0 1 1 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "171c18ff647f81f3865243c4f9d23ce1b3ba183cc96bc676e08186dfa39250cc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_226.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (2 : Fin 6) else
          if a = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (5 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (5 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (3 : Fin 6) (4 : Fin 6) ≠
      table.semigroup.mul (4 : Fin 6) (3 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_226Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_5317

namespace S6_5461

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,1,1,3,3],
  [1,1,2,2,4,4],[1,2,3,4,5,6],[1,2,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 0 0 0 2 2 b else
        if a = 3 then row6 0 0 1 1 3 3 b else
          if a = 4 then row6 0 1 2 3 4 5 b else
            row6 0 1 2 3 5 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c83ab82d138a600a257d612b81b57b4fe19252053398273517f2805a95a4bd0e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_514.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (3 : Fin 6) else
          if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (4 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (4 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (2 : Fin 6) (3 : Fin 6) ≠
      table.semigroup.mul (3 : Fin 6) (2 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_514Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (4 : Fin 6) (2 : Fin 6) (3 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_5461

namespace S6_9379

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,2,1,3,3],
  [1,1,2,2,4,4],[1,2,3,4,5,6],[1,2,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 0 1 0 2 2 b else
        if a = 3 then row6 0 0 1 1 3 3 b else
          if a = 4 then row6 0 1 2 3 4 5 b else
            row6 0 1 2 3 5 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d62657c360ebaba8362aa51703078ac0b6b8b2765fd8ed0fa21a3961b25ca22a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup sourceBasis :=
  models_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_514.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else
      if a = 1 then (1 : Fin 6) else
        if a = 2 then (2 : Fin 6) else
          if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

private theorem leftIdentity (value : Fin 6) :
    table.semigroup.mul (4 : Fin 6) value = value := by
  exact by decide +revert

private theorem rightIdentity (value : Fin 6) :
    table.semigroup.mul value (4 : Fin 6) = value := by
  exact by decide +revert

private theorem markerProductsDifferent :
    table.semigroup.mul (2 : Fin 6) (3 : Fin 6) ≠
      table.semigroup.mul (3 : Fin 6) (2 : Fin 6) := by
  decide

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_514Separates identity
      (exponentEmbedding.pullback_identity identity valid)

theorem representative_basis :
    BasisFor table.semigroup sourceBasis :=
  basisFor_of_exponent_trace table.semigroup models
    (4 : Fin 6) (2 : Fin 6) (3 : Fin 6)
    leftIdentity rightIdentity markerProductsDifferent validExponents

end S6_9379

end SemigroupBasis.CoRoots.Order6Class105TraceRoots

import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.CoRoots.Order6Class105TraceRoots
import SemigroupBasis.Examples.CommutativePeriodThreeFromTwoOrderFive
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.RetainedStateFourNormalizer
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

/-! ## The two exact eight-law presentations -/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
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

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def class471GatherLaw : Identity Nat := ⟨xyx, yxx⟩
def swap22Law : Identity Nat := ⟨xxyy, yyxx⟩
def swap23Law : Identity Nat := ⟨xxyyy, yyyxx⟩
def swap24Law : Identity Nat := ⟨xxyyyy, yyyyxx⟩
def swap33Law : Identity Nat := ⟨xxxyyy, yyyxxx⟩
def swap34Law : Identity Nat := ⟨xxxyyyy, yyyyxxx⟩
def swap44Law : Identity Nat := ⟨xxxxyyyy, yyyyxxxx⟩

/-- The class-495/direct source presentation. -/
def directBasis : List (Identity Nat) :=
  [powerLaw, swap44Law, swap33Law, swap34Law,
    swap22Law, swap23Law, swap24Law, gatherLaw]

/-- The displayed class-471 source presentation. It is the reversal of
`directBasis`, with equality sides oriented exactly as in the accepted packet. -/
def class471Basis : List (Identity Nat) :=
  [powerLaw, swap44Law, swap33Law, swap34Law,
    swap22Law, swap23Law, swap24Law, class471GatherLaw]

private def reversedSwap22Law : Identity Nat := ⟨yyxx, xxyy⟩
private def reversedSwap23Law : Identity Nat := ⟨yyyxx, xxyyy⟩
private def reversedSwap24Law : Identity Nat := ⟨yyyyxx, xxyyyy⟩
private def reversedSwap33Law : Identity Nat := ⟨yyyxxx, xxxyyy⟩
private def reversedSwap34Law : Identity Nat := ⟨yyyyxxx, xxxyyyy⟩
private def reversedSwap44Law : Identity Nat := ⟨yyyyxxxx, xxxxyyyy⟩
private def reversedGatherLaw : Identity Nat := ⟨yxx, xyx⟩

private def reversedDirectCanonical : List (Identity Nat) :=
  [powerLaw, reversedSwap44Law, reversedSwap33Law,
    reversedSwap34Law, reversedSwap22Law, reversedSwap23Law,
    reversedSwap24Law, reversedGatherLaw]

private theorem reversedDirectBasis_eq :
    reversedBasis directBasis = reversedDirectCanonical := by
  decide

/-- Every literally reversed direct law follows from the class-471 packet;
the latter differs only by equality-side orientation. -/
private theorem reversedDirectDerivesClass471
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis directBasis) :
    Derives class471Basis identity.lhs identity.rhs := by
  rw [reversedDirectBasis_eq] at member
  simp only [reversedDirectCanonical, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := powerLaw) (by simp [class471Basis])
  · exact (Derives.fromBasis (e := swap44Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := swap33Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := swap34Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := swap22Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := swap23Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := swap24Law) (by
      simp [class471Basis])).symm
  · exact (Derives.fromBasis (e := class471GatherLaw) (by
      simp [class471Basis])).symm

private def renameTwo (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n + 2 => n + 2

private theorem derivesGatherWords (u v : Word Nat) :
    Derives directBasis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have base : Derives directBasis xyx xxy :=
    (Derives.fromBasis (e := gatherLaw) (by
      simp [directBasis])).symm
  have substituted := Derives.subst base (fun
    | 0 => u
    | 1 => v
    | n + 2 => Word.singleton (n + 2))
  simpa [gatherLaw, xxy, xyx, w, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem gatherOneDerivable :
    SemigroupBasis.RetainedStateFour.GatherOneDerivable directBasis := by
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
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      directBasis .periodThreeFromTwo := by
  intro x
  have base : Derives directBasis xxxxx xx :=
    (Derives.fromBasis (e := powerLaw) (by
      simp [directBasis])).symm
  have renamed := base.rename (renameTwo x x)
  simpa [powerLaw, xx, xxxxx, w, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

private theorem derivesFromDirect (identity : Identity Nat)
    (member : identity ∈ directBasis) :
    Derives directBasis identity.lhs identity.rhs :=
  Derives.fromBasis member

private theorem swap22 (x y : Nat) :
    ListDerives directBasis [x, x, y, y] [y, y, x, x] := by
  have renamed :=
    (derivesFromDirect swap22Law (by decide)).rename (renameTwo x y)
  simpa [swap22Law, xxyy, yyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap23 (x y : Nat) :
    ListDerives directBasis [x, x, y, y, y] [y, y, y, x, x] := by
  have renamed :=
    (derivesFromDirect swap23Law (by decide)).rename (renameTwo x y)
  simpa [swap23Law, xxyyy, yyyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap24 (x y : Nat) :
    ListDerives directBasis [x, x, y, y, y, y]
      [y, y, y, y, x, x] := by
  have renamed :=
    (derivesFromDirect swap24Law (by decide)).rename (renameTwo x y)
  simpa [swap24Law, xxyyyy, yyyyxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap33 (x y : Nat) :
    ListDerives directBasis [x, x, x, y, y, y]
      [y, y, y, x, x, x] := by
  have renamed :=
    (derivesFromDirect swap33Law (by decide)).rename (renameTwo x y)
  simpa [swap33Law, xxxyyy, yyyxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap34 (x y : Nat) :
    ListDerives directBasis [x, x, x, y, y, y, y]
      [y, y, y, y, x, x, x] := by
  have renamed :=
    (derivesFromDirect swap34Law (by decide)).rename (renameTwo x y)
  simpa [swap34Law, xxxyyyy, yyyyxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

private theorem swap44 (x y : Nat) :
    ListDerives directBasis [x, x, x, x, y, y, y, y]
      [y, y, y, y, x, x, x, x] := by
  have renamed :=
    (derivesFromDirect swap44Law (by decide)).rename (renameTwo x y)
  simpa [swap44Law, xxxxyyyy, yyyyxxxx, w, renameTwo, Word.map] using
    ListDerives.ofWord renamed

/-- Exactly the pairs with no singleton block commute. -/
def repeatedCommutes (left right : Nat) : Prop :=
  left ≠ 1 ∧ right ≠ 1

theorem adjacentSwapDerivable :
    SemigroupBasis.RetainedStateFour.AdjacentSwapDerivable
      directBasis repeatedCommutes := by
  rintro ⟨leftLabel, leftState⟩ ⟨rightLabel, rightState⟩ allowed
  cases leftState <;> cases rightState
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap22 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap23 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap24 leftLabel rightLabel
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        (swap23 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap33 leftLabel rightLabel
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap34 leftLabel rightLabel
  · simp [SemigroupBasis.RetainedStateFour.BlocksIndependent,
      repeatedCommutes,
      SemigroupBasis.RetainedStateFour.State.exponent] at allowed
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        (swap24 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        (swap34 rightLabel leftLabel).symm
  · simpa [SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent] using
        swap44 leftLabel rightLabel

/-! ## Generic retained-state combinatorics -/

private theorem blocks_nodup
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (labelsNodup : SemigroupBasis.RetainedStateFour.LabelsNodup blocks) :
    blocks.Nodup := by
  induction blocks with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have mapped :
          (head.label :: tail.map
            SemigroupBasis.RetainedStateFour.Block.label).Nodup := by
        simpa [SemigroupBasis.RetainedStateFour.LabelsNodup] using
          labelsNodup
      have parts := List.nodup_cons.mp mapped
      apply List.nodup_cons.mpr
      constructor
      · intro member
        exact parts.1 (List.mem_map.mpr ⟨head, member, rfl⟩)
      · exact inductionHypothesis parts.2

private theorem translateSwapClosure
    {independent : SemigroupBasis.RetainedStateFour.Block →
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

theorem traceOrderComplete :
    SemigroupBasis.RetainedStateFour.TraceOrderComplete repeatedCommutes := by
  intro source target sourceLabels targetLabels sameState dependentOrder
  have sourceNodup : source.Nodup := blocks_nodup sourceLabels
  have targetNodup : target.Nodup := blocks_nodup targetLabels
  have permutation : source.Perm target :=
    SemigroupBasis.BlockTrace.perm_of_nodup_mem_iff
      sourceNodup targetNodup sameState
  have generic :
      SemigroupBasis.BlockTrace.SwapClosure
        (SemigroupBasis.RetainedStateFour.BlocksIndependent
          repeatedCommutes) source target :=
    SemigroupBasis.BlockTrace.SwapClosure.of_perm_of_dependent_order
      sourceNodup targetNodup permutation (by
        intro left right leftMember rightMember blocked
        simpa [SemigroupBasis.BlockTrace.Precedes,
          SemigroupBasis.RetainedStateFour.Precedes] using
            dependentOrder left right leftMember rightMember blocked)
  exact translateSwapClosure generic

theorem sameStateMap_of_exponents
    {left right : List Nat}
    (exponents : ∀ z,
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (left.count z) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (right.count z)) :
    SemigroupBasis.RetainedStateFour.SameStateMap
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo left)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo right) := by
  intro block
  rw [Order6Class105TraceRoots.mem_normalizeBlocks_iff,
    Order6Class105TraceRoots.mem_normalizeBlocks_iff]
  have stateEq :
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.state
          (left.count block.label) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.state
          (right.count block.label) := by
    unfold SemigroupBasis.RetainedStateFour.Profile.state
    congr 1
    exact exponents block.label
  constructor
  · rintro ⟨leftMember, blockState⟩
    have leftPositive : 0 < left.count block.label :=
      List.count_pos_iff.mpr leftMember
    have rightPositive : 0 < right.count block.label := by
      have rightExponentPositive :
          0 < SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
            (right.count block.label) := by
        rw [← exponents block.label]
        exact SemigroupBasis.RetainedStateFour.Profile.exponent_pos
          leftPositive
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
          0 < SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
            (left.count block.label) := by
        rw [exponents block.label]
        exact SemigroupBasis.RetainedStateFour.Profile.exponent_pos
          rightPositive
      cases leftCount : left.count block.label with
      | zero => simp [leftCount] at leftExponentPositive
      | succ n => omega
    exact ⟨List.count_pos_iff.mp leftPositive,
      blockState.trans stateEq.symm⟩

/-! ## Singleton/repeated semantic order separators -/

private theorem eq_of_mem_of_mem_of_map_nodup
    {entries : List α} {project : α → β} {first second : α}
    (mappedNodup : (entries.map project).Nodup)
    (firstMember : first ∈ entries)
    (secondMember : second ∈ entries)
    (projectedEqual : project first = project second) :
    first = second := by
  induction entries with
  | nil => simp at firstMember
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

private theorem not_precedes_self
    {block : SemigroupBasis.RetainedStateFour.Block}
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (nodup : blocks.Nodup) :
    ¬ SemigroupBasis.RetainedStateFour.Precedes block block blocks := by
  rintro ⟨before, after, shape, member⟩
  rw [shape] at nodup
  have suffixNodup : (block :: after).Nodup :=
    (List.nodup_append.mp nodup).2.1
  exact (List.nodup_cons.mp suffixNodup).1 member

private theorem precedes_or_reverse
    {left right : SemigroupBasis.RetainedStateFour.Block}
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (different : left ≠ right)
    (leftMember : left ∈ blocks) (rightMember : right ∈ blocks) :
    SemigroupBasis.RetainedStateFour.Precedes left right blocks ∨
      SemigroupBasis.RetainedStateFour.Precedes right left blocks := by
  induction blocks with
  | nil => simp at leftMember
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
                  simpa [SemigroupBasis.RetainedStateFour.Precedes] using
                    forward)
          · exact Or.inr <| by
              simpa [SemigroupBasis.RetainedStateFour.Precedes] using
                SemigroupBasis.BlockTrace.precedes_cons head (by
                  simpa [SemigroupBasis.RetainedStateFour.Precedes] using
                    reverse)

private def pairFilter
    (left right : Nat) (letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (letter = left ∨ letter = right)

private def PairLabelsFree
    (left right : Nat)
    (blocks : List SemigroupBasis.RetainedStateFour.Block) : Prop :=
  ∀ block, block ∈ blocks →
    block.label ≠ left ∧ block.label ≠ right

private theorem pairFilter_renderBlocks_eq_nil
    {left right : Nat}
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (free : PairLabelsFree left right blocks) :
    pairFilter left right
      (SemigroupBasis.RetainedStateFour.renderBlocks blocks) = [] := by
  induction blocks with
  | nil => rfl
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
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using
        tailFilter

private theorem pairFilter_renderBlocks_of_precedes
    {left right : SemigroupBasis.RetainedStateFour.Block}
    {blocks : List SemigroupBasis.RetainedStateFour.Block}
    (labelsNodup : SemigroupBasis.RetainedStateFour.LabelsNodup blocks)
    (different : left ≠ right)
    (order : SemigroupBasis.RetainedStateFour.Precedes
      left right blocks) :
    pairFilter left.label right.label
        (SemigroupBasis.RetainedStateFour.renderBlocks blocks) =
      left.render ++ right.render := by
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
  have labelsDifferent : left.label ≠ right.label := by
    intro labelsEqual
    exact different <| eq_of_mem_of_mem_of_map_nodup
      labelsNodup leftMember rightMember labelsEqual
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
          simp only [SemigroupBasis.RetainedStateFour.renderBlocks,
            List.flatMap_append, List.flatMap_cons,
            SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render]
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
          cases leftBlockState <;> cases rightBlockState <;>
            simp [SemigroupBasis.RetainedStateFour.State.exponent,
              beforeFilter', middleFilter', suffixFilter',
              labelsDifferent, Ne.symm labelsDifferent]

private def listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (letters : List Nat) : S :=
  letters.foldl
    (fun current letter => G.mul current (valuation letter)) one

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
          foldl_pairFilter G one valuation rightIdentity left right
            outside rest (G.mul initial (valuation left))
        simpa [pairFilter] using inductionHypothesis
      · by_cases letterRight : letter = right
        · subst letter
          have inductionHypothesis :=
            foldl_pairFilter G one valuation rightIdentity left right
              outside rest (G.mul initial (valuation right))
          simpa [pairFilter, letterLeft] using inductionHypothesis
        · rw [show pairFilter left right (letter :: rest) =
              pairFilter left right rest by
            simp [pairFilter, letterLeft, letterRight]]
          simp only [List.foldl_cons]
          rw [outside letter letterLeft letterRight, rightIdentity]
          exact foldl_pairFilter G one valuation rightIdentity
            left right outside rest initial

private theorem listEval_pairFilter
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (rightIdentity : ∀ value, G.mul value one = value)
    (left right : Nat)
    (outside : ∀ letter, letter ≠ left → letter ≠ right →
      valuation letter = one)
    (letters : List Nat) :
    listEval G one valuation letters =
      listEval G one valuation (pairFilter left right letters) :=
  foldl_pairFilter G one valuation rightIdentity
    left right outside letters one

private theorem eval_eq_listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word = listEval G one valuation word.toList := by
  cases word with
  | mk head tail =>
      simp [Semigroup.eval, Word.toList, listEval, leftIdentity]

private theorem eval_eq_normalized
    (G : Semigroup S) (models : Models G directBasis)
    (one : S) (valuation : Nat → S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word =
      listEval G one valuation
        (SemigroupBasis.RetainedStateFour.renderBlocks
          (SemigroupBasis.RetainedStateFour.normalizeBlocks
            .periodThreeFromTwo word.toList)) := by
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
              (SemigroupBasis.RetainedStateFour.normalizeBlocks
                .periodThreeFromTwo (Word.mk head tail).toList)) := by
          change
            listEval G one valuation (rightHead :: rightTail) =
              listEval G one valuation
                (SemigroupBasis.RetainedStateFour.renderBlocks
                  (SemigroupBasis.RetainedStateFour.normalizeBlocks
                    .periodThreeFromTwo (head :: tail)))
          rw [targetShape]

/-- Candidate-independent semantic data for every dependent pair. The
repeated marker is idempotent, so one finite noncommutation check handles
states two, three, and four. -/
structure SemanticSeparators (G : Semigroup S) where
  one : S
  single : S
  repeated : S
  leftIdentity : ∀ value, G.mul one value = value
  rightIdentity : ∀ value, G.mul value one = value
  repeatedIdempotent : G.mul repeated repeated = repeated
  separated : G.mul single repeated ≠ G.mul repeated single

private theorem eval_of_precedes_singleton_left
    (G : Semigroup S) (models : Models G directBasis)
    (separators : SemanticSeparators G)
    (valuation : Nat → S) (word : Word Nat)
    {left right : SemigroupBasis.RetainedStateFour.Block}
    (different : left ≠ right)
    (leftSingleton : left.state = .one)
    (order : SemigroupBasis.RetainedStateFour.Precedes left right
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo word.toList))
    (leftValueAt : valuation left.label = separators.single)
    (rightValueAt : valuation right.label = separators.repeated)
    (outside : ∀ letter,
      letter ≠ left.label → letter ≠ right.label →
        valuation letter = separators.one) :
    G.eval valuation word =
      G.mul separators.single separators.repeated := by
  rw [eval_eq_normalized G models separators.one valuation
    separators.leftIdentity word]
  rw [listEval_pairFilter G separators.one valuation
    separators.rightIdentity left.label right.label outside]
  rw [pairFilter_renderBlocks_of_precedes
    (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
      .periodThreeFromTwo word.toList) different order]
  rcases left with ⟨leftLabel, leftState⟩
  rcases right with ⟨rightLabel, rightState⟩
  simp only [SemigroupBasis.RetainedStateFour.Block.state] at leftSingleton
  subst leftState
  cases rightState <;>
    simp [listEval, SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent,
      leftValueAt, rightValueAt, separators.leftIdentity,
      G.assoc, separators.repeatedIdempotent]

private theorem eval_of_precedes_singleton_right
    (G : Semigroup S) (models : Models G directBasis)
    (separators : SemanticSeparators G)
    (valuation : Nat → S) (word : Word Nat)
    {left right : SemigroupBasis.RetainedStateFour.Block}
    (different : left ≠ right)
    (rightSingleton : right.state = .one)
    (order : SemigroupBasis.RetainedStateFour.Precedes left right
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo word.toList))
    (leftValueAt : valuation left.label = separators.repeated)
    (rightValueAt : valuation right.label = separators.single)
    (outside : ∀ letter,
      letter ≠ left.label → letter ≠ right.label →
        valuation letter = separators.one) :
    G.eval valuation word =
      G.mul separators.repeated separators.single := by
  rw [eval_eq_normalized G models separators.one valuation
    separators.leftIdentity word]
  rw [listEval_pairFilter G separators.one valuation
    separators.rightIdentity left.label right.label outside]
  rw [pairFilter_renderBlocks_of_precedes
    (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
      .periodThreeFromTwo word.toList) different order]
  rcases left with ⟨leftLabel, leftState⟩
  rcases right with ⟨rightLabel, rightState⟩
  simp only [SemigroupBasis.RetainedStateFour.Block.state] at rightSingleton
  subst rightState
  cases leftState <;>
    simp [listEval, SemigroupBasis.RetainedStateFour.Block.render,
      SemigroupBasis.RetainedStateFour.State.render,
      SemigroupBasis.RetainedStateFour.State.exponent,
      leftValueAt, rightValueAt, separators.leftIdentity,
      G.assoc, separators.repeatedIdempotent]

private theorem state_eq_one_of_exponent_eq_one
    {state : SemigroupBasis.RetainedStateFour.State}
    (exponentEq : state.exponent = 1) :
    state = .one := by
  cases state <;>
    simp [SemigroupBasis.RetainedStateFour.State.exponent] at exponentEq ⊢

private theorem dependentOrder_of_separator
    (G : Semigroup S) (models : Models G directBasis)
    (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (sameState :
      SemigroupBasis.RetainedStateFour.SameStateMap
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          .periodThreeFromTwo identity.lhs.toList)
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          .periodThreeFromTwo identity.rhs.toList)) :
    SemigroupBasis.RetainedStateFour.SameDependentOrder
      repeatedCommutes
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo identity.lhs.toList)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks
        .periodThreeFromTwo identity.rhs.toList) := by
  intro left right leftMember rightMember blocked
  have sourceLabels :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
      .periodThreeFromTwo identity.lhs.toList
  have targetLabels :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
      .periodThreeFromTwo identity.rhs.toList
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
      exact blocksEqual <| eq_of_mem_of_mem_of_map_nodup
        sourceLabels leftMember rightMember labelsEqual
    have notBothRepeated :
        ¬(left.state.exponent ≠ 1 ∧ right.state.exponent ≠ 1) := by
      simpa [SemigroupBasis.RetainedStateFour.BlocksIndependent,
        repeatedCommutes] using blocked
    have singletonExponent :
        left.state.exponent = 1 ∨ right.state.exponent = 1 := by
      by_cases leftOne : left.state.exponent = 1
      · exact Or.inl leftOne
      · by_cases rightOne : right.state.exponent = 1
        · exact Or.inr rightOne
        · exact False.elim (notBothRepeated ⟨leftOne, rightOne⟩)
    have singletonSide :
        left.state = .one ∨ right.state = .one := by
      rcases singletonExponent with leftOne | rightOne
      · exact Or.inl (state_eq_one_of_exponent_eq_one leftOne)
      · exact Or.inr (state_eq_one_of_exponent_eq_one rightOne)
    rcases singletonSide with leftSingleton | rightSingleton
    · let valuation : Nat → S := fun letter =>
        if letter = left.label then separators.single
        else if letter = right.label then separators.repeated
        else separators.one
      have valueAtLeft :
          valuation left.label = separators.single := by
        simp [valuation]
      have valueAtRight :
          valuation right.label = separators.repeated := by
        simp [valuation, Ne.symm labelsDifferent]
      have outside : ∀ letter,
          letter ≠ left.label → letter ≠ right.label →
            valuation letter = separators.one := by
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
          eval_of_precedes_singleton_left G models separators valuation
            identity.lhs blocksEqual leftSingleton sourceOrder
            valueAtLeft valueAtRight outside
        have targetEvaluation :=
          eval_of_precedes_singleton_right G models separators valuation
            identity.rhs (Ne.symm blocksEqual) leftSingleton targetReverse
            valueAtRight valueAtLeft (by
              intro letter letterRight letterLeft
              exact outside letter letterLeft letterRight)
        apply separators.separated
        calc
          G.mul separators.single separators.repeated =
              G.eval valuation identity.lhs := sourceEvaluation.symm
          _ = G.eval valuation identity.rhs := valid valuation
          _ = G.mul separators.repeated separators.single :=
            targetEvaluation
      · intro targetOrder
        classical
        apply Classical.byContradiction
        intro sourceNotForward
        have sourceReverse :=
          (precedes_or_reverse blocksEqual leftMember rightMember).resolve_left
            sourceNotForward
        have targetEvaluation :=
          eval_of_precedes_singleton_left G models separators valuation
            identity.rhs blocksEqual leftSingleton targetOrder
            valueAtLeft valueAtRight outside
        have sourceEvaluation :=
          eval_of_precedes_singleton_right G models separators valuation
            identity.lhs (Ne.symm blocksEqual) leftSingleton sourceReverse
            valueAtRight valueAtLeft (by
              intro letter letterRight letterLeft
              exact outside letter letterLeft letterRight)
        apply separators.separated
        calc
          G.mul separators.single separators.repeated =
              G.eval valuation identity.rhs := targetEvaluation.symm
          _ = G.eval valuation identity.lhs := (valid valuation).symm
          _ = G.mul separators.repeated separators.single :=
            sourceEvaluation
    · let valuation : Nat → S := fun letter =>
        if letter = left.label then separators.repeated
        else if letter = right.label then separators.single
        else separators.one
      have valueAtLeft :
          valuation left.label = separators.repeated := by
        simp [valuation]
      have valueAtRight :
          valuation right.label = separators.single := by
        simp [valuation, Ne.symm labelsDifferent]
      have outside : ∀ letter,
          letter ≠ left.label → letter ≠ right.label →
            valuation letter = separators.one := by
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
          eval_of_precedes_singleton_right G models separators valuation
            identity.lhs blocksEqual rightSingleton sourceOrder
            valueAtLeft valueAtRight outside
        have targetEvaluation :=
          eval_of_precedes_singleton_left G models separators valuation
            identity.rhs (Ne.symm blocksEqual) rightSingleton targetReverse
            valueAtRight valueAtLeft (by
              intro letter letterRight letterLeft
              exact outside letter letterLeft letterRight)
        apply separators.separated
        calc
          G.mul separators.single separators.repeated =
              G.eval valuation identity.rhs := targetEvaluation.symm
          _ = G.eval valuation identity.lhs := (valid valuation).symm
          _ = G.mul separators.repeated separators.single :=
            sourceEvaluation
      · intro targetOrder
        classical
        apply Classical.byContradiction
        intro sourceNotForward
        have sourceReverse :=
          (precedes_or_reverse blocksEqual leftMember rightMember).resolve_left
            sourceNotForward
        have targetEvaluation :=
          eval_of_precedes_singleton_right G models separators valuation
            identity.rhs blocksEqual rightSingleton targetOrder
            valueAtLeft valueAtRight outside
        have sourceEvaluation :=
          eval_of_precedes_singleton_left G models separators valuation
            identity.lhs (Ne.symm blocksEqual) rightSingleton sourceReverse
            valueAtRight valueAtLeft (by
              intro letter letterRight letterLeft
              exact outside letter letterLeft letterRight)
        apply separators.separated
        calc
          G.mul separators.single separators.repeated =
              G.eval valuation identity.lhs := sourceEvaluation.symm
          _ = G.eval valuation identity.rhs := valid valuation
          _ = G.mul separators.repeated separators.single :=
            targetEvaluation

private theorem basisFor_of_exponent_trace
    (candidate : Semigroup S)
    (models : Models candidate directBasis)
    (separators : SemanticSeparators candidate)
    (validExponents : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        ∀ letter,
          SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
              (identity.lhs.toList.count letter) =
            SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
              (identity.rhs.toList.count letter)) :
    BasisFor candidate directBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have sameState :=
    sameStateMap_of_exponents (validExponents identity valid)
  have dependentOrder :=
    dependentOrder_of_separator candidate models separators
      identity valid sameState
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

/-! ## Finite reflection and exponent evaluations -/

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

private def finiteDirectBasis : List (Identity (Fin 2)) :=
  directBasis.map fun identity => identity.map toFinTwo

private def finiteClass471Basis : List (Identity (Fin 2)) :=
  class471Basis.map fun identity => identity.map toFinTwo

private theorem directBasis_roundTrip_checked :
    directBasis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem class471Basis_roundTrip_checked :
    class471Basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem modelsDirect_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteDirectBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup directBasis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteDirectBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp directBasis_roundTrip_checked)
        identity member
  rw [restored] at finiteValid
  exact finiteValid

private theorem modelsClass471_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteClass471Basis.all candidate.checkIdentity = true) :
    Models candidate.semigroup class471Basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteClass471Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp class471Basis_roundTrip_checked)
        identity member
  rw [restored] at finiteValid
  exact finiteValid

private def exponentSeparator
    (target identity : S) (letter : Nat) : Nat → S :=
  fun candidate => if candidate = letter then target else identity

private theorem exponentSeparatorFold
    (G : Semigroup S) (state : Nat → S)
    (target identity : S)
    (mulTarget : ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity : ∀ n, G.mul (state n) identity = state n)
    (letter : Nat) (letters : List Nat) (accumulator : Nat) :
    letters.foldl
        (fun current candidate =>
          G.mul current
            (exponentSeparator target identity letter candidate))
        (state accumulator) =
      state (accumulator + letters.count letter) := by
  induction letters generalizing accumulator with
  | nil => simp
  | cons candidate rest inductionHypothesis =>
      simp only [List.foldl_cons]
      by_cases candidateEq : candidate = letter
      · subst candidate
        rw [List.count_cons_self]
        rw [show exponentSeparator target identity letter letter = target by
          simp [exponentSeparator]]
        rw [mulTarget, inductionHypothesis]
        congr 1
        omega
      · rw [List.count_cons_of_ne candidateEq]
        rw [show exponentSeparator target identity letter candidate = identity by
          simp [exponentSeparator, candidateEq]]
        rw [mulIdentity, inductionHypothesis]

private theorem evalExponentSeparator
    (G : Semigroup S) (state : Nat → S)
    (target identity : S)
    (stateZero : state 0 = identity)
    (stateOne : state 1 = target)
    (mulTarget : ∀ n, G.mul (state n) target = state (n + 1))
    (mulIdentity : ∀ n, G.mul (state n) identity = state n)
    (letter : Nat) (word : Word Nat) :
    G.eval (exponentSeparator target identity letter) word =
      state (word.toList.count letter) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current candidate =>
              G.mul current
                (exponentSeparator target identity letter candidate))
            (exponentSeparator target identity letter head) =
          state ((head :: tail).count letter)
      by_cases headEq : head = letter
      · subst head
        rw [List.count_cons_self]
        rw [show exponentSeparator target identity letter letter = state 1 by
          simp [exponentSeparator, stateOne]]
        rw [exponentSeparatorFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega
      · rw [List.count_cons_of_ne headEq]
        rw [show exponentSeparator target identity letter head = state 0 by
          simp [exponentSeparator, headEq, stateZero]]
        rw [exponentSeparatorFold G state target identity
          mulTarget mulIdentity]
        congr 1
        omega

/-! ## S6_14916 -/

namespace S6_14916

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,2,2,2,2],[1,1,3,3,5,6],
  [1,2,3,4,5,6],[1,1,5,5,6,3],[1,1,6,6,3,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 1 1 1 1 b else
      if a = 2 then row6 0 0 2 2 4 5 b else
        if a = 3 then row6 0 1 2 3 4 5 b else
          if a = 4 then row6 0 0 4 4 5 2 b else
            row6 0 0 5 5 2 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- The accepted packet uses the opposite of the catalogue table. -/
def sourceMul (a b : Fin 6) : Fin 6 := mul b a

def sourceTable : FiniteTable where
  order := 6
  mul := sourceMul
  assoc := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup directBasis :=
  modelsDirect_of_finite_checks table (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sourceModels : Models sourceTable.semigroup class471Basis :=
  modelsClass471_of_finite_checks sourceTable (by decide)

private def thresholdState (n : Nat) : Fin 6 :=
  if n = 0 then 3 else if n = 1 then 1 else 0

private def periodState (n : Nat) : Fin 6 :=
  if n = 0 then 3 else if n % 3 = 0 then 2 else
    if n % 3 = 1 then 4 else 5

private def thresholdSeparator (letter : Nat) : Nat → Fin 6 :=
  exponentSeparator 1 3 letter

private def periodSeparator (letter : Nat) : Nat → Fin 6 :=
  exponentSeparator 4 3 letter

private theorem mulIdentity (value : Fin 6) :
    table.semigroup.mul value (3 : Fin 6) = value := by
  exact by decide +revert

private theorem thresholdMul_target (n : Nat) :
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

private theorem periodMul_target (n : Nat) :
    table.semigroup.mul (periodState n) (4 : Fin 6) =
      periodState (n + 1) := by
  by_cases nZero : n = 0
  · subst n
    rfl
  · by_cases remainderZero : n % 3 = 0
    · have nextRemainder : (n + 1) % 3 = 1 := by omega
      simp [table, FiniteTable.semigroup, mul, row6, periodState,
        nZero, remainderZero, nextRemainder,
        show n + 1 ≠ 0 by omega]
    · by_cases remainderOne : n % 3 = 1
      · have nextRemainder : (n + 1) % 3 = 2 := by omega
        simp [table, FiniteTable.semigroup, mul, row6, periodState,
          nZero, remainderZero, remainderOne, nextRemainder,
          show n + 1 ≠ 0 by omega]
      · have remainderTwo : n % 3 = 2 := by omega
        have nextRemainder : (n + 1) % 3 = 0 := by omega
        simp [table, FiniteTable.semigroup, mul, row6, periodState,
          nZero, remainderZero, remainderOne, remainderTwo,
          nextRemainder, show n + 1 ≠ 0 by omega]

private theorem evalThresholdSeparator (letter : Nat) (word : Word Nat) :
    table.semigroup.eval (thresholdSeparator letter) word =
      thresholdState (word.toList.count letter) := by
  exact evalExponentSeparator table.semigroup thresholdState
    (1 : Fin 6) (3 : Fin 6)
    (by rfl) (by rfl) thresholdMul_target
    (fun n => mulIdentity (thresholdState n)) letter word

private theorem evalPeriodSeparator (letter : Nat) (word : Word Nat) :
    table.semigroup.eval (periodSeparator letter) word =
      periodState (word.toList.count letter) := by
  exact evalExponentSeparator table.semigroup periodState
    (4 : Fin 6) (3 : Fin 6)
    (by rfl) (by rfl) periodMul_target
    (fun n => mulIdentity (periodState n)) letter word

private def exponentCode
    (threshold period : Fin 6) : Nat :=
  if threshold = 3 then 0 else if threshold = 1 then 1 else
    if period = 5 then 2 else if period = 2 then 3 else 4

private theorem exponentCode_states (n : Nat) :
    exponentCode (thresholdState n) (periodState n) =
      SemigroupBasis.Examples.periodThreeFromTwoExponent n := by
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
          SemigroupBasis.Examples.periodThreeFromTwoExponent,
          nZero, nOne, remainderZero, nextRemainder,
          show ¬n < 2 by omega]
      · by_cases remainderOne : n % 3 = 1
        · have nextRemainder : (n + 1) % 3 = 2 := by omega
          simp [exponentCode, thresholdState, periodState,
            SemigroupBasis.Examples.periodThreeFromTwoExponent,
            nZero, nOne, remainderZero, remainderOne,
            nextRemainder,
            show ¬n < 2 by omega]
        · have remainderTwo : n % 3 = 2 := by omega
          have nextRemainder : (n + 1) % 3 = 0 := by omega
          simp [exponentCode, thresholdState, periodState,
            SemigroupBasis.Examples.periodThreeFromTwoExponent,
            nZero, nOne, remainderZero, remainderOne, remainderTwo,
            nextRemainder,
            show ¬n < 2 by omega]

private theorem exponent_eq_of_states
    (m n : Nat)
    (thresholdEq : thresholdState m = thresholdState n)
    (periodEq : periodState m = periodState n) :
    SemigroupBasis.Examples.periodThreeFromTwoExponent m =
      SemigroupBasis.Examples.periodThreeFromTwoExponent n := by
  calc
    SemigroupBasis.Examples.periodThreeFromTwoExponent m =
        exponentCode (thresholdState m) (periodState m) :=
      (exponentCode_states m).symm
    _ = exponentCode (thresholdState n) (periodState n) := by
      rw [thresholdEq, periodEq]
    _ = SemigroupBasis.Examples.periodThreeFromTwoExponent n :=
      exponentCode_states n

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.rhs.toList.count letter) := by
  intro letter
  have thresholdEq := valid (thresholdSeparator letter)
  have periodEq := valid (periodSeparator letter)
  rw [evalThresholdSeparator, evalThresholdSeparator] at thresholdEq
  rw [evalPeriodSeparator, evalPeriodSeparator] at periodEq
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    exponent_eq_of_states _ _ thresholdEq periodEq

private def semanticSeparators : SemanticSeparators table.semigroup where
  one := (3 : Fin 6)
  single := (1 : Fin 6)
  repeated := (2 : Fin 6)
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  repeatedIdempotent := by decide
  separated := by decide

theorem representative_basis :
    BasisFor table.semigroup directBasis :=
  basisFor_of_exponent_trace table.semigroup models
    semanticSeparators validExponents

theorem tableOpposite_eq_source :
    table.semigroup.opposite = sourceTable.semigroup := by
  unfold table sourceTable sourceMul FiniteTable.semigroup
    Semigroup.opposite
  rfl

/-- The exact displayed class-471 packet basis on the packet orientation. -/
theorem source_basis :
    BasisFor sourceTable.semigroup class471Basis := by
  have reversed := representative_basis.oppositeReversed
  rw [tableOpposite_eq_source] at reversed
  exact reversed.replace sourceModels reversedDirectDerivesClass471

end S6_14916

/-! ## S6_14939 -/

namespace S6_14939

/-- Exact one-based catalogue table:
`[[1,1,1,1,5,6],[1,1,2,2,5,6],[1,1,3,3,5,6],
  [1,2,3,4,5,6],[5,5,5,5,6,1],[6,6,6,6,1,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 4 5 b else
    if a = 1 then row6 0 0 1 1 4 5 b else
      if a = 2 then row6 0 0 2 2 4 5 b else
        if a = 3 then row6 0 1 2 3 4 5 b else
          if a = 4 then row6 4 4 4 4 5 0 b else
            row6 5 5 5 5 0 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def sourceMul (a b : Fin 6) : Fin 6 := mul b a

def sourceTable : FiniteTable where
  order := 6
  mul := sourceMul
  assoc := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup directBasis :=
  modelsDirect_of_finite_checks table (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sourceModels : Models sourceTable.semigroup class471Basis :=
  modelsClass471_of_finite_checks sourceTable (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_1004.semigroup
      table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (3 : Fin 6) else
          if value = 3 then (4 : Fin 6) else (5 : Fin 6)
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
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_1004Separates identity
      (exponentEmbedding.pullback_identity identity valid)

private def semanticSeparators : SemanticSeparators table.semigroup where
  one := (3 : Fin 6)
  single := (1 : Fin 6)
  repeated := (2 : Fin 6)
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  repeatedIdempotent := by decide
  separated := by decide

theorem representative_basis :
    BasisFor table.semigroup directBasis :=
  basisFor_of_exponent_trace table.semigroup models
    semanticSeparators validExponents

theorem tableOpposite_eq_source :
    table.semigroup.opposite = sourceTable.semigroup := by
  unfold table sourceTable sourceMul FiniteTable.semigroup
    Semigroup.opposite
  rfl

/-- The exact displayed class-471 packet basis on the packet orientation. -/
theorem source_basis :
    BasisFor sourceTable.semigroup class471Basis := by
  have reversed := representative_basis.oppositeReversed
  rw [tableOpposite_eq_source] at reversed
  exact reversed.replace sourceModels reversedDirectDerivesClass471

end S6_14939

/-! ## S6_15929 -/

namespace S6_15929

/-- Exact one-based catalogue table:
`[[1,1,1,4,5,5],[1,2,2,4,5,6],[1,2,3,4,5,6],
  [4,4,4,5,1,1],[5,5,5,1,4,4],[5,5,6,1,4,4]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 3 4 4 b else
    if a = 1 then row6 0 1 1 3 4 5 b else
      if a = 2 then row6 0 1 2 3 4 5 b else
        if a = 3 then row6 3 3 3 4 0 0 b else
          if a = 4 then row6 4 4 4 0 3 3 b else
            row6 4 4 5 0 3 3 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- This packet's direct normalization runs on the opposite table. -/
def sourceMul (a b : Fin 6) : Fin 6 := mul b a

def sourceTable : FiniteTable where
  order := 6
  mul := sourceMul
  assoc := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sourceModels : Models sourceTable.semigroup directBasis :=
  modelsDirect_of_finite_checks sourceTable (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem representativeModels : Models table.semigroup class471Basis :=
  modelsClass471_of_finite_checks table (by decide)

def exponentEmbedding :
    Embedding SemigroupBasis.Examples.s5_1156.semigroup
      sourceTable.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (2 : Fin 6) else
        if value = 2 then (3 : Fin 6) else
          if value = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem validExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy sourceTable.semigroup) :
    ∀ letter,
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.lhs.toList.count letter) =
        SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.exponent
          (identity.rhs.toList.count letter) := by
  simpa [SemigroupBasis.RetainedStateFour.Profile.exponent] using
    SemigroupBasis.Examples.s5_1156Separates identity
      (exponentEmbedding.pullback_identity identity valid)

private def semanticSeparators :
    SemanticSeparators sourceTable.semigroup where
  one := (2 : Fin 6)
  single := (5 : Fin 6)
  repeated := (1 : Fin 6)
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  repeatedIdempotent := by decide
  separated := by decide

/-- The exact displayed class-495 packet basis on the packet orientation. -/
theorem source_basis :
    BasisFor sourceTable.semigroup directBasis :=
  basisFor_of_exponent_trace sourceTable.semigroup sourceModels
    semanticSeparators validExponents

theorem sourceOpposite_eq_table :
    sourceTable.semigroup.opposite = table.semigroup := by
  unfold sourceTable table sourceMul FiniteTable.semigroup
    Semigroup.opposite
  rfl

theorem representative_basis :
    BasisFor table.semigroup class471Basis := by
  have reversed := source_basis.oppositeReversed
  rw [sourceOpposite_eq_table] at reversed
  exact reversed.replace representativeModels
    reversedDirectDerivesClass471

end S6_15929

end SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots

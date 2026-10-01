import SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints
import SemigroupBasis.EdmundsPeriodTwoTraceAdapter

namespace SemigroupBasis.CoRoots.Order6Class54TraceRoots

open SemigroupBasis
open SemigroupBasis.BlockTrace
open SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints
open SemigroupBasis.EdmundsPeriodTwoTraceAdapter
open SemigroupBasis.Examples

universe u

/-! ## Class-54 syntax laws -/

/-- The five oriented laws consumed by the period-two trace adapter are literal
members of the recorded seven-law class-54 basis. -/
def class54Laws : Class54OrientedLaws class54Basis where
  power := by
    change Derives class54Basis lawXX_XXXX.lhs lawXX_XXXX.rhs
    exact Derives.fromBasis (by simp [class54Basis])
  gatherReversed := by
    change Derives class54Basis lawXXY_XYX.lhs lawXXY_XYX.rhs
    exact Derives.fromBasis (by simp [class54Basis])
  squareCommutationReversed := by
    change Derives class54Basis lawXXYY_YYXX.lhs lawXXYY_YYXX.rhs
    exact Derives.fromBasis (by simp [class54Basis])
  singleDouble := by
    change Derives class54Basis lawXYY_YYX.lhs lawXYY_YYX.rhs
    exact Derives.fromBasis (by simp [class54Basis])
  singleTriple := by
    change Derives class54Basis lawXYYY_YYYX.lhs lawXYYY_YYYX.rhs
    exact Derives.fromBasis (by simp [class54Basis])

/-! ## Two-coordinate retained-state separator -/

private theorem retainedExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n <= 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private def retainedState (n : Nat) : Fin 4 :=
  ⟨periodTwoFromTwoExponent n, by
    have := retainedExponent_le_three n
    omega⟩

private def nextRetainedState (state : Fin 4) : Fin 4 :=
  if state = 0 then 1
  else if state = 1 then 2
  else if state = 2 then 3
  else 2

private theorem retainedState_succ (n : Nat) :
    retainedState (n + 1) = nextRetainedState (retainedState n) := by
  have bound := retainedExponent_le_three n
  by_cases hzero : periodTwoFromTwoExponent n = 0
  · apply Fin.ext
    simp [retainedState, nextRetainedState, hzero,
      periodTwoFromTwoExponent_succ]
  · by_cases hone : periodTwoFromTwoExponent n = 1
    · apply Fin.ext
      simp [retainedState, nextRetainedState, hzero, hone,
        periodTwoFromTwoExponent_succ]
    · by_cases htwo : periodTwoFromTwoExponent n = 2
      · apply Fin.ext
        simp [retainedState, nextRetainedState, hzero, hone, htwo,
          periodTwoFromTwoExponent_succ]
      · have hthree : periodTwoFromTwoExponent n = 3 := by omega
        apply Fin.ext
        simp [retainedState, nextRetainedState, hzero, hone, htwo, hthree,
          periodTwoFromTwoExponent_succ]

private def retainedPowerCode
    (G : Semigroup S) (one value : S) (state : Fin 4) : S :=
  if state = 0 then one
  else if state = 1 then value
  else if state = 2 then G.mul value value
  else G.mul (G.mul value value) value

/-- Finite semantic data shared by retained-state and singleton-order
separation. The two power coordinates distinguish all four retained states. -/
private structure SemanticSeparators {S : Type u} (G : Semigroup S) where
  one : S
  witness : Fin 2 -> S
  leftIdentity : forall value, G.mul one value = value
  rightIdentity : forall value, G.mul value one = value
  codeStep : forall index state,
    G.mul (retainedPowerCode G one (witness index) state) (witness index) =
      retainedPowerCode G one (witness index) (nextRetainedState state)
  codePairInjective : Function.Injective (fun state : Fin 4 =>
    (retainedPowerCode G one (witness 0) state,
      retainedPowerCode G one (witness 1) state))
  firstOrder : S
  secondOrder : S
  orderSeparated :
    G.mul firstOrder secondOrder ≠ G.mul secondOrder firstOrder

private def SemanticSeparators.code
    {G : Semigroup S} (separators : SemanticSeparators G)
    (index : Fin 2) (state : Fin 4) : S :=
  retainedPowerCode G separators.one (separators.witness index) state

private def SemanticSeparators.swapOrder
    {G : Semigroup S} (separators : SemanticSeparators G) :
    SemanticSeparators G where
  one := separators.one
  witness := separators.witness
  leftIdentity := separators.leftIdentity
  rightIdentity := separators.rightIdentity
  codeStep := separators.codeStep
  codePairInjective := separators.codePairInjective
  firstOrder := separators.secondOrder
  secondOrder := separators.firstOrder
  orderSeparated := by
    intro equal
    exact separators.orderSeparated equal.symm

private def listEval
    (G : Semigroup S) (one : S) (valuation : Nat -> S)
    (letters : List Nat) : S :=
  letters.foldl (fun current letter => G.mul current (valuation letter)) one

private theorem eval_eq_listEval
    (G : Semigroup S) (one : S) (valuation : Nat -> S)
    (leftIdentity : forall value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word = listEval G one valuation word.toList := by
  cases word with
  | mk head tail =>
      simp [Semigroup.eval, Word.toList, listEval, leftIdentity]

private def stateValuation
    {G : Semigroup S} (separators : SemanticSeparators G)
    (index : Fin 2) (selected : Nat) : Nat -> S :=
  fun letter =>
    if letter = selected then separators.witness index else separators.one

private theorem stateFold
    {G : Semigroup S} (separators : SemanticSeparators G)
    (index : Fin 2) (selected : Nat) :
    forall (letters : List Nat) (acc : Nat),
      letters.foldl
          (fun current letter =>
            G.mul current (stateValuation separators index selected letter))
          (separators.code index (retainedState acc)) =
        separators.code index
          (retainedState (acc + letters.count selected))
  | [], _ => by simp
  | letter :: rest, acc => by
      simp only [List.foldl_cons]
      by_cases selectedLetter : letter = selected
      · subst letter
        rw [show stateValuation separators index selected selected =
            separators.witness index by
          simp [stateValuation]]
        have step :
            G.mul (separators.code index (retainedState acc))
                (separators.witness index) =
              separators.code index
                (nextRetainedState (retainedState acc)) := by
          simpa [SemanticSeparators.code] using
            separators.codeStep index (retainedState acc)
        rw [step, ← retainedState_succ, stateFold]
        rw [List.count_cons_self]
        have countArithmetic :
            acc + (rest.count selected + 1) =
              acc + 1 + rest.count selected := by
          omega
        rw [countArithmetic]
      · rw [show stateValuation separators index selected letter =
            separators.one by
          simp [stateValuation, selectedLetter]]
        rw [separators.rightIdentity, stateFold,
          List.count_cons_of_ne selectedLetter]

private theorem eval_stateValuation
    {G : Semigroup S} (separators : SemanticSeparators G)
    (index : Fin 2) (selected : Nat) (word : Word Nat) :
    G.eval (stateValuation separators index selected) word =
      separators.code index
        (retainedState (word.toList.count selected)) := by
  rw [eval_eq_listEval G separators.one _ separators.leftIdentity]
  unfold listEval
  have initial :
      separators.code index (retainedState 0) = separators.one := by
    simp [SemanticSeparators.code, retainedState, retainedPowerCode,
      periodTwoFromTwoExponent]
  rw [← initial]
  simpa using
    stateFold separators index selected word.toList 0

private theorem valid_retainedExponent_eq
    {G : Semigroup S} (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) (label : Nat) :
    periodTwoFromTwoExponent (identity.lhs.toList.count label) =
      periodTwoFromTwoExponent (identity.rhs.toList.count label) := by
  have coordinateEqual : forall index : Fin 2,
      separators.code index
          (retainedState (identity.lhs.toList.count label)) =
        separators.code index
          (retainedState (identity.rhs.toList.count label)) := by
    intro index
    have evaluated := valid (stateValuation separators index label)
    rw [eval_stateValuation, eval_stateValuation] at evaluated
    exact evaluated
  have stateEqual :
      retainedState (identity.lhs.toList.count label) =
        retainedState (identity.rhs.toList.count label) := by
    apply separators.codePairInjective
    apply Prod.ext
    · exact coordinateEqual 0
    · exact coordinateEqual 1
  exact congrArg Fin.val stateEqual

/-! ## Membership in retained traces -/

private theorem retainedBlock_eq_of_label_eq_exponent_eq
    {left right : RetainedBlock}
    (labelEqual : left.label = right.label)
    (exponentEqual : left.exponent = right.exponent) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [EdmundsPeriodTwoBlock.label, EdmundsPeriodTwoBlock.exponent]

private theorem count_render_self (block : RetainedBlock) :
    block.render.count block.label = block.exponent := by
  cases block <;>
    simp [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label,
      EdmundsPeriodTwoBlock.exponent]

private theorem count_render_of_label_ne
    {left : RetainedBlock} {label : Nat} (different : left.label ≠ label) :
    left.render.count label = 0 := by
  cases left <;>
    simp_all [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label]

private theorem count_renderRetainedBlocks_eq_zero
    {blocks : List RetainedBlock} {label : Nat}
    (absent : label ∉ blocks.map EdmundsPeriodTwoBlock.label) :
    (renderRetainedBlocks blocks).count label = 0 := by
  induction blocks with
  | nil => simp [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks]
  | cons head tail inductionHypothesis =>
      have labelNeHead : label ≠ head.label := by
        intro equal
        apply absent
        simp [equal]
      have absentTail :
          label ∉ tail.map EdmundsPeriodTwoBlock.label := by
        intro member
        exact absent (by simp [member])
      have tailCountZero := inductionHypothesis absentTail
      simp only [renderRetainedBlocks,
        renderEdmundsPeriodTwoBlocks] at tailCountZero
      simp only [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
        List.flatMap_cons, List.count_append]
      rw [count_render_of_label_ne (Ne.symm labelNeHead),
        tailCountZero]

private theorem mem_retainedBlocks_iff_count
    {blocks : List RetainedBlock}
    (labelsNodup : RetainedLabelsNodup blocks)
    (block : RetainedBlock) :
    block ∈ blocks ↔
      (renderRetainedBlocks blocks).count block.label = block.exponent := by
  induction blocks with
  | nil =>
      cases block <;>
        simp [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
          EdmundsPeriodTwoBlock.label, EdmundsPeriodTwoBlock.exponent]
  | cons head tail inductionHypothesis =>
      simp only [RetainedLabelsNodup, List.map_cons,
        List.nodup_cons] at labelsNodup
      rcases labelsNodup with ⟨headLabelNotTail, tailLabelsNodup⟩
      simp only [List.mem_cons]
      change
        (block = head ∨ block ∈ tail) ↔
          (head.render ++ renderRetainedBlocks tail).count block.label =
            block.exponent
      rw [List.count_append]
      by_cases sameLabel : head.label = block.label
      · have tailCountZero :
            (renderRetainedBlocks tail).count block.label = 0 := by
          apply count_renderRetainedBlocks_eq_zero
          intro member
          apply headLabelNotTail
          rw [sameLabel]
          exact member
        have headCount : head.render.count block.label = head.exponent := by
          rw [← sameLabel]
          exact count_render_self head
        rw [headCount, tailCountZero, Nat.add_zero]
        constructor
        · rintro (equal | tailMember)
          · subst block
            rfl
          · exact False.elim <| headLabelNotTail <|
              List.mem_map.mpr ⟨block, tailMember, sameLabel.symm⟩
        · intro exponentEqual
          exact Or.inl <|
            (retainedBlock_eq_of_label_eq_exponent_eq
              sameLabel exponentEqual).symm
      · have headCountZero : head.render.count block.label = 0 :=
          count_render_of_label_ne sameLabel
        have headNeBlock : head ≠ block := by
          intro equal
          exact sameLabel (congrArg EdmundsPeriodTwoBlock.label equal)
        have blockNeHead : block ≠ head := Ne.symm headNeBlock
        rw [headCountZero, Nat.zero_add]
        simpa [blockNeHead] using
          inductionHypothesis tailLabelsNodup

private theorem normalBlocks_mem_iff
    (word : Word Nat) (block : RetainedBlock) :
    block ∈ normalBlocks word ↔
      periodTwoFromTwoExponent (word.toList.count block.label) =
        block.exponent := by
  rw [mem_retainedBlocks_iff_count (normalBlocks_labelsNodup word)]
  rw [render_normalBlocks, normalWord_toList,
    edmundsPeriodTwoBlocksNormalList_count]

private theorem sameRetainedStateMap_of_valid
    {G : Semigroup S} (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    SameRetainedStateMap
      (normalBlocks identity.lhs) (normalBlocks identity.rhs) := by
  intro block
  rw [normalBlocks_mem_iff, normalBlocks_mem_iff]
  rw [valid_retainedExponent_eq separators identity valid block.label]

/-! ## Noncommuting singleton-order separator -/

private theorem eq_of_mem_of_mem_of_map_nodup
    {entries : List α} {project : α → β}
    {first second : α}
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
        · exact inductionHypothesis tailMappedNodup firstTail secondTail

private theorem not_precedes_self
    {block : RetainedBlock} {blocks : List RetainedBlock}
    (nodup : blocks.Nodup) :
    ¬ Precedes block block blocks := by
  rintro ⟨before, after, shape, member⟩
  rw [shape] at nodup
  have suffixNodup : (block :: after).Nodup :=
    (List.nodup_append.mp nodup).2.1
  exact (List.nodup_cons.mp suffixNodup).1 member

private theorem precedes_or_reverse
    {left right : RetainedBlock} {blocks : List RetainedBlock}
    (different : left ≠ right)
    (leftMember : left ∈ blocks) (rightMember : right ∈ blocks) :
    Precedes left right blocks ∨ Precedes right left blocks := by
  induction blocks with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      by_cases headLeft : head = left
      · subst head
        exact Or.inl <| precedes_cons_self
          (by simpa [Ne.symm different] using rightMember)
      · by_cases headRight : head = right
        · subst head
          exact Or.inr <| precedes_cons_self
            (by simpa [different] using leftMember)
        · have leftTail : left ∈ tail := by
            have membershipCases : left = head ∨ left ∈ tail := by
              simpa using leftMember
            rcases membershipCases with leftHead | member
            · exact False.elim (headLeft leftHead.symm)
            · exact member
          have rightTail : right ∈ tail := by
            have membershipCases : right = head ∨ right ∈ tail := by
              simpa using rightMember
            rcases membershipCases with rightHead | member
            · exact False.elim (headRight rightHead.symm)
            · exact member
          rcases inductionHypothesis leftTail rightTail with forward | reverse
          · exact Or.inl (precedes_cons head forward)
          · exact Or.inr (precedes_cons head reverse)

private def PairLabelsFree
    (left right : Nat) (blocks : List RetainedBlock) : Prop :=
  forall block, block ∈ blocks ->
    block.label ≠ left ∧ block.label ≠ right

private theorem foldl_renderRetainedBlocks_free
    {G : Semigroup S} (separators : SemanticSeparators G)
    (valuation : Nat -> S) (left right : Nat)
    (outside : forall letter, letter ≠ left -> letter ≠ right ->
      valuation letter = separators.one) :
    forall (blocks : List RetainedBlock) (initial : S),
      PairLabelsFree left right blocks ->
      (renderRetainedBlocks blocks).foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        initial
  | [], _, _ => rfl
  | head :: tail, initial, free => by
      have headFree := free head (List.Mem.head tail)
      have tailFree : PairLabelsFree left right tail := by
        intro block member
        exact free block (List.Mem.tail head member)
      have headValue : valuation head.label = separators.one :=
        outside head.label headFree.1 headFree.2
      simp only [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
        List.flatMap_cons, List.foldl_append]
      have headFold :
          head.render.foldl
              (fun current letter => G.mul current (valuation letter)) initial =
            initial := by
        cases head <;>
          simp_all [EdmundsPeriodTwoBlock.render,
            EdmundsPeriodTwoBlock.label, separators.rightIdentity]
      rw [headFold]
      exact foldl_renderRetainedBlocks_free separators valuation left right
        outside tail initial tailFree

private theorem listEval_renderRetainedBlocks_of_precedes
    {G : Semigroup S} (separators : SemanticSeparators G)
    (valuation : Nat -> S)
    {left right : RetainedBlock} {blocks : List RetainedBlock}
    (labelsNodup : RetainedLabelsNodup blocks)
    (different : left ≠ right)
    (leftExponent : left.exponent = 1)
    (rightExponent : right.exponent = 1)
    (order : Precedes left right blocks)
    (leftValueAt : valuation left.label = separators.firstOrder)
    (rightValueAt : valuation right.label = separators.secondOrder)
    (outside : forall letter,
      letter ≠ left.label -> letter ≠ right.label ->
        valuation letter = separators.one) :
    listEval G separators.one valuation (renderRetainedBlocks blocks) =
      G.mul separators.firstOrder separators.secondOrder := by
  obtain ⟨before, after, blocksShape, rightInAfter⟩ := order
  obtain ⟨middle, suffix, afterShape⟩ :=
    List.mem_iff_append.mp rightInAfter
  rw [afterShape] at blocksShape
  subst blocks
  have blocksNodup :
      (before ++ left :: (middle ++ right :: suffix)).Nodup :=
    retainedBlocks_nodup labelsNodup
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
      left ∈ before ++ left :: (middle ++ right :: suffix) := by simp
  have rightMember :
      right ∈ before ++ left :: (middle ++ right :: suffix) := by simp
  have beforeFree : PairLabelsFree left.label right.label before := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) :=
      List.mem_append_left _ member
    constructor
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEqual
      subst block
      exact beforeDisjoint left member left (List.Mem.head _) rfl
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEqual
      subst block
      exact beforeDisjoint right member right (by simp) rfl
  have middleFree : PairLabelsFree left.label right.label middle := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) := by
      simp only [List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (Or.inl member))
    constructor
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEqual
      subst block
      exact leftNotRest (List.mem_append_left _ member)
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEqual
      subst block
      exact middleDisjoint right member right (List.Mem.head _) rfl
  have suffixFree : PairLabelsFree left.label right.label suffix := by
    intro block member
    have blockMember :
        block ∈ before ++ left :: (middle ++ right :: suffix) := by
      simp only [List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr member)))
    constructor
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember leftMember labelEqual
      subst block
      exact leftNotRest <| List.mem_append_right middle
        (List.Mem.tail right member)
    · intro labelEqual
      have blockEqual := eq_of_mem_of_mem_of_map_nodup
        labelsNodup blockMember rightMember labelEqual
      subst block
      exact rightNotSuffix member
  have leftRender : left.render = [left.label] := by
    cases left <;>
      simp_all [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label,
        EdmundsPeriodTwoBlock.exponent]
  have rightRender : right.render = [right.label] := by
    cases right <;>
      simp_all [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label,
        EdmundsPeriodTwoBlock.exponent]
  have renderedShape :
      renderRetainedBlocks
          (before ++ left :: (middle ++ right :: suffix)) =
        renderRetainedBlocks before ++
          (left.render ++
            (renderRetainedBlocks middle ++
              (right.render ++ renderRetainedBlocks suffix))) := by
    simp [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
      List.append_assoc]
  rw [renderedShape]
  unfold listEval
  rw [List.foldl_append]
  rw [foldl_renderRetainedBlocks_free separators valuation
    left.label right.label outside before separators.one beforeFree]
  rw [List.foldl_append, leftRender]
  simp only [List.foldl_cons, List.foldl_nil, leftValueAt,
    separators.leftIdentity]
  rw [List.foldl_append]
  rw [foldl_renderRetainedBlocks_free separators valuation
    left.label right.label outside middle separators.firstOrder middleFree]
  rw [List.foldl_append, rightRender]
  simp only [List.foldl_cons, List.foldl_nil, rightValueAt]
  exact foldl_renderRetainedBlocks_free separators valuation
    left.label right.label outside suffix
      (G.mul separators.firstOrder separators.secondOrder) suffixFree

private theorem eval_of_normalized_precedes
    {G : Semigroup S} (models : Models G class54Basis)
    (separators : SemanticSeparators G)
    (valuation : Nat -> S) (word : Word Nat)
    {left right : RetainedBlock}
    (different : left ≠ right)
    (leftExponent : left.exponent = 1)
    (rightExponent : right.exponent = 1)
    (order : Precedes left right (normalBlocks word))
    (leftValueAt : valuation left.label = separators.firstOrder)
    (rightValueAt : valuation right.label = separators.secondOrder)
    (outside : forall letter,
      letter ≠ left.label -> letter ≠ right.label ->
        valuation letter = separators.one) :
    G.eval valuation word =
      G.mul separators.firstOrder separators.secondOrder := by
  calc
    G.eval valuation word = G.eval valuation (normalWord word) :=
      ((parserSpec word).derivesNormalIn class54Laws.toSyntaxLaws).sound
        models valuation
    _ = listEval G separators.one valuation (normalWord word).toList :=
      eval_eq_listEval G separators.one valuation
        separators.leftIdentity (normalWord word)
    _ = listEval G separators.one valuation
        (renderRetainedBlocks (normalBlocks word)) := by
      rw [render_normalBlocks]
    _ = G.mul separators.firstOrder separators.secondOrder :=
      listEval_renderRetainedBlocks_of_precedes separators valuation
        (normalBlocks_labelsNodup word) different leftExponent rightExponent
        order leftValueAt rightValueAt outside

private theorem dependentOrder_of_separator
    {G : Semigroup S} (models : Models G class54Basis)
    (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (sameState : SameRetainedStateMap
      (normalBlocks identity.lhs) (normalBlocks identity.rhs)) :
    SameDependentOrder class54Commutes
      (normalBlocks identity.lhs) (normalBlocks identity.rhs) := by
  intro left right leftMember rightMember blocked
  have targetLeft := (sameState left).mp leftMember
  have targetRight := (sameState right).mp rightMember
  have sourceLabels := normalBlocks_labelsNodup identity.lhs
  have targetLabels := normalBlocks_labelsNodup identity.rhs
  by_cases blocksEqual : left = right
  · subst right
    constructor
    · intro impossible
      exact False.elim <|
        not_precedes_self (retainedBlocks_nodup sourceLabels) impossible
    · intro impossible
      exact False.elim <|
        not_precedes_self (retainedBlocks_nodup targetLabels) impossible
  · have labelsDifferent : left.label ≠ right.label := by
      intro labelsEqual
      exact blocksEqual <| eq_of_mem_of_mem_of_map_nodup
        sourceLabels leftMember rightMember labelsEqual
    have singletonExponents :
        left.exponent = 1 ∧ right.exponent = 1 :=
      Classical.not_not.mp <| by
        simpa [BlocksIndependent, class54Commutes] using blocked
    let valuation : Nat -> S := fun letter =>
      if letter = left.label then separators.firstOrder
      else if letter = right.label then separators.secondOrder
      else separators.one
    have valueAtLeft : valuation left.label = separators.firstOrder := by
      simp [valuation]
    have valueAtRight : valuation right.label = separators.secondOrder := by
      simp [valuation, Ne.symm labelsDifferent]
    have outside : forall letter,
        letter ≠ left.label -> letter ≠ right.label ->
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
        eval_of_normalized_precedes models separators valuation identity.lhs
          blocksEqual singletonExponents.1 singletonExponents.2 sourceOrder
          valueAtLeft valueAtRight outside
      have targetEvaluation :=
        show G.eval valuation identity.rhs =
            G.mul separators.secondOrder separators.firstOrder from by
          simpa [SemanticSeparators.swapOrder] using
            eval_of_normalized_precedes models separators.swapOrder valuation
              identity.rhs (Ne.symm blocksEqual) singletonExponents.2
              singletonExponents.1 targetReverse valueAtRight valueAtLeft (by
                intro letter letterRight letterLeft
                exact outside letter letterLeft letterRight)
      apply separators.orderSeparated
      calc
        G.mul separators.firstOrder separators.secondOrder =
            G.eval valuation identity.lhs := sourceEvaluation.symm
        _ = G.eval valuation identity.rhs := valid valuation
        _ = G.mul separators.secondOrder separators.firstOrder :=
          targetEvaluation
    · intro targetOrder
      classical
      apply Classical.byContradiction
      intro sourceNotForward
      have sourceReverse :=
        (precedes_or_reverse blocksEqual leftMember rightMember).resolve_left
          sourceNotForward
      have targetEvaluation :=
        eval_of_normalized_precedes models separators valuation identity.rhs
          blocksEqual singletonExponents.1 singletonExponents.2 targetOrder
          valueAtLeft valueAtRight outside
      have sourceEvaluation :=
        show G.eval valuation identity.lhs =
            G.mul separators.secondOrder separators.firstOrder from by
          simpa [SemanticSeparators.swapOrder] using
            eval_of_normalized_precedes models separators.swapOrder valuation
              identity.lhs (Ne.symm blocksEqual) singletonExponents.2
              singletonExponents.1 sourceReverse valueAtRight valueAtLeft (by
                intro letter letterRight letterLeft
                exact outside letter letterLeft letterRight)
      apply separators.orderSeparated
      calc
        G.mul separators.firstOrder separators.secondOrder =
            G.eval valuation identity.rhs := targetEvaluation.symm
        _ = G.eval valuation identity.lhs := (valid valuation).symm
        _ = G.mul separators.secondOrder separators.firstOrder :=
          sourceEvaluation

/-! ## Shared certificate and exact roots -/

/-- One family-level certificate constructor. Concrete roots supply only finite
power-coordinate and noncommutation checks. -/
private def class54TraceCertificate
    {S : Type u} (G : Semigroup S) (models : Models G class54Basis)
    (separators : SemanticSeparators G) :
    TraceCertificate G class54Basis where
  commutes := class54Commutes
  normalWord := normalWord
  normalBlocks := normalBlocks
  renderNormal := render_normalBlocks
  labelsNodup := normalBlocks_labelsNodup
  derivesNormal := fun word =>
    (parserSpec word).derivesNormalIn class54Laws.toSyntaxLaws
  sameStateMap := fun identity valid =>
    sameRetainedStateMap_of_valid separators identity valid
  dependentOrder := fun identity valid =>
    dependentOrder_of_separator models separators identity valid
      (sameRetainedStateMap_of_valid separators identity valid)
  adjacentSwap := class54Laws.adjacentSwap

namespace S6_1262

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_1262.semigroup

abbrev basis := Order6BlockTraceRootEndpoints.S6_1262.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  witness := fun index => if index = 0 then 1 else 4
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  codeStep := by
    intro index state
    revert index state
    decide
  codePairInjective := by
    intro left right
    revert left right
    decide
  firstOrder := 2
  secondOrder := 3
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  class54TraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_1262.models semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_1262.basisFor traceCertificate

end S6_1262

namespace S6_1348

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_1348.semigroup

abbrev basis := Order6BlockTraceRootEndpoints.S6_1348.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  witness := fun index => if index = 0 then 1 else 2
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  codeStep := by
    intro index state
    revert index state
    decide
  codePairInjective := by
    intro left right
    revert left right
    decide
  firstOrder := 3
  secondOrder := 4
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  class54TraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_1348.models semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_1348.basisFor traceCertificate

end S6_1348

namespace S6_1354

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_1354.semigroup

abbrev basis := Order6BlockTraceRootEndpoints.S6_1354.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  witness := fun index => if index = 0 then 1 else 2
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  codeStep := by
    intro index state
    revert index state
    decide
  codePairInjective := by
    intro left right
    revert left right
    decide
  firstOrder := 1
  secondOrder := 4
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  class54TraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_1354.models semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_1354.basisFor traceCertificate

end S6_1354

namespace S6_3051

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_3051.semigroup

abbrev basis := Order6BlockTraceRootEndpoints.S6_3051.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 4
  witness := fun index => if index = 0 then 1 else 5
  leftIdentity := by
    intro value
    revert value
    decide
  rightIdentity := by
    intro value
    revert value
    decide
  codeStep := by
    intro index state
    revert index state
    decide
  codePairInjective := by
    intro left right
    revert left right
    decide
  firstOrder := 2
  secondOrder := 3
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  class54TraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_3051.models semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_3051.basisFor traceCertificate

end S6_3051

end SemigroupBasis.CoRoots.Order6Class54TraceRoots

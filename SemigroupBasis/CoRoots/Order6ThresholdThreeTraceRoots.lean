import SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints
import SemigroupBasis.EdmundsThresholdThreeTraceAdapter

namespace SemigroupBasis.CoRoots.Order6ThresholdThreeTraceRoots

open SemigroupBasis
open SemigroupBasis.BlockTrace
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_530
open SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints
open SemigroupBasis.EdmundsThresholdThreeTraceAdapter
open SemigroupBasis.Examples

universe u

/-! ## Recorded syntax orientations -/

/-- Class 236 records `xyx = yxx`, so its threshold-three normalization is
the reversed (last-occurrence) orientation. -/
private def class236TraceLaws : ReversedTraceLaws class236Basis where
  syntaxLaws := {
    power := by
      change Derives class236Basis lawXXX_XXXX.lhs lawXXX_XXXX.rhs
      exact Derives.fromBasis (by simp [class236Basis])
    gather := by
      change Derives class236Basis lawXYX_YXX.rhs lawXYX_YXX.lhs
      exact (Derives.fromBasis (by simp [class236Basis])).symm
  }
  swapLaws := {
    doubleDouble := by
      change Derives class236Basis lawXXYY_YYXX.lhs lawXXYY_YYXX.rhs
      exact Derives.fromBasis (by simp [class236Basis])
    doubleTriple := by
      change Derives class236Basis lawXXYYY_YYYXX.lhs lawXXYYY_YYYXX.rhs
      exact Derives.fromBasis (by simp [class236Basis])
    tripleTriple := by
      change Derives class236Basis
        lawXXXYYY_YYYXXX.lhs lawXXXYYY_YYYXXX.rhs
      exact Derives.fromBasis (by simp [class236Basis])
  }

/-- Class 389 records `xxy = xyx`, exactly the forward first-occurrence
orientation consumed by the threshold-three parser. -/
private def class389TraceLaws : ForwardTraceLaws class389Basis where
  syntaxLaws := {
    power := by
      change Derives class389Basis lawXXX_XXXX.lhs lawXXX_XXXX.rhs
      exact Derives.fromBasis (by simp [class389Basis])
    gather := by
      change Derives class389Basis lawXXY_XYX.lhs lawXXY_XYX.rhs
      exact Derives.fromBasis (by simp [class389Basis])
  }
  swapLaws := {
    doubleDouble := by
      change Derives class389Basis lawXXYY_YYXX.lhs lawXXYY_YYXX.rhs
      exact Derives.fromBasis (by simp [class389Basis])
    doubleTriple := by
      change Derives class389Basis lawXXYYY_YYYXX.lhs lawXXYYY_YYYXX.rhs
      exact Derives.fromBasis (by simp [class389Basis])
    tripleTriple := by
      change Derives class389Basis
        lawXXXYYY_YYYXXX.lhs lawXXXYYY_YYYXXX.rhs
      exact Derives.fromBasis (by simp [class389Basis])
  }

/-! ## Parser-independent retained-state mechanics -/

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

private theorem forwardNormalBlocks_mem_iff
    (word : Word Nat) (block : RetainedBlock) :
    block ∈ normalBlocks word ↔
      s5_530Exponent (word.toList.count block.label) = block.exponent := by
  rw [mem_retainedBlocks_iff_count (normalBlocks_labelsNodup word)]
  rw [render_normalBlocks, normalWord_toList, s5_530NormalList_count]

private theorem reversedNormalBlocks_mem_iff
    (word : Word Nat) (block : RetainedBlock) :
    block ∈ reversedNormalBlocks word ↔
      s5_530Exponent (word.toList.count block.label) = block.exponent := by
  rw [mem_retainedBlocks_iff_count
    (reversedNormalBlocks_labelsNodup word)]
  rw [render_reversedNormalBlocks, reversedNormalWord_toList,
    List.count_reverse, s5_530NormalList_count]
  simp [Word.toList_reverse, List.count_reverse]

/-- The common interface needed by the semantic proof. It deliberately hides
whether the target uses first- or last-occurrence normalization. -/
private structure TraceMechanics (basis : List (Identity Nat)) where
  normalWord : Word Nat → Word Nat
  normalBlocks : Word Nat → List RetainedBlock
  renderNormal : ∀ word,
    renderRetainedBlocks (normalBlocks word) = (normalWord word).toList
  labelsNodup : ∀ word, RetainedLabelsNodup (normalBlocks word)
  derivesNormal : ∀ word, Derives basis word (normalWord word)
  memIff : ∀ word block,
    block ∈ normalBlocks word ↔
      s5_530Exponent (word.toList.count block.label) = block.exponent
  adjacentSwap : AdjacentSwapDerivable basis repeatedCommutes

private def forwardMechanics
    {basis : List (Identity Nat)} (laws : ForwardTraceLaws basis) :
    TraceMechanics basis where
  normalWord := normalWord
  normalBlocks := normalBlocks
  renderNormal := render_normalBlocks
  labelsNodup := normalBlocks_labelsNodup
  derivesNormal := fun word =>
    (parserSpec word).derivesNormalIn laws.syntaxLaws
  memIff := forwardNormalBlocks_mem_iff
  adjacentSwap := laws.swapLaws.adjacentSwap

private def reversedMechanics
    {basis : List (Identity Nat)} (laws : ReversedTraceLaws basis) :
    TraceMechanics basis where
  normalWord := reversedNormalWord
  normalBlocks := reversedNormalBlocks
  renderNormal := render_reversedNormalBlocks
  labelsNodup := reversedNormalBlocks_labelsNodup
  derivesNormal := fun word =>
    (reversedParserSpec word).derivesNormalIn laws.syntaxLaws
  memIff := reversedNormalBlocks_mem_iff
  adjacentSwap := laws.swapLaws.adjacentSwap

/-! ## Finite semantic separators -/

private theorem retainedExponent_le_three (n : Nat) :
    s5_530Exponent n <= 3 := by
  exact Nat.min_le_right _ _

private def retainedState (n : Nat) : Fin 4 :=
  ⟨s5_530Exponent n, Nat.lt_succ_of_le (retainedExponent_le_three n)⟩

private def nextRetainedState (state : Fin 4) : Fin 4 :=
  ⟨min (state.val + 1) 3, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem retainedState_succ (n : Nat) :
    retainedState (n + 1) = nextRetainedState (retainedState n) := by
  apply Fin.ext
  exact s5_530Exponent_succ n

private def retainedPowerCode
    (G : Semigroup S) (one value : S) (state : Fin 4) : S :=
  if state = 0 then one
  else if state = 1 then value
  else if state = 2 then G.mul value value
  else G.mul (G.mul value value) value

/-- A concrete root supplies one power-chain witness for exponent states and
one noncommuting singleton/idempotent pair for dependent block order. -/
private structure SemanticSeparators {S : Type u} (G : Semigroup S) where
  one : S
  powerWitness : S
  leftIdentity : ∀ value, G.mul one value = value
  rightIdentity : ∀ value, G.mul value one = value
  codeStep : ∀ state,
    G.mul (retainedPowerCode G one powerWitness state) powerWitness =
      retainedPowerCode G one powerWitness (nextRetainedState state)
  codeInjective : Function.Injective
    (retainedPowerCode G one powerWitness)
  singletonOrder : S
  repeatedOrder : S
  repeatedIdempotent : G.mul repeatedOrder repeatedOrder = repeatedOrder
  orderSeparated :
    G.mul singletonOrder repeatedOrder ≠
      G.mul repeatedOrder singletonOrder

private def SemanticSeparators.code
    {G : Semigroup S} (separators : SemanticSeparators G)
    (state : Fin 4) : S :=
  retainedPowerCode G separators.one separators.powerWitness state

private def listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (letters : List Nat) : S :=
  letters.foldl (fun current letter => G.mul current (valuation letter)) one

private theorem eval_eq_listEval
    (G : Semigroup S) (one : S) (valuation : Nat → S)
    (leftIdentity : ∀ value, G.mul one value = value)
    (word : Word Nat) :
    G.eval valuation word = listEval G one valuation word.toList := by
  cases word with
  | mk head tail =>
      simp [Semigroup.eval, Word.toList, listEval, leftIdentity]

private def stateValuation
    {G : Semigroup S} (separators : SemanticSeparators G)
    (selected : Nat) : Nat → S :=
  fun letter =>
    if letter = selected then separators.powerWitness else separators.one

private theorem stateFold
    {G : Semigroup S} (separators : SemanticSeparators G)
    (selected : Nat) :
    ∀ (letters : List Nat) (acc : Nat),
      letters.foldl
          (fun current letter =>
            G.mul current (stateValuation separators selected letter))
          (separators.code (retainedState acc)) =
        separators.code (retainedState (acc + letters.count selected))
  | [], _ => by simp
  | letter :: rest, acc => by
      simp only [List.foldl_cons]
      by_cases selectedLetter : letter = selected
      · subst letter
        rw [show stateValuation separators selected selected =
            separators.powerWitness by simp [stateValuation]]
        have step :
            G.mul (separators.code (retainedState acc))
                separators.powerWitness =
              separators.code
                (nextRetainedState (retainedState acc)) := by
          simpa [SemanticSeparators.code] using
            separators.codeStep (retainedState acc)
        rw [step, ← retainedState_succ, stateFold]
        rw [List.count_cons_self]
        have countArithmetic :
            acc + (rest.count selected + 1) =
              acc + 1 + rest.count selected := by
          omega
        rw [countArithmetic]
      · rw [show stateValuation separators selected letter =
            separators.one by simp [stateValuation, selectedLetter]]
        rw [separators.rightIdentity, stateFold,
          List.count_cons_of_ne selectedLetter]

private theorem eval_stateValuation
    {G : Semigroup S} (separators : SemanticSeparators G)
    (selected : Nat) (word : Word Nat) :
    G.eval (stateValuation separators selected) word =
      separators.code (retainedState (word.toList.count selected)) := by
  rw [eval_eq_listEval G separators.one _ separators.leftIdentity]
  unfold listEval
  have initial :
      separators.code (retainedState 0) = separators.one := by
    simp [SemanticSeparators.code, retainedState, retainedPowerCode,
      s5_530Exponent]
  rw [← initial]
  simpa using stateFold separators selected word.toList 0

private theorem valid_retainedExponent_eq
    {G : Semigroup S} (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) (label : Nat) :
    s5_530Exponent (identity.lhs.toList.count label) =
      s5_530Exponent (identity.rhs.toList.count label) := by
  have evaluated := valid (stateValuation separators label)
  rw [eval_stateValuation, eval_stateValuation] at evaluated
  have stateEqual :
      retainedState (identity.lhs.toList.count label) =
        retainedState (identity.rhs.toList.count label) :=
    separators.codeInjective evaluated
  exact congrArg Fin.val stateEqual

private theorem sameRetainedStateMap_of_valid
    {G : Semigroup S} {basis : List (Identity Nat)}
    (mechanics : TraceMechanics basis)
    (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    SameRetainedStateMap
      (mechanics.normalBlocks identity.lhs)
      (mechanics.normalBlocks identity.rhs) := by
  intro block
  rw [mechanics.memIff, mechanics.memIff]
  rw [valid_retainedExponent_eq separators identity valid block.label]

/-! ## Dependent-order separation -/

private theorem eq_of_mem_of_mem_of_map_nodup
    {alpha beta : Type} {entries : List alpha} {project : alpha → beta}
    {first second : alpha}
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
  ∀ block, block ∈ blocks →
    block.label ≠ left ∧ block.label ≠ right

private theorem foldl_renderRetainedBlocks_free
    {G : Semigroup S} (separators : SemanticSeparators G)
    (valuation : Nat → S) (left right : Nat)
    (outside : ∀ letter, letter ≠ left → letter ≠ right →
      valuation letter = separators.one) :
    ∀ (blocks : List RetainedBlock) (initial : S),
      PairLabelsFree left right blocks →
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

private theorem foldl_block_single
    {G : Semigroup S} (valuation : Nat → S)
    (block : RetainedBlock) (value initial : S)
    (single : block.exponent = 1)
    (valueAt : valuation block.label = value) :
    block.render.foldl
        (fun current letter => G.mul current (valuation letter)) initial =
      G.mul initial value := by
  cases block <;>
    simp_all [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label,
      EdmundsPeriodTwoBlock.exponent]

private theorem foldl_block_idempotent
    {G : Semigroup S} (valuation : Nat → S)
    (block : RetainedBlock) (value initial : S)
    (idempotent : G.mul value value = value)
    (valueAt : valuation block.label = value) :
    block.render.foldl
        (fun current letter => G.mul current (valuation letter)) initial =
      G.mul initial value := by
  cases block <;>
    simp_all [EdmundsPeriodTwoBlock.render, EdmundsPeriodTwoBlock.label,
      valueAt, G.assoc, idempotent]

private theorem listEval_renderRetainedBlocks_of_precedes
    {G : Semigroup S} (separators : SemanticSeparators G)
    (valuation : Nat → S)
    {left right : RetainedBlock} {blocks : List RetainedBlock}
    (labelsNodup : RetainedLabelsNodup blocks)
    (different : left ≠ right)
    (order : Precedes left right blocks)
    (leftValue rightValue : S)
    (leftFold : ∀ initial,
      left.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial leftValue)
    (rightFold : ∀ initial,
      right.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial rightValue)
    (outside : ∀ letter,
      letter ≠ left.label → letter ≠ right.label →
        valuation letter = separators.one) :
    listEval G separators.one valuation (renderRetainedBlocks blocks) =
      G.mul leftValue rightValue := by
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
  rw [List.foldl_append, leftFold, separators.leftIdentity]
  rw [List.foldl_append]
  rw [foldl_renderRetainedBlocks_free separators valuation
    left.label right.label outside middle leftValue middleFree]
  rw [List.foldl_append, rightFold]
  exact foldl_renderRetainedBlocks_free separators valuation
    left.label right.label outside suffix (G.mul leftValue rightValue)
      suffixFree

private theorem eval_of_normalized_precedes
    {G : Semigroup S} {basis : List (Identity Nat)}
    (mechanics : TraceMechanics basis) (models : Models G basis)
    (separators : SemanticSeparators G)
    (valuation : Nat → S) (word : Word Nat)
    {left right : RetainedBlock}
    (different : left ≠ right)
    (order : Precedes left right (mechanics.normalBlocks word))
    (leftValue rightValue : S)
    (leftFold : ∀ initial,
      left.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial leftValue)
    (rightFold : ∀ initial,
      right.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial rightValue)
    (outside : ∀ letter,
      letter ≠ left.label → letter ≠ right.label →
        valuation letter = separators.one) :
    G.eval valuation word = G.mul leftValue rightValue := by
  calc
    G.eval valuation word = G.eval valuation (mechanics.normalWord word) :=
      (mechanics.derivesNormal word).sound models valuation
    _ = listEval G separators.one valuation
        (mechanics.normalWord word).toList :=
      eval_eq_listEval G separators.one valuation
        separators.leftIdentity (mechanics.normalWord word)
    _ = listEval G separators.one valuation
        (renderRetainedBlocks (mechanics.normalBlocks word)) := by
      rw [mechanics.renderNormal]
    _ = G.mul leftValue rightValue :=
      listEval_renderRetainedBlocks_of_precedes separators valuation
        (mechanics.labelsNodup word) different order
        leftValue rightValue leftFold rightFold outside

private theorem pairOrder_of_separated_values
    {G : Semigroup S} {basis : List (Identity Nat)}
    (mechanics : TraceMechanics basis) (models : Models G basis)
    (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (sameState : SameRetainedStateMap
      (mechanics.normalBlocks identity.lhs)
      (mechanics.normalBlocks identity.rhs))
    {left right : RetainedBlock}
    (leftMember : left ∈ mechanics.normalBlocks identity.lhs)
    (rightMember : right ∈ mechanics.normalBlocks identity.lhs)
    (different : left ≠ right)
    (valuation : Nat → S) (leftValue rightValue : S)
    (separated : G.mul leftValue rightValue ≠ G.mul rightValue leftValue)
    (leftFold : ∀ initial,
      left.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial leftValue)
    (rightFold : ∀ initial,
      right.render.foldl
          (fun current letter => G.mul current (valuation letter)) initial =
        G.mul initial rightValue)
    (outside : ∀ letter,
      letter ≠ left.label → letter ≠ right.label →
        valuation letter = separators.one) :
    Precedes left right (mechanics.normalBlocks identity.lhs) ↔
      Precedes left right (mechanics.normalBlocks identity.rhs) := by
  have targetLeft := (sameState left).mp leftMember
  have targetRight := (sameState right).mp rightMember
  constructor
  · intro sourceOrder
    classical
    apply Classical.byContradiction
    intro targetNotForward
    have targetReverse :=
      (precedes_or_reverse different targetLeft targetRight).resolve_left
        targetNotForward
    have sourceEvaluation :=
      eval_of_normalized_precedes mechanics models separators valuation
        identity.lhs different sourceOrder leftValue rightValue
        leftFold rightFold outside
    have targetEvaluation :=
      eval_of_normalized_precedes mechanics models separators valuation
        identity.rhs (Ne.symm different) targetReverse rightValue leftValue
        rightFold leftFold (by
          intro letter letterRight letterLeft
          exact outside letter letterLeft letterRight)
    apply separated
    calc
      G.mul leftValue rightValue = G.eval valuation identity.lhs :=
        sourceEvaluation.symm
      _ = G.eval valuation identity.rhs := valid valuation
      _ = G.mul rightValue leftValue := targetEvaluation
  · intro targetOrder
    classical
    apply Classical.byContradiction
    intro sourceNotForward
    have sourceReverse :=
      (precedes_or_reverse different leftMember rightMember).resolve_left
        sourceNotForward
    have targetEvaluation :=
      eval_of_normalized_precedes mechanics models separators valuation
        identity.rhs different targetOrder leftValue rightValue
        leftFold rightFold outside
    have sourceEvaluation :=
      eval_of_normalized_precedes mechanics models separators valuation
        identity.lhs (Ne.symm different) sourceReverse rightValue leftValue
        rightFold leftFold (by
          intro letter letterRight letterLeft
          exact outside letter letterLeft letterRight)
    apply separated
    calc
      G.mul leftValue rightValue = G.eval valuation identity.rhs :=
        targetEvaluation.symm
      _ = G.eval valuation identity.lhs := (valid valuation).symm
      _ = G.mul rightValue leftValue := sourceEvaluation

private theorem dependentOrder_of_separator
    {G : Semigroup S} {basis : List (Identity Nat)}
    (mechanics : TraceMechanics basis) (models : Models G basis)
    (separators : SemanticSeparators G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (sameState : SameRetainedStateMap
      (mechanics.normalBlocks identity.lhs)
      (mechanics.normalBlocks identity.rhs)) :
    SameDependentOrder repeatedCommutes
      (mechanics.normalBlocks identity.lhs)
      (mechanics.normalBlocks identity.rhs) := by
  apply sameDependentOrder_of_stateOne
  intro left right leftMember rightMember dependent
  have targetLeft := (sameState left).mp leftMember
  have targetRight := (sameState right).mp rightMember
  by_cases blocksEqual : left = right
  · subst right
    constructor
    · intro impossible
      exact False.elim <| not_precedes_self
        (retainedBlocks_nodup (mechanics.labelsNodup identity.lhs))
        impossible
    · intro impossible
      exact False.elim <| not_precedes_self
        (retainedBlocks_nodup (mechanics.labelsNodup identity.rhs))
        impossible
  · have labelsDifferent : left.label ≠ right.label := by
      intro labelsEqual
      exact blocksEqual <| eq_of_mem_of_mem_of_map_nodup
        (mechanics.labelsNodup identity.lhs)
        leftMember rightMember labelsEqual
    by_cases leftOne : left.exponent = 1
    · let valuation : Nat → S := fun letter =>
        if letter = left.label then separators.singletonOrder
        else if letter = right.label then separators.repeatedOrder
        else separators.one
      have leftAt : valuation left.label = separators.singletonOrder := by
        simp [valuation]
      have rightAt : valuation right.label = separators.repeatedOrder := by
        simp [valuation, Ne.symm labelsDifferent]
      have outside : ∀ letter,
          letter ≠ left.label → letter ≠ right.label →
            valuation letter = separators.one := by
        intro letter letterLeft letterRight
        simp [valuation, letterLeft, letterRight]
      exact pairOrder_of_separated_values mechanics models separators
        identity valid sameState leftMember rightMember blocksEqual
        valuation separators.singletonOrder separators.repeatedOrder
        separators.orderSeparated
        (fun initial =>
          foldl_block_single valuation left separators.singletonOrder
            initial leftOne leftAt)
        (fun initial =>
          foldl_block_idempotent valuation right separators.repeatedOrder
            initial separators.repeatedIdempotent rightAt)
        outside
    · have rightOne : right.exponent = 1 :=
        dependent.resolve_left leftOne
      let valuation : Nat → S := fun letter =>
        if letter = left.label then separators.repeatedOrder
        else if letter = right.label then separators.singletonOrder
        else separators.one
      have leftAt : valuation left.label = separators.repeatedOrder := by
        simp [valuation]
      have rightAt : valuation right.label = separators.singletonOrder := by
        simp [valuation, Ne.symm labelsDifferent]
      have outside : ∀ letter,
          letter ≠ left.label → letter ≠ right.label →
            valuation letter = separators.one := by
        intro letter letterLeft letterRight
        simp [valuation, letterLeft, letterRight]
      exact pairOrder_of_separated_values mechanics models separators
        identity valid sameState leftMember rightMember blocksEqual
        valuation separators.repeatedOrder separators.singletonOrder
        (Ne.symm separators.orderSeparated)
        (fun initial =>
          foldl_block_idempotent valuation left separators.repeatedOrder
            initial separators.repeatedIdempotent leftAt)
        (fun initial =>
          foldl_block_single valuation right separators.singletonOrder
            initial rightOne rightAt)
        outside

/-! ## Shared certificate constructor -/

private def thresholdThreeTraceCertificate
    {S : Type u} {basis : List (Identity Nat)}
    (G : Semigroup S) (models : Models G basis)
    (mechanics : TraceMechanics basis)
    (separators : SemanticSeparators G) :
    TraceCertificate G basis where
  commutes := repeatedCommutes
  normalWord := mechanics.normalWord
  normalBlocks := mechanics.normalBlocks
  renderNormal := mechanics.renderNormal
  labelsNodup := mechanics.labelsNodup
  derivesNormal := mechanics.derivesNormal
  sameStateMap := fun identity valid =>
    sameRetainedStateMap_of_valid mechanics separators identity valid
  dependentOrder := fun identity valid =>
    dependentOrder_of_separator mechanics models separators identity valid
      (sameRetainedStateMap_of_valid mechanics separators identity valid)
  adjacentSwap := mechanics.adjacentSwap

private def class236Mechanics : TraceMechanics class236Basis :=
  reversedMechanics class236TraceLaws

private def class389Mechanics : TraceMechanics class389Basis :=
  forwardMechanics class389TraceLaws

/-! ## Exact order-six roots -/

namespace S6_5627

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_5627.semigroup
abbrev basis := Order6BlockTraceRootEndpoints.S6_5627.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  powerWitness := 3
  leftIdentity := by intro value; revert value; decide
  rightIdentity := by intro value; revert value; decide
  codeStep := by intro state; revert state; decide
  codeInjective := by intro left right; revert left right; decide
  singletonOrder := 2
  repeatedOrder := 4
  repeatedIdempotent := by decide
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  thresholdThreeTraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_5627.models
    class236Mechanics semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_5627.basisFor traceCertificate

end S6_5627

namespace S6_5671

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_5671.semigroup
abbrev basis := Order6BlockTraceRootEndpoints.S6_5671.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  powerWitness := 3
  leftIdentity := by intro value; revert value; decide
  rightIdentity := by intro value; revert value; decide
  codeStep := by intro state; revert state; decide
  codeInjective := by intro left right; revert left right; decide
  singletonOrder := 2
  repeatedOrder := 4
  repeatedIdempotent := by decide
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  thresholdThreeTraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_5671.models
    class236Mechanics semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_5671.basisFor traceCertificate

end S6_5671

namespace S6_9469

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_9469.semigroup
abbrev basis := Order6BlockTraceRootEndpoints.S6_9469.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  powerWitness := 2
  leftIdentity := by intro value; revert value; decide
  rightIdentity := by intro value; revert value; decide
  codeStep := by intro state; revert state; decide
  codeInjective := by intro left right; revert left right; decide
  singletonOrder := 3
  repeatedOrder := 4
  repeatedIdempotent := by decide
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  thresholdThreeTraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_9469.models
    class236Mechanics semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_9469.basisFor traceCertificate

end S6_9469

namespace S6_9624

abbrev semigroup := Order6BlockTraceRootEndpoints.S6_9624.semigroup
abbrev basis := Order6BlockTraceRootEndpoints.S6_9624.basis

private def semanticSeparators : SemanticSeparators semigroup where
  one := 5
  powerWitness := 2
  leftIdentity := by intro value; revert value; decide
  rightIdentity := by intro value; revert value; decide
  codeStep := by intro state; revert state; decide
  codeInjective := by intro left right; revert left right; decide
  singletonOrder := 4
  repeatedOrder := 0
  repeatedIdempotent := by decide
  orderSeparated := by decide

def traceCertificate : TraceCertificate semigroup basis :=
  thresholdThreeTraceCertificate semigroup
    Order6BlockTraceRootEndpoints.S6_9624.models
    class389Mechanics semanticSeparators

theorem representative_basis : BasisFor semigroup basis :=
  Order6BlockTraceRootEndpoints.S6_9624.basisFor traceCertificate

end S6_9624

end SemigroupBasis.CoRoots.Order6ThresholdThreeTraceRoots

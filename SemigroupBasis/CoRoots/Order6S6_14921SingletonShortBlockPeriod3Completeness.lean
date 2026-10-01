import SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3Prelude
import SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots

namespace SemigroupBasis
namespace CoRoots
namespace Order6S6_14921SingletonShortBlockPeriod3

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

set_option maxRecDepth 100000

/-! ## The exact mixed block normal form -/

/-- A noninitial block keeps its positive multiplicity modulo three. -/
def laterExponent (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + (n - 1) % 3

private def normalBlocks (letters : List Nat) :
    List SemigroupBasis.RetainedStateFour.Block :=
  SemigroupBasis.RetainedStateFour.normalizeBlocks
    .periodThreeFromTwo letters

private def laterBlockRender
    (block : SemigroupBasis.RetainedStateFour.Block) : List Nat :=
  match block.state with
  | .one => [block.label]
  | .two => [block.label, block.label]
  | .three => [block.label, block.label, block.label]
  | .four => [block.label]

private def renderLaterBlocks :
    List SemigroupBasis.RetainedStateFour.Block → List Nat
  | [] => []
  | block :: rest => laterBlockRender block ++ renderLaterBlocks rest

/-- The metadata-recorded normal form: first-occurrence order, the
threshold-two period-three state on the first block, and positive residue
modulo three on every later block. -/
def requiredNormalList (letters : List Nat) : List Nat :=
  match firstOccurrenceSequence letters with
  | [] => []
  | first :: rest =>
      List.replicate
          (periodThreeFromTwoExponent (letters.count first)) first ++
        rest.flatMap fun letter =>
          List.replicate (laterExponent (letters.count letter)) letter

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem derivesGatherBlocks (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have base : Derives basis xyx xxy :=
    Derives.symm <| Derives.fromBasis (e := gatherLaw) (by
      simp [basis])
  change Derives basis ⟨0, [1, 0]⟩ ⟨0, [0, 1]⟩ at base
  have substituted := Derives.subst base (instantiateTwoWords u v)
  simpa [xyx, xxy, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesLaterFourToOne (stem letter : Word Nat) :
    Derives basis
      (stem ++ (((letter ++ letter) ++ letter) ++ letter))
      (stem ++ letter) := by
  have base : Derives basis xyyyy xy :=
    Derives.symm <| Derives.fromBasis (e := tailLaw) (by
      simp [basis])
  change Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1]⟩ at base
  have substituted :=
    Derives.subst base (instantiateTwoWords stem letter)
  simpa [xyyyy, xy, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem gatherOneDerivable :
    SemigroupBasis.RetainedStateFour.GatherOneDerivable basis := by
  intro x middle suffix
  cases middle with
  | nil =>
      exact ListDerives.refl _
  | cons y ys =>
      let middleWord := listWordOfCons y ys
      have core :=
        derivesGatherBlocks (Word.singleton x) middleWord
      have coreList := ListDerives.ofWord core
      simpa [middleWord, listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using coreList.append suffix

private def renameTwo (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | n + 2 => n + 2

private theorem fiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      basis .periodThreeFromTwo := by
  intro x
  have base : Derives basis xxxxx xx :=
    Derives.symm <| Derives.fromBasis (e := powerLaw) (by
      simp [basis])
  change Derives basis ⟨0, [0, 0, 0, 0]⟩ ⟨0, [0]⟩ at base
  have renamed := base.rename (renameTwo x x)
  simpa [powerLaw, xxxxx, xx, renameTwo, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

private def blockWord
    (block : SemigroupBasis.RetainedStateFour.Block) : Word Nat :=
  match block.state with
  | .one => ⟨block.label, []⟩
  | .two => ⟨block.label, [block.label]⟩
  | .three => ⟨block.label, [block.label, block.label]⟩
  | .four => ⟨block.label, [block.label, block.label, block.label]⟩

@[simp]
private theorem blockWord_toList
    (block : SemigroupBasis.RetainedStateFour.Block) :
    (blockWord block).toList =
      SemigroupBasis.RetainedStateFour.Block.render block := by
  cases block with
  | mk label state =>
      cases state <;> rfl

private theorem derivesReduceLaterBlocks (stem : Word Nat) :
    ∀ blocks : List SemigroupBasis.RetainedStateFour.Block,
      ListDerives basis
        (stem.toList ++
          SemigroupBasis.RetainedStateFour.renderBlocks blocks)
        (stem.toList ++ renderLaterBlocks blocks)
  | [] => by
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
        renderLaterBlocks] using
          (ListDerives.refl (basis := basis) stem.toList)
  | block :: rest => by
      cases block with
      | mk label state =>
          cases state with
          | one =>
              simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
                SemigroupBasis.RetainedStateFour.Block.render,
                SemigroupBasis.RetainedStateFour.State.render,
                renderLaterBlocks, laterBlockRender,
                Word.toList_append, List.append_assoc] using
                  derivesReduceLaterBlocks
                    (stem ++ Word.singleton label) rest
          | two =>
              simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
                SemigroupBasis.RetainedStateFour.Block.render,
                SemigroupBasis.RetainedStateFour.State.render,
                renderLaterBlocks, laterBlockRender,
                Word.toList_append, List.append_assoc] using
                  derivesReduceLaterBlocks
                    (stem ++ ⟨label, [label]⟩) rest
          | three =>
              simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
                SemigroupBasis.RetainedStateFour.Block.render,
                SemigroupBasis.RetainedStateFour.State.render,
                renderLaterBlocks, laterBlockRender,
                Word.toList_append, List.append_assoc] using
                  derivesReduceLaterBlocks
                    (stem ++ ⟨label, [label, label]⟩) rest
          | four =>
              have contracted :
                  ListDerives basis
                    (stem.toList ++ [label, label, label, label])
                    (stem.toList ++ [label]) := by
                simpa [Word.toList_append, Word.toList_singleton,
                  List.append_assoc] using
                    ListDerives.ofWord
                      (derivesLaterFourToOne stem (Word.singleton label))
              have contractedWithRest :=
                contracted.append
                  (SemigroupBasis.RetainedStateFour.renderBlocks rest)
              have remaining :=
                derivesReduceLaterBlocks
                  (stem ++ Word.singleton label) rest
              have remaining' :
                  ListDerives basis
                    (stem.toList ++ [label] ++
                      SemigroupBasis.RetainedStateFour.renderBlocks rest)
                    (stem.toList ++ [label] ++ renderLaterBlocks rest) := by
                simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
                  Word.toList_append, Word.toList_singleton,
                  List.append_assoc] using remaining
              have joined := contractedWithRest.trans remaining'
              simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
                SemigroupBasis.RetainedStateFour.Block.render,
                SemigroupBasis.RetainedStateFour.State.render,
                renderLaterBlocks, laterBlockRender,
                List.append_assoc] using joined

private theorem laterBlockRender_profileState
    (label n : Nat) (positive : 0 < n) :
    laterBlockRender
        { label := label
          state :=
            SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo.state n } =
      List.replicate (laterExponent n) label := by
  by_cases one : n = 1
  · subst n
    rfl
  have atLeastTwo : 2 ≤ n := by omega
  have remainderCases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases remainderCases with remainder | remainder | remainder
  · have nextRemainder : (n + 1) % 3 = 1 := by omega
    have priorRemainder : (n - 1) % 3 = 2 := by omega
    simp [laterBlockRender, laterExponent,
      SemigroupBasis.RetainedStateFour.Profile.state,
      SemigroupBasis.RetainedStateFour.Profile.exponent,
      SemigroupBasis.RetainedStateFour.State.ofExponent,
      periodThreeFromTwoExponent, one, remainder,
      nextRemainder, priorRemainder,
      show n ≠ 0 by omega, show ¬ n < 2 by omega]
  · have nextRemainder : (n + 1) % 3 = 2 := by omega
    have priorRemainder : (n - 1) % 3 = 0 := by omega
    simp [laterBlockRender, laterExponent,
      SemigroupBasis.RetainedStateFour.Profile.state,
      SemigroupBasis.RetainedStateFour.Profile.exponent,
      SemigroupBasis.RetainedStateFour.State.ofExponent,
      periodThreeFromTwoExponent, one, remainder,
      nextRemainder, priorRemainder,
      show n ≠ 0 by omega, show ¬ n < 2 by omega]
  · have nextRemainder : (n + 1) % 3 = 0 := by omega
    have priorRemainder : (n - 1) % 3 = 1 := by omega
    simp [laterBlockRender, laterExponent,
      SemigroupBasis.RetainedStateFour.Profile.state,
      SemigroupBasis.RetainedStateFour.Profile.exponent,
      SemigroupBasis.RetainedStateFour.State.ofExponent,
      periodThreeFromTwoExponent, one, remainder,
      nextRemainder, priorRemainder,
      show n ≠ 0 by omega, show ¬ n < 2 by omega]

private theorem blockRender_of_mem_normalBlocks
    (letters : List Nat)
    (block : SemigroupBasis.RetainedStateFour.Block)
    (member : block ∈ normalBlocks letters) :
    SemigroupBasis.RetainedStateFour.Block.render block =
      List.replicate
        (periodThreeFromTwoExponent (letters.count block.label))
        block.label := by
  have data :=
    (SemigroupBasis.CoRoots.Order6Class105TraceRoots.mem_normalizeBlocks_iff
      .periodThreeFromTwo letters block).mp <| by
        simpa [normalBlocks] using member
  have positive : 0 < letters.count block.label :=
    List.count_pos_iff.mpr data.1
  simp only [SemigroupBasis.RetainedStateFour.Block.render,
    SemigroupBasis.RetainedStateFour.State.render]
  rw [data.2,
    SemigroupBasis.RetainedStateFour.Profile.state_exponent positive]
  rfl

private theorem laterBlockRender_of_mem_normalBlocks
    (letters : List Nat)
    (block : SemigroupBasis.RetainedStateFour.Block)
    (member : block ∈ normalBlocks letters) :
    laterBlockRender block =
      List.replicate (laterExponent (letters.count block.label))
        block.label := by
  have data :=
    (SemigroupBasis.CoRoots.Order6Class105TraceRoots.mem_normalizeBlocks_iff
      .periodThreeFromTwo letters block).mp <| by
        simpa [normalBlocks] using member
  have positive : 0 < letters.count block.label :=
    List.count_pos_iff.mpr data.1
  simpa [laterBlockRender, data.2] using
    laterBlockRender_profileState block.label
      (letters.count block.label) positive

private theorem renderLaterBlocks_formula
    (letters : List Nat) :
    ∀ blocks : List SemigroupBasis.RetainedStateFour.Block,
      (∀ block, block ∈ blocks → block ∈ normalBlocks letters) →
      renderLaterBlocks blocks =
        (blocks.map SemigroupBasis.RetainedStateFour.Block.label).flatMap
          (fun label =>
            List.replicate (laterExponent (letters.count label)) label)
  | [], _ => rfl
  | block :: rest, subset => by
      rw [renderLaterBlocks]
      simp only [List.map_cons, List.flatMap_cons]
      rw [laterBlockRender_of_mem_normalBlocks letters block
        (subset block (by simp))]
      have restFormula := renderLaterBlocks_formula letters rest <| by
        intro candidate member
        exact subset candidate (by simp [member])
      rw [restFormula]

private theorem requiredNormalList_from_blocks (letters : List Nat) :
    requiredNormalList letters =
      match normalBlocks letters with
      | [] => []
      | first :: rest =>
          SemigroupBasis.RetainedStateFour.Block.render first ++
            renderLaterBlocks rest := by
  have labels :=
    SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots.normalizeBlocks_labelMap
      SemigroupBasis.RetainedStateFour.Profile.periodThreeFromTwo letters
  have labels' :
      (normalBlocks letters).map
          SemigroupBasis.RetainedStateFour.Block.label =
        firstOccurrenceSequence letters := by
    simpa [normalBlocks] using labels
  cases blocksEq : normalBlocks letters with
  | nil =>
      have orderEmpty : firstOccurrenceSequence letters = [] := by
        rw [blocksEq] at labels'
        simpa using labels'.symm
      simp [requiredNormalList, orderEmpty, blocksEq]
  | cons first rest =>
      have order :
          firstOccurrenceSequence letters =
            first.label ::
              rest.map SemigroupBasis.RetainedStateFour.Block.label := by
        rw [blocksEq] at labels'
        simpa using labels'.symm
      have firstMember : first ∈ normalBlocks letters := by
        rw [blocksEq]
        simp
      have firstRender :=
        blockRender_of_mem_normalBlocks letters first firstMember
      have restRender := renderLaterBlocks_formula letters rest <| by
        intro block member
        rw [blocksEq]
        exact List.Mem.tail first member
      simp [requiredNormalList, order, blocksEq, firstRender, restRender]

private theorem derivesRequiredList (letters : List Nat) :
    ListDerives basis letters (requiredNormalList letters) := by
  have sourceNormal :=
    SemigroupBasis.RetainedStateFour.derivesNormalize_of_laws
      gatherOneDerivable fiveReductionDerivable letters
  change ListDerives basis letters
    (SemigroupBasis.RetainedStateFour.renderBlocks
      (normalBlocks letters)) at sourceNormal
  rw [requiredNormalList_from_blocks]
  cases blocksEq : normalBlocks letters with
  | nil =>
      simpa [blocksEq,
        SemigroupBasis.RetainedStateFour.renderBlocks] using sourceNormal
  | cons first rest =>
      have reduced := derivesReduceLaterBlocks (blockWord first) rest
      have reduced' :
          ListDerives basis
            (SemigroupBasis.RetainedStateFour.renderBlocks (first :: rest))
            (SemigroupBasis.RetainedStateFour.Block.render first ++
              renderLaterBlocks rest) := by
        simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
          List.append_assoc] using reduced
      have sourceNormal' :
          ListDerives basis letters
            (SemigroupBasis.RetainedStateFour.renderBlocks
              (first :: rest)) := by
        simpa [blocksEq] using sourceNormal
      simpa [blocksEq] using sourceNormal'.trans reduced'

private theorem derivesToRequiredNormalForm (word : Word Nat) :
    match requiredNormalList word.toList with
    | [] => False
    | head :: tail => Derives basis word ⟨head, tail⟩ := by
  cases word with
  | mk head tail =>
      change
        match requiredNormalList (head :: tail) with
        | [] => False
        | normalHead :: normalTail =>
            Derives basis ⟨head, tail⟩ ⟨normalHead, normalTail⟩
      have listed := derivesRequiredList (head :: tail)
      cases normalEq : requiredNormalList (head :: tail) with
      | nil =>
          exact listed.target_ne_nil normalEq
      | cons normalHead normalTail =>
          have listed' :
              ListDerives basis (head :: tail)
                (normalHead :: normalTail) := by
            simpa [normalEq] using listed
          simpa [listWordOfCons] using listed'.toWord

/-! ## Exact table invariants -/

/-- The embedded left regular band detects first-occurrence order. -/
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

private def thresholdValuation (selected : Nat) (letter : Nat) : Fin 6 :=
  if letter = selected then 1 else 3

private def thresholdState (n : Nat) : Fin 6 :=
  if n = 0 then 1 else 0

private theorem thresholdState_mul_selected (n : Nat) :
    table.semigroup.mul (thresholdState n) (1 : Fin 6) =
      thresholdState (n + 1) := by
  cases n <;> simp [thresholdState, table] <;> decide

private theorem thresholdState_mul_other (n : Nat) :
    table.semigroup.mul (thresholdState n) (3 : Fin 6) = thresholdState n := by
  cases n <;> simp [thresholdState, table] <;> decide

private theorem thresholdFold (selected : Nat) (letters : List Nat)
    (n : Nat) :
    letters.foldl
        (fun current letter =>
          table.semigroup.mul current (thresholdValuation selected letter))
        (thresholdState n) =
      thresholdState (n + letters.count selected) := by
  induction letters generalizing n with
  | nil => simp
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [List.count_cons_self]
        rw [show thresholdValuation selected selected = (1 : Fin 6) by
          simp [thresholdValuation]]
        rw [thresholdState_mul_selected, inductionHypothesis]
        congr 1
        omega
      · rw [List.count_cons_of_ne equal]
        rw [show thresholdValuation selected letter = (3 : Fin 6) by
          simp [thresholdValuation, equal]]
        rw [thresholdState_mul_other, inductionHypothesis]

private theorem evalThresholdValuation_of_head
    (selected : Nat) (word : Word Nat) (head : word.head = selected) :
    (table.semigroup.eval (thresholdValuation selected) word).val =
      if word.toList.count selected = 1 then 1 else 0 := by
  cases word with
  | mk first rest =>
      simp only [Word.head] at head
      subst first
      change
        (rest.foldl
          (fun current letter =>
            table.semigroup.mul current
              (thresholdValuation selected letter))
          (thresholdValuation selected selected)).val = _
      rw [show thresholdValuation selected selected = thresholdState 0 by
        simp [thresholdValuation, thresholdState]]
      rw [thresholdFold]
      simp only [Word.toList, List.count_cons_self]
      cases rest.count selected <;> simp [thresholdState]

private def cycleValuation (selected : Nat) (letter : Nat) : Fin 6 :=
  if letter = selected then 4 else 3

private def cycleState (n : Nat) : Fin 6 :=
  match n % 3 with
  | 0 => 3
  | 1 => 4
  | _ => 5

private theorem cycleState_mul_selected (n : Nat) :
    table.semigroup.mul (cycleState n) (4 : Fin 6) = cycleState (n + 1) := by
  have cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with remainder | remainder | remainder
  · have next : (n + 1) % 3 = 1 := by omega
    rw [show cycleState n = (3 : Fin 6) by simp [cycleState, remainder]]
    rw [show cycleState (n + 1) = (4 : Fin 6) by
      simp [cycleState, next]]
    decide
  · have next : (n + 1) % 3 = 2 := by omega
    rw [show cycleState n = (4 : Fin 6) by simp [cycleState, remainder]]
    rw [show cycleState (n + 1) = (5 : Fin 6) by
      simp [cycleState, next]]
    decide
  · have next : (n + 1) % 3 = 0 := by omega
    rw [show cycleState n = (5 : Fin 6) by simp [cycleState, remainder]]
    rw [show cycleState (n + 1) = (3 : Fin 6) by
      simp [cycleState, next]]
    decide

private theorem cycleState_mul_other (n : Nat) :
    table.semigroup.mul (cycleState n) (3 : Fin 6) = cycleState n := by
  have cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with remainder | remainder | remainder
  · rw [show cycleState n = (3 : Fin 6) by simp [cycleState, remainder]]
    decide
  · rw [show cycleState n = (4 : Fin 6) by simp [cycleState, remainder]]
    decide
  · rw [show cycleState n = (5 : Fin 6) by simp [cycleState, remainder]]
    decide

private theorem cycleFold (selected : Nat) (letters : List Nat)
    (n : Nat) :
    letters.foldl
        (fun current letter =>
          table.semigroup.mul current (cycleValuation selected letter))
        (cycleState n) =
      cycleState (n + letters.count selected) := by
  induction letters generalizing n with
  | nil => simp
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [List.count_cons_self]
        rw [show cycleValuation selected selected = (4 : Fin 6) by
          simp [cycleValuation]]
        rw [cycleState_mul_selected, inductionHypothesis]
        congr 1
        omega
      · rw [List.count_cons_of_ne equal]
        rw [show cycleValuation selected letter = (3 : Fin 6) by
          simp [cycleValuation, equal]]
        rw [cycleState_mul_other, inductionHypothesis]

private theorem cycleValuation_eq_state (selected letter : Nat) :
    cycleValuation selected letter =
      cycleState (if letter = selected then 1 else 0) := by
  by_cases equal : letter = selected <;>
    simp [equal, cycleValuation, cycleState]

private theorem evalCycleValuation (selected : Nat) (word : Word Nat) :
    (table.semigroup.eval (cycleValuation selected) word).val =
      match word.toList.count selected % 3 with
      | 0 => 3
      | 1 => 4
      | _ => 5 := by
  cases word with
  | mk first rest =>
      change
        (rest.foldl
          (fun current letter =>
            table.semigroup.mul current
              (cycleValuation selected letter))
          (cycleValuation selected first)).val =
            match (first :: rest).count selected % 3 with
            | 0 => 3
            | 1 => 4
            | _ => 5
      rw [cycleValuation_eq_state, cycleFold]
      have countEq :
          (if first = selected then 1 else 0) + rest.count selected =
            (first :: rest).count selected := by
        simp only [List.count_cons]
        by_cases equal : first = selected <;> simp [equal, Nat.add_comm]
      rw [countEq]
      unfold cycleState
      split <;> rfl

theorem validCountModThree
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (selected : Nat) :
    identity.lhs.toList.count selected % 3 =
      identity.rhs.toList.count selected % 3 := by
  have evaluated := congrArg Fin.val (valid (cycleValuation selected))
  rw [evalCycleValuation, evalCycleValuation] at evaluated
  have leftCases : identity.lhs.toList.count selected % 3 = 0 ∨
      identity.lhs.toList.count selected % 3 = 1 ∨
      identity.lhs.toList.count selected % 3 = 2 := by omega
  have rightCases : identity.rhs.toList.count selected % 3 = 0 ∨
      identity.rhs.toList.count selected % 3 = 1 ∨
      identity.rhs.toList.count selected % 3 = 2 := by omega
  rcases leftCases with left | left | left <;>
    rcases rightCases with right | right | right <;>
      simp [left, right] at evaluated ⊢

private theorem firstOccurrenceSequence_head (word : Word Nat) :
    (firstOccurrenceSequence word.toList).head? = some word.head := by
  cases word
  rfl

private theorem validHeadsEq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have order := validFirstOccurrenceSequence identity valid
  have heads := congrArg List.head? order
  rw [firstOccurrenceSequence_head, firstOccurrenceSequence_head] at heads
  simpa only [Option.some.injEq] using heads

private theorem validCountEqOne_of_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (selected : Nat)
    (leftHead : identity.lhs.head = selected)
    (rightHead : identity.rhs.head = selected) :
    (identity.lhs.toList.count selected = 1 ↔
      identity.rhs.toList.count selected = 1) := by
  have evaluated := congrArg Fin.val (valid (thresholdValuation selected))
  rw [evalThresholdValuation_of_head selected identity.lhs leftHead,
    evalThresholdValuation_of_head selected identity.rhs rightHead] at evaluated
  by_cases left : identity.lhs.toList.count selected = 1 <;>
    by_cases right : identity.rhs.toList.count selected = 1 <;>
      simp [left, right] at evaluated ⊢

private theorem firstExponent_eq_of_mod_and_one
    {left right : Nat} (leftPositive : 0 < left)
    (rightPositive : 0 < right) (modEq : left % 3 = right % 3)
    (oneEq : (left = 1 ↔ right = 1)) :
    periodThreeFromTwoExponent left =
      periodThreeFromTwoExponent right := by
  unfold periodThreeFromTwoExponent
  by_cases leftOne : left = 1
  · have rightOne := oneEq.mp leftOne
    simp [leftOne, rightOne]
  · have leftAtLeastTwo : 2 ≤ left := by omega
    have rightOne : right ≠ 1 := by simpa [leftOne] using oneEq
    have rightAtLeastTwo : 2 ≤ right := by omega
    simp only [if_neg (by omega : ¬ left < 2),
      if_neg (by omega : ¬ right < 2)]
    omega

private theorem laterExponent_eq_of_zero_and_mod
    {left right : Nat} (zeroEq : (left = 0 ↔ right = 0))
    (modEq : left % 3 = right % 3) :
    laterExponent left = laterExponent right := by
  unfold laterExponent
  by_cases leftZero : left = 0
  · have rightZero := zeroEq.mp leftZero
    simp [leftZero, rightZero]
  · have rightZero : right ≠ 0 := by simpa [leftZero] using zeroEq
    simp [leftZero, rightZero]
    omega

theorem validFirstExponent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    periodThreeFromTwoExponent
        (identity.lhs.toList.count identity.lhs.head) =
      periodThreeFromTwoExponent
        (identity.rhs.toList.count identity.lhs.head) := by
  have heads := validHeadsEq identity valid
  apply firstExponent_eq_of_mod_and_one
  · exact List.count_pos_iff.mpr (by simp [Word.toList])
  · exact List.count_pos_iff.mpr (by simp [Word.toList, heads])
  · exact validCountModThree identity valid identity.lhs.head
  · exact validCountEqOne_of_head identity valid identity.lhs.head
      rfl heads.symm

private theorem mem_firstOccurrenceSequence_iff (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst selected
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

theorem validLaterExponent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (selected : Nat) :
    laterExponent (identity.lhs.toList.count selected) =
      laterExponent (identity.rhs.toList.count selected) := by
  apply laterExponent_eq_of_zero_and_mod
  · have order := validFirstOccurrenceSequence identity valid
    have support : selected ∈ identity.lhs.toList ↔
        selected ∈ identity.rhs.toList :=
      (mem_firstOccurrenceSequence_iff selected identity.lhs.toList).symm.trans <|
        order.symm ▸ mem_firstOccurrenceSequence_iff selected identity.rhs.toList
    constructor
    · intro leftZero
      apply List.count_eq_zero.mpr
      intro rightMember
      exact (List.count_eq_zero.mp leftZero) (support.mpr rightMember)
    · intro rightZero
      apply List.count_eq_zero.mpr
      intro leftMember
      exact (List.count_eq_zero.mp rightZero) (support.mp leftMember)
  · exact validCountModThree identity valid selected

private theorem requiredNormalList_eq_of_invariants
    {left right : List Nat}
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right)
    (firstStates : ∀ selected, left.head? = some selected →
      periodThreeFromTwoExponent (left.count selected) =
        periodThreeFromTwoExponent (right.count selected))
    (laterStates : ∀ selected,
      laterExponent (left.count selected) =
        laterExponent (right.count selected)) :
    requiredNormalList left = requiredNormalList right := by
  unfold requiredNormalList
  cases leftOrder : firstOccurrenceSequence left with
  | nil =>
      have rightOrder : firstOccurrenceSequence right = [] :=
        order ▸ leftOrder
      simp [leftOrder, rightOrder]
  | cons first rest =>
      have rightOrder : firstOccurrenceSequence right = first :: rest :=
        order ▸ leftOrder
      rw [rightOrder]
      simp only
      have leftHead : left.head? = some first := by
        cases left with
        | nil => simp [firstOccurrenceSequence] at leftOrder
        | cons head tail =>
            simp only [List.head?_cons]
            simp only [firstOccurrenceSequence] at leftOrder
            exact congrArg List.head? leftOrder
      rw [firstStates first leftHead]
      congr 1
      have renderers :
          (fun selected =>
              List.replicate (laterExponent (left.count selected)) selected) =
            (fun selected =>
              List.replicate (laterExponent (right.count selected)) selected) := by
        funext selected
        rw [laterStates selected]
      rw [renderers]

private theorem derivesOfRequiredInvariants
    (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList)
    (firstState :
      periodThreeFromTwoExponent (left.toList.count left.head) =
        periodThreeFromTwoExponent (right.toList.count left.head))
    (laterStates : ∀ selected,
      laterExponent (left.toList.count selected) =
        laterExponent (right.toList.count selected)) :
    Derives basis left right := by
  have normalEq :
      requiredNormalList left.toList = requiredNormalList right.toList := by
    apply requiredNormalList_eq_of_invariants order
    · intro selected head
      have selectedEq : left.head = selected := by
        simpa [Word.toList] using head
      simpa [selectedEq] using firstState
    · exact laterStates
  have leftNormal := derivesToRequiredNormalForm left
  have rightNormal := derivesToRequiredNormalForm right
  cases leftEq : requiredNormalList left.toList with
  | nil =>
      rw [leftEq] at leftNormal
      exact False.elim leftNormal
  | cons head tail =>
      have rightEq : requiredNormalList right.toList = head :: tail := by
        rw [← normalEq, leftEq]
      rw [leftEq] at leftNormal
      rw [rightEq] at rightNormal
      exact leftNormal.trans rightNormal.symm

/-- Unrestricted completeness of the exact three-law basis for `S6_14921`.
The proof first invokes the shared retained-state-four gather normalizer and
then contracts state four only in blocks with a nonempty left context. -/
theorem basis_complete_aristotle : BasisFor table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  exact derivesOfRequiredInvariants identity.lhs identity.rhs
    (validFirstOccurrenceSequence identity valid)
    (validFirstExponent identity valid)
    (validLaterExponent identity valid)

end Order6S6_14921SingletonShortBlockPeriod3
end CoRoots
end SemigroupBasis

import SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots
import SemigroupBasis.Examples.CommutativePeriodTwoFromThreeOrderFive
import SemigroupBasis.Examples.DualMultipleBlockFive
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

set_option maxRecDepth 100000

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def zyx : Word Nat := w 2 [1, 0]
def zxy : Word Nat := w 2 [0, 1]

def powerLaw : Identity Nat := ⟨xxx, xxxxx⟩
def squareRotationLaw : Identity Nat := ⟨yyxx, xyyx⟩
def gatherLaw : Identity Nat := ⟨xyx, xxy⟩
def suffixSwapLaw : Identity Nat := ⟨zyx, zxy⟩

/-- The route-selected orientation of the exact four-law candidate. -/
def basis : List (Identity Nat) :=
  [powerLaw, squareRotationLaw, gatherLaw, suffixSwapLaw]

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def renameThree (x y z : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => n + 3

/-- Swap two nonempty blocks behind an arbitrary nonempty prefix. -/
theorem derivesSuffixSwap (stem left right : Word Nat) :
    Derives basis
      ((stem ++ left) ++ right)
      ((stem ++ right) ++ left) := by
  have base : Derives basis zyx zxy :=
    Derives.fromBasis (e := suffixSwapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords right left stem)
  simpa [suffixSwapLaw, zyx, zxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later copy of a nonempty block beside its first copy. -/
theorem derivesGather (block middle : Word Nat) :
    Derives basis
      ((block ++ middle) ++ block)
      ((block ++ block) ++ middle) := by
  have base : Derives basis xyx xxy :=
    Derives.fromBasis (e := gatherLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle middle)
  simpa [gatherLaw, xyx, xxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem gatherOneDerivable :
    SemigroupBasis.RetainedStateFour.GatherOneDerivable basis := by
  intro x middle suffix
  cases middle with
  | nil =>
      exact ListDerives.refl _
  | cons y ys =>
      let middleWord := listWordOfCons y ys
      have core :=
        derivesGather (Word.singleton x) middleWord
      have listed := ListDerives.ofWord core
      simpa [middleWord, listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using listed.append suffix

private theorem fiveReductionDerivable :
    SemigroupBasis.RetainedStateFour.FiveReductionDerivable
      basis .periodTwoFromThree := by
  intro x
  have base : Derives basis xxxxx xxx :=
    (Derives.fromBasis (e := powerLaw) (by simp [basis])).symm
  have renamed := base.rename (renameThree x x x)
  simpa [powerLaw, xxx, xxxxx, w, renameThree, Word.map,
    SemigroupBasis.RetainedStateFour.Profile.resetExponent] using
      ListDerives.ofWord renamed

private theorem derivesSquareRotation (left right : Word Nat) :
    Derives basis
      ((left ++ (right ++ right)) ++ left)
      ((right ++ right) ++ (left ++ left)) := by
  have base : Derives basis xyyx yyxx :=
    (Derives.fromBasis (e := squareRotationLaw)
      (by simp [basis])).symm
  have substituted :=
    Derives.subst base
      (instantiateThreeWords left right right)
  simpa [squareRotationLaw, yyxx, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareSquareCommutation
    (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      ((right ++ right) ++ (left ++ left)) := by
  exact Derives.trans
    (derivesSuffixSwap left left (right ++ right))
    (derivesSquareRotation left right)

private theorem derivesCubeSquareCommutation
    (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ left) ++ (right ++ right))
      ((right ++ right) ++ ((left ++ left) ++ left)) := by
  have first :=
    Derives.prepend left
      (derivesSquareSquareCommutation left right)
  have second :=
    Derives.appendRight
      (derivesSquareRotation left right) left
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

private theorem derivesSquareCubeCommutation
    (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ ((right ++ right) ++ right))
      (((right ++ right) ++ right) ++ (left ++ left)) := by
  exact (derivesCubeSquareCommutation right left).symm

private theorem derivesCubeCubeCommutation
    (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ left) ++ ((right ++ right) ++ right))
      (((right ++ right) ++ right) ++ ((left ++ left) ++ left)) := by
  have first :=
    Derives.appendRight
      (derivesCubeSquareCommutation left right) right
  have second :=
    derivesSuffixSwap
      (right ++ right) ((left ++ left) ++ left) right
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

private theorem derivesFourSquareCommutation
    (left right : Word Nat) :
    Derives basis
      ((((left ++ left) ++ left) ++ left) ++ (right ++ right))
      ((right ++ right) ++ (((left ++ left) ++ left) ++ left)) := by
  have first :=
    Derives.prepend (left ++ left)
      (derivesSquareSquareCommutation left right)
  have second :=
    Derives.appendRight
      (derivesSquareSquareCommutation left right) (left ++ left)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

private theorem derivesSquareFourCommutation
    (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (((right ++ right) ++ right) ++ right))
      ((((right ++ right) ++ right) ++ right) ++ (left ++ left)) := by
  exact (derivesFourSquareCommutation right left).symm

private theorem derivesFourCubeCommutation
    (left right : Word Nat) :
    Derives basis
      ((((left ++ left) ++ left) ++ left) ++
        ((right ++ right) ++ right))
      (((right ++ right) ++ right) ++
        (((left ++ left) ++ left) ++ left)) := by
  have first :=
    Derives.prepend (left ++ left)
      (derivesSquareCubeCommutation left right)
  have second :=
    Derives.appendRight
      (derivesSquareCubeCommutation left right) (left ++ left)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

private theorem derivesCubeFourCommutation
    (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ left) ++
        (((right ++ right) ++ right) ++ right))
      ((((right ++ right) ++ right) ++ right) ++
        ((left ++ left) ++ left)) := by
  exact (derivesFourCubeCommutation right left).symm

private theorem derivesFourFourCommutation
    (left right : Word Nat) :
    Derives basis
      ((((left ++ left) ++ left) ++ left) ++
        (((right ++ right) ++ right) ++ right))
      ((((right ++ right) ++ right) ++ right) ++
        (((left ++ left) ++ left) ++ left)) := by
  simpa [Word.append_assoc] using
    derivesSquareSquareCommutation
      (left ++ left) (right ++ right)

private abbrev Block :=
  SemigroupBasis.RetainedStateFour.Block

private def blockWord (block : Block) : Word Nat :=
  match block.state with
  | .one => w block.label []
  | .two => w block.label [block.label]
  | .three => w block.label [block.label, block.label]
  | .four => w block.label [block.label, block.label, block.label]

@[simp]
private theorem blockWord_toList (block : Block) :
    (blockWord block).toList =
      SemigroupBasis.RetainedStateFour.Block.render block := by
  cases block with
  | mk label state =>
      cases state <;> rfl

private theorem derivesTailBlockPermutation
    (stem : Word Nat) {source target : List Block}
    (permutation : source.Perm target) :
    ListDerives basis
      (stem.toList ++
        SemigroupBasis.RetainedStateFour.renderBlocks source)
      (stem.toList ++
        SemigroupBasis.RetainedStateFour.renderBlocks target) := by
  induction permutation generalizing stem with
  | nil =>
      exact ListDerives.refl _
  | cons block _ inductionHypothesis =>
      have next :=
        inductionHypothesis (stem ++ blockWord block)
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
        Word.toList_append, List.append_assoc] using next
  | swap left right suffix =>
      have core :=
        derivesSuffixSwap stem (blockWord right) (blockWord left)
      have listed :=
        (ListDerives.ofWord core).append
          (SemigroupBasis.RetainedStateFour.renderBlocks suffix)
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
        Word.toList_append, List.append_assoc] using listed
  | trans _ _ first second =>
      exact (first stem).trans (second stem)

private theorem derivesLeadingMultipleSwap
    (left right : Block)
    (leftMultiple :
      left.state ≠ SemigroupBasis.RetainedStateFour.State.one)
    (rightMultiple :
      right.state ≠ SemigroupBasis.RetainedStateFour.State.one) :
    ListDerives basis
      (left.render ++ right.render)
      (right.render ++ left.render) := by
  rcases left with ⟨leftLabel, leftState⟩
  rcases right with ⟨rightLabel, rightState⟩
  cases leftState with
  | one =>
      exact False.elim (leftMultiple rfl)
  | two =>
      cases rightState with
      | one =>
          exact False.elim (rightMultiple rfl)
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesSquareSquareCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesSquareCubeCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesSquareFourCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
  | three =>
      cases rightState with
      | one =>
          exact False.elim (rightMultiple rfl)
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesCubeSquareCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesCubeCubeCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesCubeFourCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
  | four =>
      cases rightState with
      | one =>
          exact False.elim (rightMultiple rfl)
      | two =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesFourSquareCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | three =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesFourCubeCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))
      | four =>
          simpa [SemigroupBasis.RetainedStateFour.Block.render,
            SemigroupBasis.RetainedStateFour.State.render,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using
              ListDerives.ofWord
                (derivesFourFourCommutation
                  (Word.singleton leftLabel)
                  (Word.singleton rightLabel))

private theorem blocksNodup
    {blocks : List Block}
    (labelsNodup :
      SemigroupBasis.RetainedStateFour.LabelsNodup blocks) :
    blocks.Nodup := by
  induction blocks with
  | nil =>
      exact List.nodup_nil
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

private def singletonHeadBlock : List Block → Option Nat
  | [] => none
  | block :: _ =>
      if block.state = .one then some block.label else none

private theorem derivesBlocksOfPermutationWithMultipleHeads
    (sourceHead targetHead : Block)
    (sourceTail targetTail : List Block)
    (permutation :
      (sourceHead :: sourceTail).Perm
        (targetHead :: targetTail))
    (sourceMultiple : sourceHead.state ≠ .one)
    (targetMultiple : targetHead.state ≠ .one) :
    ListDerives basis
      (SemigroupBasis.RetainedStateFour.renderBlocks
        (sourceHead :: sourceTail))
      (SemigroupBasis.RetainedStateFour.renderBlocks
        (targetHead :: targetTail)) := by
  by_cases headsEqual : sourceHead = targetHead
  · subst targetHead
    have tailPermutation : sourceTail.Perm targetTail :=
      permutation.cons_inv
    simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using
      derivesTailBlockPermutation
        (blockWord sourceHead) tailPermutation
  · have targetInSource :
        targetHead ∈ sourceHead :: sourceTail :=
      permutation.mem_iff.mpr (List.Mem.head targetTail)
    have targetNotSource : targetHead ≠ sourceHead := Ne.symm headsEqual
    have targetInTail : targetHead ∈ sourceTail := by
      simpa [targetNotSource] using targetInSource
    have exposePermutation :
        sourceTail.Perm
          (targetHead :: sourceTail.erase targetHead) :=
      List.perm_cons_erase targetInTail
    have exposed :
        ListDerives basis
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (sourceHead :: sourceTail))
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (sourceHead :: targetHead :: sourceTail.erase targetHead)) := by
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using
        derivesTailBlockPermutation
          (blockWord sourceHead) exposePermutation
    have swapped :
        ListDerives basis
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (sourceHead :: targetHead :: sourceTail.erase targetHead))
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (targetHead :: sourceHead :: sourceTail.erase targetHead)) := by
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks,
        List.append_assoc] using
          (derivesLeadingMultipleSwap sourceHead targetHead
            sourceMultiple targetMultiple).append
              (SemigroupBasis.RetainedStateFour.renderBlocks
                (sourceTail.erase targetHead))
    have erasedPermutation :
        (sourceHead :: sourceTail.erase targetHead).Perm targetTail := by
      have exposeSource :
          (sourceHead :: sourceTail).Perm
            (sourceHead :: targetHead :: sourceTail.erase targetHead) :=
        List.Perm.cons sourceHead exposePermutation
      have moveTargetToFront :
          (sourceHead :: sourceTail).Perm
            (targetHead :: sourceHead :: sourceTail.erase targetHead) :=
        exposeSource.trans
          (List.Perm.swap targetHead sourceHead
            (sourceTail.erase targetHead))
      exact (moveTargetToFront.symm.trans permutation).cons_inv
    have finished :
        ListDerives basis
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (targetHead :: sourceHead :: sourceTail.erase targetHead))
          (SemigroupBasis.RetainedStateFour.renderBlocks
            (targetHead :: targetTail)) := by
      simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using
        derivesTailBlockPermutation
          (blockWord targetHead) erasedPermutation
    exact exposed.trans <| swapped.trans finished

private theorem derivesBlocksOfInvariants
    {source target : List Block}
    (sourceLabels :
      SemigroupBasis.RetainedStateFour.LabelsNodup source)
    (targetLabels :
      SemigroupBasis.RetainedStateFour.LabelsNodup target)
    (sameState :
      SemigroupBasis.RetainedStateFour.SameStateMap source target)
    (sameSingletonHead :
      singletonHeadBlock source = singletonHeadBlock target) :
    ListDerives basis
      (SemigroupBasis.RetainedStateFour.renderBlocks source)
      (SemigroupBasis.RetainedStateFour.renderBlocks target) := by
  have sourceNodup := blocksNodup sourceLabels
  have targetNodup := blocksNodup targetLabels
  have permutation : source.Perm target :=
    SemigroupBasis.BlockTrace.perm_of_nodup_mem_iff
      sourceNodup targetNodup sameState
  cases source with
  | nil =>
      have targetNil : target = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq.symm
      subst target
      exact ListDerives.refl _
  | cons sourceHead sourceTail =>
      cases target with
      | nil =>
          simp at permutation
      | cons targetHead targetTail =>
          rcases sourceHead with ⟨sourceLabel, sourceState⟩
          rcases targetHead with ⟨targetLabel, targetState⟩
          cases sourceState with
          | one =>
              cases targetState with
              | one =>
                  have labelsEqual : sourceLabel = targetLabel := by
                    simpa [singletonHeadBlock] using sameSingletonHead
                  subst targetLabel
                  have tailPermutation :
                      sourceTail.Perm targetTail :=
                    permutation.cons_inv
                  simpa [SemigroupBasis.RetainedStateFour.renderBlocks] using
                    derivesTailBlockPermutation
                      (blockWord
                        { label := sourceLabel, state := .one })
                      tailPermutation
              | two =>
                  simp [singletonHeadBlock] at sameSingletonHead
              | three =>
                  simp [singletonHeadBlock] at sameSingletonHead
              | four =>
                  simp [singletonHeadBlock] at sameSingletonHead
          | two =>
              have targetMultiple :
                  targetState ≠
                    SemigroupBasis.RetainedStateFour.State.one := by
                intro equality
                subst targetState
                simp [singletonHeadBlock] at sameSingletonHead
              exact derivesBlocksOfPermutationWithMultipleHeads
                { label := sourceLabel, state := .two }
                { label := targetLabel, state := targetState }
                sourceTail targetTail permutation (by simp) targetMultiple
          | three =>
              have targetMultiple :
                  targetState ≠
                    SemigroupBasis.RetainedStateFour.State.one := by
                intro equality
                subst targetState
                simp [singletonHeadBlock] at sameSingletonHead
              exact derivesBlocksOfPermutationWithMultipleHeads
                { label := sourceLabel, state := .three }
                { label := targetLabel, state := targetState }
                sourceTail targetTail permutation (by simp) targetMultiple
          | four =>
              have targetMultiple :
                  targetState ≠
                    SemigroupBasis.RetainedStateFour.State.one := by
                intro equality
                subst targetState
                simp [singletonHeadBlock] at sameSingletonHead
              exact derivesBlocksOfPermutationWithMultipleHeads
                { label := sourceLabel, state := .four }
                { label := targetLabel, state := targetState }
                sourceTail targetTail permutation (by simp) targetMultiple

private theorem periodTwoFromThreeState_eq_one_iff
    {n : Nat} (positive : 0 < n) :
    SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree.state n =
        .one ↔
      n = 1 := by
  by_cases small : n < 3
  · have cases : n = 1 ∨ n = 2 := by omega
    rcases cases with rfl | rfl <;> decide
  · have remainder : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by
      omega
    rcases remainder with remainder | remainder <;>
      simp [SemigroupBasis.RetainedStateFour.Profile.state,
        SemigroupBasis.RetainedStateFour.Profile.exponent,
        SemigroupBasis.RetainedStateFour.State.ofExponent,
        periodTwoFromThreeExponent, small, remainder] <;>
      omega

private theorem singletonHeadBlock_normalize (word : Word Nat) :
    singletonHeadBlock
        (SemigroupBasis.RetainedStateFour.normalizeBlocks
          .periodTwoFromThree word.toList) =
      dualMultipleBlockFiveSingletonHead word := by
  cases word with
  | mk head tail =>
      have positive : 0 < (head :: tail).count head := by simp
      unfold dualMultipleBlockFiveSingletonHead
      simp only [Word.toList, Word.head,
        SemigroupBasis.RetainedStateFour.normalizeBlocks,
        singletonHeadBlock]
      simp only [periodTwoFromThreeState_eq_one_iff positive]

/-- The exponent states and optional singleton head are a complete set of
derivational invariants for the route-selected four-law basis. -/
theorem derivesOfInvariantEq
    (left right : Word Nat)
    (exponents :
      ∀ letter,
        periodTwoFromThreeExponent (left.toList.count letter) =
          periodTwoFromThreeExponent (right.toList.count letter))
    (singletonHead :
      dualMultipleBlockFiveSingletonHead left =
        dualMultipleBlockFiveSingletonHead right) :
    Derives basis left right := by
  let profile :=
    SemigroupBasis.RetainedStateFour.Profile.periodTwoFromThree
  let leftBlocks :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks
      profile left.toList
  let rightBlocks :=
    SemigroupBasis.RetainedStateFour.normalizeBlocks
      profile right.toList
  have leftNormal :=
    SemigroupBasis.RetainedStateFour.derivesNormalize_of_laws
      gatherOneDerivable fiveReductionDerivable left.toList
  have rightNormal :=
    SemigroupBasis.RetainedStateFour.derivesNormalize_of_laws
      gatherOneDerivable fiveReductionDerivable right.toList
  have sameState :
      SemigroupBasis.RetainedStateFour.SameStateMap
        leftBlocks rightBlocks := by
    apply
      SemigroupBasis.CoRoots.Order6FirstOccurrenceBlockRoots.sameStateMap_of_exponents
    exact exponents
  have sameHead : singletonHeadBlock leftBlocks =
      singletonHeadBlock rightBlocks := by
    simpa [leftBlocks, rightBlocks, profile,
      singletonHeadBlock_normalize] using singletonHead
  have bridge :=
    derivesBlocksOfInvariants
      (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
        profile left.toList)
      (SemigroupBasis.RetainedStateFour.normalizeBlocks_labelsNodup
        profile right.toList)
      sameState sameHead
  have listed : ListDerives basis left.toList right.toList :=
    leftNormal.trans <| bridge.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact listed.toWord

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem dualMultipleBlockFive_models :
    Models dualMultipleBlockFive.semigroup basis :=
  FiniteCertificate.checkModels_sound
    dualMultipleBlockFive basis toFinThree (by decide)

theorem s5_223_models :
    Models s5_223.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_223 basis toFinThree (by decide)

private theorem singletonHead_eq_of_dualMultipleBlockFive_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy dualMultipleBlockFive.semigroup) :
    dualMultipleBlockFiveSingletonHead identity.lhs =
      dualMultipleBlockFiveSingletonHead identity.rhs := by
  apply Option.ext
  intro letter
  rw [dualMultipleBlockFiveSingletonHead_eq_some_iff,
    dualMultipleBlockFiveSingletonHead_eq_some_iff,
    dualMultipleBlockFiveValid_state_eq identity valid letter]

/-- Parameter-free completeness for the intersection of the canonical
dual-multiple-block and period-two-from-three factor theories. -/
def naturalIntersectionBasis :
    IntersectionBasis
      dualMultipleBlockFive.semigroup
      s5_223.semigroup basis where
  leftModels := dualMultipleBlockFive_models
  rightModels := s5_223_models
  complete := by
    intro identity leftValid rightValid
    exact derivesOfInvariantEq identity.lhs identity.rhs
      (s5_223Separates identity rightValid)
      (singletonHead_eq_of_dualMultipleBlockFive_valid
        identity leftValid)

def xxyy : Word Nat := w 0 [0, 1, 1]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def representativePowerLaw : Identity Nat := ⟨xxx, xxxxx⟩
def representativeSquareRotationLaw : Identity Nat := ⟨xxyy, xyyx⟩
def representativeGatherLaw : Identity Nat := ⟨xyx, yxx⟩
def representativePrefixSwapLaw : Identity Nat := ⟨xyz, yxz⟩

/-- Exact catalogue-orientation basis recorded by
`factor_intersection_residual59_v1`. -/
def representativeBasis : List (Identity Nat) :=
  [representativePowerLaw, representativeSquareRotationLaw,
    representativeGatherLaw, representativePrefixSwapLaw]

theorem reversedBasis_eq_representativeBasis :
    reversedBasis basis = representativeBasis := by
  decide

/-- The same intersection in the stored `S5_121` catalogue orientation. -/
def representativeIntersectionBasis :
    IntersectionBasis
      dualMultipleBlockFiveStored.semigroup
      s5_223.semigroup representativeBasis := by
  have reversed := naturalIntersectionBasis.oppositeReversed
  rw [reversedBasis_eq_representativeBasis,
    s5_223SelfDual] at reversed
  simpa [dualMultipleBlockFiveStored,
    dualMultipleBlockFiveStoredMul,
    dualMultipleBlockFive,
    FiniteTable.semigroup, Semigroup.opposite] using reversed

end SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock

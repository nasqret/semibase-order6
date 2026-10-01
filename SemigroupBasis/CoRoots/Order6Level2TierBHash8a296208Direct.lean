import SemigroupBasis.CoRoots.S5_379Family
import SemigroupBasis.CoRoots.S5_442Invariant
import SemigroupBasis.CoRoots.S5_790Invariant
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Unrestricted completeness for the direct-factor part of the displayed-basis
group with SHA-256
`8a29620870ac67a01b130021b9f014d89b2c1f99824f929efd82c51db88f27d8`.

The common invariant is the complete `S5_379` component/simple-variable
signature together with the first letter.  The only `S5_379` source law that
can change the first letter is replayed behind a protected prefix using the
guarded law `xyzyz = xzyyz`.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzyz : Word Nat := w 0 [1, 2, 1, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftContractionLaw : Identity Nat := ⟨xxyx, xyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def crossingFinalLaw : Identity Nat := ⟨xyxy, xyyx⟩
def attachmentLaw : Identity Nat := ⟨xyxzy, xyyzx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def guardedCrossingInitialLaw : Identity Nat := ⟨xyzyz, xzyyz⟩

/-- The exact seven-law displayed candidate. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftContractionLaw, rightDuplicationLaw,
    crossingFinalLaw, attachmentLaw, closedInteriorSwapLaw,
    guardedCrossingInitialLaw]

theorem basis_length : basis.length = 7 := by
  decide

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

private theorem derivesPowerExpansion (word : Word Nat) :
    Derives basis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords word word word)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesLeftContraction
    (left middle : Word Nat) :
    Derives basis
      (((left ++ left) ++ middle) ++ left)
      ((left ++ middle) ++ left) := by
  have substituted :=
    derivesBasisSubstitution leftContractionLaw (by simp [basis])
      (instantiateThreeWords left middle middle)
  simpa [leftContractionLaw, xxyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesGuardedCrossingInitial
    (guard left right : Word Nat) :
    Derives basis
      (guard ++ (((left ++ right) ++ left) ++ right))
      (guard ++ (((right ++ left) ++ left) ++ right)) := by
  have substituted :=
    derivesBasisSubstitution guardedCrossingInitialLaw
      (by simp [basis])
      (instantiateThreeWords guard left right)
  simpa [guardedCrossingInitialLaw, xyzyz, xzyyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (substitution : Nat -> Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat -> Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete `S5_379` normalizer behind a protected nonempty
prefix. -/
theorem liftS5_379UnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_379.basis left right)
    (guard : Word Nat) (substitution : Nat -> Word Nat) :
    Derives basis
      (guard ++ left.bind substitution)
      (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_379.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Derives.prepend guard <|
          derivesBasisSubstitution powerLaw (by simp [basis]) substitution
      · exact Derives.prepend guard <|
          (derivesBasisSubstitution leftContractionLaw
            (by simp [basis]) substitution).symm
      · exact Derives.prepend guard <|
          derivesBasisSubstitution rightDuplicationLaw
            (by simp [basis]) substitution
      · exact Derives.prepend guard <|
          derivesBasisSubstitution crossingFinalLaw
            (by simp [basis]) substitution
      · have xyxyShape : SemigroupBasis.CoRoots.S5_379.xyxy =
            (⟨0, [1, 0, 1]⟩ : Word Nat) := by decide
        have yxxyShape : SemigroupBasis.CoRoots.S5_379.yxxy =
            (⟨1, [0, 0, 1]⟩ : Word Nat) := by decide
        simpa [SemigroupBasis.CoRoots.S5_379.crossingInitialLaw,
          xyxyShape, yxxyShape,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesGuardedCrossingInitial guard
            (substitution 0) (substitution 1)
      · exact Derives.prepend guard <|
          derivesBasisSubstitution closedInteriorSwapLaw
            (by simp [basis]) substitution
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis guard substitution).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis guard substitution).trans
          (secondHypothesis guard substitution)
  | prepend front _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis
          (guard ++ front.bind substitution) substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis guard substitution)
          (suffix.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis guard
          (fun letter => (first letter).bind substitution)

/-! ## Fixed-first component/simple-variable closure -/

structure SameGuardedComponentSimpleSignature
    (left right : Word Nat) : Prop where
  componentSimple :
    SemigroupBasis.CoRoots.S5_379.SameComponentSimpleSignature
      left right
  first : left.head = right.head

namespace SameGuardedComponentSimpleSignature

theorem symm {left right : Word Nat}
    (same : SameGuardedComponentSimpleSignature left right) :
    SameGuardedComponentSimpleSignature right left := by
  refine ⟨⟨?_, ?_, ?_⟩, same.first.symm⟩
  · intro valuation
    exact (same.componentSimple.component valuation).symm
  · intro letter
    exact (same.componentSimple.support letter).symm
  · intro letter
    exact (same.componentSimple.globallySimple letter).symm

end SameGuardedComponentSimpleSignature

private theorem connectedComponentSignaturesList_canonical
    (letters : List Nat) :
    connectedComponentFourCanonicalSignatures
      (connectedComponentSignaturesList letters) := by
  let components := connectedComponentDecomposeList letters
  have nonempty :=
    connectedComponentDecomposeList_nonempty_components letters
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint letters
  constructor
  · intro signature signatureMember
    rw [connectedComponentSignaturesList] at signatureMember
    rcases List.mem_map.mp signatureMember with
      ⟨component, componentMember, rfl⟩
    exact connectedComponentSignatureOfList_valid
      (nonempty component componentMember)
  · rw [connectedComponentSignaturesList, List.pairwise_map]
    apply pairwise.imp
    intro left right disjoint
    intro letter leftMember rightMember
    apply disjoint letter
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at leftMember
      exact leftMember
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at rightMember
      exact rightMember

private def singletonComponentSignature
    (letter : Nat) : connectedComponentSignature :=
  ⟨[letter], false⟩

private theorem singleton_cons_signatures_canonical
    (head : Nat) (tail : List Nat)
    (headAbsent : head ∉ tail) :
    connectedComponentFourCanonicalSignatures
      (singletonComponentSignature head ::
        connectedComponentSignaturesList tail) := by
  have tailCanonical :=
    connectedComponentSignaturesList_canonical tail
  constructor
  · intro signature member
    rcases List.mem_cons.mp member with rfl | member
    · simp [singletonComponentSignature,
        connectedComponentSignatureValid]
    · exact tailCanonical.1 signature member
  · rw [List.pairwise_cons]
    refine ⟨?_, tailCanonical.2⟩
    intro signature signatureMember tested singletonMember supportMember
    have testedEq : tested = head := by
      simpa [singletonComponentSignature] using singletonMember
    subst tested
    have renderedMember :
        head ∈ connectedComponentRenderSignature signature :=
      (connectedComponentRenderSignature_mem_iff
        (tailCanonical.1 signature signatureMember).1 head).2
        supportMember
    have allRenderedMember :
        head ∈ connectedComponentRenderSignatures
          (connectedComponentSignaturesList tail) := by
      rw [connectedComponentRenderSignatures, List.mem_flatMap]
      exact ⟨signature, signatureMember, renderedMember⟩
    have canonicalMember :
        head ∈ connectedComponentCanonicalRenderList tail := by
      simpa [connectedComponentCanonicalRenderList] using
        allRenderedMember
    exact headAbsent <|
      (connectedComponentCanonicalRenderList_mem_iff head tail).1
        canonicalMember

private theorem canonicalRenderList_cons_of_head_absent
    (head : Nat) (tail : List Nat)
    (headAbsent : head ∉ tail) :
    connectedComponentCanonicalRenderList (head :: tail) =
      head :: connectedComponentCanonicalRenderList tail := by
  let source : Word Nat := ⟨head, tail⟩
  let target : Word Nat :=
    ⟨head, connectedComponentCanonicalRenderList tail⟩
  have sourceCanonical :=
    connectedComponentFourSignaturesWord_canonical source
  have targetCanonical :=
    singleton_cons_signatures_canonical head tail headAbsent
  have sourceDerivation :=
    connectedComponentFour_derivesCanonical source
  have targetDerivation :
      Derives connectedComponentFourBasis source target := by
    have tailDerivation :=
      connectedComponentCanonicalRenderList_derives tail
    have prefixed := tailDerivation.prepend [head]
    simpa [source, target, connectedComponentWordOfCons] using
      prefixed.toWord
  have equalEval :
      ∀ valuation : Nat -> Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender source) =
          connectedComponentFour.semigroup.eval valuation target := by
    intro valuation
    have sourceSound :=
      sourceDerivation.sound connectedComponentFourBasis_models valuation
    have targetSound :=
      targetDerivation.sound connectedComponentFourBasis_models valuation
    exact sourceSound.symm.trans targetSound
  have signaturesEqual :
      connectedComponentSignaturesWord source =
        singletonComponentSignature head ::
          connectedComponentSignaturesList tail := by
    apply connectedComponentCanonical_eq_of_equalEval
      sourceCanonical targetCanonical
      (connectedComponentCanonicalRender source) target
    · exact connectedComponentCanonicalRender_toList source
    · simp [target, Word.toList, singletonComponentSignature,
        connectedComponentRenderSignatures,
        connectedComponentCanonicalRenderList]
    · exact equalEval
  change
    connectedComponentRenderSignatures
        (connectedComponentSignaturesWord source) =
      head ::
        connectedComponentRenderSignatures
          (connectedComponentSignaturesList tail)
  rw [signaturesEqual]
  rfl

private theorem suffixSameComponentSimple
    (head : Nat) (left right : Word Nat)
    (headAbsentLeft : head ∉ left.toList)
    (headAbsentRight : head ∉ right.toList)
    (whole :
      SameGuardedComponentSimpleSignature
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)) :
    SemigroupBasis.CoRoots.S5_379.SameComponentSimpleSignature
      left right := by
  have leftSplit :=
    canonicalRenderList_cons_of_head_absent
      head left.toList headAbsentLeft
  have rightSplit :=
    canonicalRenderList_cons_of_head_absent
      head right.toList headAbsentRight
  have wholeComponents :=
    S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
      (Word.singleton head ++ left)
      (Word.singleton head ++ right)
      whole.componentSimple.component
  have wholeCanonical :
      connectedComponentCanonicalRenderList
          (head :: left.toList) =
        connectedComponentCanonicalRenderList
          (head :: right.toList) := by
    exact connectedComponentCanonicalRenderList_eq_of_signature_eq
      wholeComponents
  rw [leftSplit, rightSplit] at wholeCanonical
  have suffixCanonical :
      connectedComponentCanonicalRenderList left.toList =
        connectedComponentCanonicalRenderList right.toList :=
    (List.cons.inj wholeCanonical).2
  have canonicalWordEq :
      connectedComponentCanonicalRender left =
        connectedComponentCanonicalRender right := by
    apply Word.toList_injective
    simpa [connectedComponentCanonicalRender_toList] using
      suffixCanonical
  have componentDerivation :
      Derives connectedComponentFourBasis left right := by
    exact (connectedComponentFour_derivesCanonical left).trans <| by
      rw [canonicalWordEq]
      exact (connectedComponentFour_derivesCanonical right).symm
  refine ⟨?_, ?_, ?_⟩
  · intro valuation
    exact componentDerivation.sound
      connectedComponentFourBasis_models valuation
  · intro letter
    by_cases equal : letter = head
    · subst letter
      simp [headAbsentLeft, headAbsentRight]
    · simpa [uniqueSeparatorWordOfCons, Word.toList, Word.append,
        Word.singleton, equal, Ne.symm equal] using
        whole.componentSimple.support letter
  · intro letter
    by_cases equal : letter = head
    · subst letter
      simp only [SemigroupBasis.CoRoots.S5_379.GloballySimple,
        uniqueSeparatorWordOfCons, Word.toList, Word.append,
        Word.singleton]
      have leftZero : List.count head (left.head :: left.tail) = 0 :=
        List.count_eq_zero.mpr
          (by simpa [Word.toList] using headAbsentLeft)
      have rightZero : List.count head (right.head :: right.tail) = 0 :=
        List.count_eq_zero.mpr
          (by simpa [Word.toList] using headAbsentRight)
      simp [leftZero, rightZero]
    · simpa [SemigroupBasis.CoRoots.S5_379.GloballySimple,
        uniqueSeparatorWordOfCons, Word.toList, Word.append,
        Word.singleton, equal, Ne.symm equal] using
        whole.componentSimple.globallySimple letter

private theorem headSimple_iff
    {left right : Word Nat}
    (same : SameGuardedComponentSimpleSignature left right) :
    SemigroupBasis.CoRoots.S5_379.GloballySimple left left.head ↔
      SemigroupBasis.CoRoots.S5_379.GloballySimple right right.head := by
  simpa [same.first] using
    same.componentSimple.globallySimple left.head

private theorem headNotMemTailOfSimple
    (word : Word Nat)
    (simple :
      SemigroupBasis.CoRoots.S5_379.GloballySimple word word.head) :
    word.head ∉ word.tail := by
  intro member
  have positive : 0 < word.tail.count word.head :=
    List.count_pos_iff.mpr member
  simp only [SemigroupBasis.CoRoots.S5_379.GloballySimple,
    Word.toList, List.count_cons_self] at simple
  omega

private theorem headMemTailOfNotSimple
    (word : Word Nat)
    (notSimple :
      ¬ SemigroupBasis.CoRoots.S5_379.GloballySimple word word.head) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply notSimple
  cases word with
  | mk head tail =>
      simp [SemigroupBasis.CoRoots.S5_379.GloballySimple,
        Word.toList, List.count_eq_zero.mpr absent]

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameGuardedComponentSimpleSignature left right)
    (rightHeadSimple :
      SemigroupBasis.CoRoots.S5_379.GloballySimple right right.head)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.componentSimple.support letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    have headOrTail :
        letter = left.head ∨ letter ∈ left.tail := by
      simpa [Word.toList] using leftMember
    rcases headOrTail with equal | inTail
    · exact equal
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.first
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfSimple right rightHeadSimple)
      rightHeadInTail

private abbrev ListDerives := S5_107.ListDerives basis

private theorem listDerivesAddInitialHead
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle := S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesLeftContraction
            (Word.singleton head) middle).symm
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

private theorem derivesAddInitialHead
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialHead head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

/-- Unrestricted syntactic completeness of the `S5_379` signature together
with the fixed first letter. -/
theorem derivesOfSameGuardedComponentSimpleSignature
    {left right : Word Nat}
    (same : SameGuardedComponentSimpleSignature left right) :
    Derives basis left right := by
  have simpleIff := headSimple_iff same
  by_cases leftHeadSimple :
      SemigroupBasis.CoRoots.S5_379.GloballySimple left left.head
  · have rightHeadSimple :
        SemigroupBasis.CoRoots.S5_379.GloballySimple right right.head :=
      simpleIff.mp leftHeadSimple
    have tailsEmpty : left.tail = [] ↔ right.tail = [] := by
      constructor
      · exact tailNilOfSameSignature same rightHeadSimple
      · exact tailNilOfSameSignature same.symm leftHeadSimple
    cases left with
    | mk leftHead leftTail =>
        cases right with
        | mk rightHead rightTail =>
            simp only at same leftHeadSimple rightHeadSimple tailsEmpty
            have heads : leftHead = rightHead := same.first
            subst rightHead
            cases leftTail with
            | nil =>
                have rightEmpty : rightTail = [] := tailsEmpty.mp rfl
                subst rightTail
                exact Derives.refl _
            | cons leftSecond leftRest =>
                cases rightTail with
                | nil =>
                    have impossible : leftSecond :: leftRest = [] :=
                      tailsEmpty.mpr rfl
                    contradiction
                | cons rightSecond rightRest =>
                    let leftSuffix : Word Nat :=
                      Word.mk leftSecond leftRest
                    let rightSuffix : Word Nat :=
                      Word.mk rightSecond rightRest
                    have leftHeadAbsent :
                        leftHead ∉ leftSuffix.toList := by
                      change leftHead ∉ leftSecond :: leftRest
                      exact headNotMemTailOfSimple
                        (Word.mk leftHead (leftSecond :: leftRest))
                        leftHeadSimple
                    have rightHeadAbsent :
                        leftHead ∉ rightSuffix.toList := by
                      change leftHead ∉ rightSecond :: rightRest
                      exact headNotMemTailOfSimple
                        (Word.mk leftHead (rightSecond :: rightRest))
                        rightHeadSimple
                    have whole :
                        SameGuardedComponentSimpleSignature
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix) := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using same
                    have suffixSame :=
                      suffixSameComponentSimple
                        leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent whole
                    have suffixDerivation :=
                      SemigroupBasis.CoRoots.S5_379.derives_of_sameComponentSimpleSignature
                        suffixSame
                    have lifted :=
                      liftS5_379UnderPrefix suffixDerivation
                        (Word.singleton leftHead) Word.singleton
                    rw [bind_singleton, bind_singleton] at lifted
                    simpa [leftSuffix, rightSuffix, Word.singleton,
                      Word.append] using lifted
  · have rightHeadNotSimple :
        ¬ SemigroupBasis.CoRoots.S5_379.GloballySimple
          right right.head := by
      intro rightSimple
      exact leftHeadSimple (simpleIff.mpr rightSimple)
    have leftHeadInTail : left.head ∈ left.tail :=
      headMemTailOfNotSimple left leftHeadSimple
    have rightHeadInTail : right.head ∈ right.tail :=
      headMemTailOfNotSimple right rightHeadNotSimple
    have leftExpanded :=
      derivesAddInitialHead left leftHeadInTail
    have rightExpanded :=
      derivesAddInitialHead right rightHeadInTail
    have commonDerivation :=
      SemigroupBasis.CoRoots.S5_379.derives_of_sameComponentSimpleSignature
        same.componentSimple
    have lifted :=
      liftS5_379UnderPrefix commonDerivation
        (Word.singleton left.head) Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (Word.singleton left.head ++ left)
          (Word.singleton right.head ++ right) := by
      simpa [same.first] using lifted
    exact leftExpanded.trans <| guarded.trans rightExpanded.symm

/-- Any semigroup carrying the three finite detectors for component order,
global simplicity, and first letter has the seven-law basis.  This endpoint
does not require the detector maps to be jointly injective. -/
theorem basisForOfComponentMultiplicityHeadDetectors
    {S : Type u} (target : Semigroup S)
    (targetModels : Models target basis)
    (component :
      SplitSurjection target connectedComponentFour.semigroup)
    (multiplicity :
      SplitSurjection target commutativeExponentThree.semigroup)
    (head : Embedding leftZeroTwo.semigroup target) :
    BasisFor target basis := by
  refine ⟨targetModels, ?_⟩
  intro identity valid
  have componentValid :
      identity.SatisfiedBy connectedComponentFour.semigroup :=
    component.pushforwardIdentity identity valid
  have multiplicityValid :
      identity.SatisfiedBy commutativeExponentThree.semigroup :=
    multiplicity.pushforwardIdentity identity valid
  have headValid :
      identity.SatisfiedBy leftZeroTwo.semigroup :=
    head.pullback_identity identity valid
  exact derivesOfSameGuardedComponentSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_379.sameSignature_of_factors
        identity componentValid multiplicityValid,
      S5_790Invariant.leftZeroValid_head_eq identity headValid⟩

/-! ## Direct factor intersections -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_4.table basis toFinThree (by decide)

private theorem modelsS3_15 :
    Models SemigroupBasis.Generated.S3_15.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_15.table basis toFinThree (by decide)

private theorem modelsS5_379 :
    Models SemigroupBasis.CoRoots.S5_379.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_379.table basis toFinThree (by decide)

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup = table.semigroup.opposite :=
  rfl

private theorem modelsS5_379Opposite :
    Models SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable SemigroupBasis.CoRoots.S5_379.table)
    basis toFinThree (by decide)

private def componentAntiMap (value : Fin 4) : Fin 4 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 3 else 2

/-- The explicit anti-automorphism `[0,1,3,2]` of `S4_70`. -/
private def componentAntiEmbedding :
    Embedding connectedComponentFour.semigroup
      connectedComponentFour.semigroup.opposite where
  toFun := componentAntiMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private theorem sameSignatureOfS5_379OppositeValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite) :
    SemigroupBasis.CoRoots.S5_379.SameComponentSimpleSignature
      identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.CoRoots.S5_379.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity SemigroupBasis.CoRoots.S5_379.table.semigroup).mp valid
  have reversedSame :=
    SemigroupBasis.CoRoots.S5_379.valid_sameSignature
      identity.reversed reversedValid
  refine ⟨?_, ?_, ?_⟩
  · have oppositeComponent :
        identity.SatisfiedBy connectedComponentFour.semigroup.opposite :=
      (Identity.satisfiedBy_opposite_iff_reversed
        identity connectedComponentFour.semigroup).mpr
          reversedSame.component
    exact componentAntiEmbedding.pullback_identity
      identity oppositeComponent
  · intro letter
    simpa [Identity.reversed, Word.toList_reverse] using
      reversedSame.support letter
  · intro letter
    simpa [SemigroupBasis.CoRoots.S5_379.GloballySimple,
      Identity.reversed, Word.toList_reverse, List.count_reverse] using
      reversedSame.globallySimple letter

private theorem head_eq_of_s2_4_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_4.table_eq_catalogue_model] using
      valid
  exact S5_790Invariant.leftZeroValid_head_eq identity markerValid

private theorem head_eq_of_s3_15_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftNormalBandFifteen.semigroup at valid
  exact leftNormalBandFifteenValid_head_eq identity valid

theorem derivesOfS2_4S5_379Valid
    (identity : Identity Nat)
    (headValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (signatureValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_379.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedComponentSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_379.valid_sameSignature
        identity signatureValid,
      head_eq_of_s2_4_valid identity headValid⟩

theorem derivesOfS3_15S5_379Valid
    (identity : Identity Nat)
    (headValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup)
    (signatureValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_379.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedComponentSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_379.valid_sameSignature
        identity signatureValid,
      head_eq_of_s3_15_valid identity headValid⟩

theorem derivesOfS2_4S5_379OppositeValid
    (identity : Identity Nat)
    (headValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (signatureValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedComponentSimpleSignature
    ⟨sameSignatureOfS5_379OppositeValid identity signatureValid,
      head_eq_of_s2_4_valid identity headValid⟩

def intersectionBasisS2_4S5_379 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.CoRoots.S5_379.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_379
  complete := derivesOfS2_4S5_379Valid

def intersectionBasisS3_15S5_379 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.CoRoots.S5_379.table.semigroup
      basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_379
  complete := derivesOfS3_15S5_379Valid

def intersectionBasisS2_4S5_379Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_379Opposite
  complete := derivesOfS2_4S5_379OppositeValid

end SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct

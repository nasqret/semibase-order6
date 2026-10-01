import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_790Invariant
import SemigroupBasis.Examples.ConnectedComponentFourFinal

namespace SemigroupBasis.CoRoots.S5_790

open SemigroupBasis
open SemigroupBasis.Examples

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay an arbitrary `S4_70` derivation after a fixed nonempty prefix.
The first five root laws are direct or derived consequences of `basis`; the
bare endpoint rotation is replayed by the prefix-guarded sixth law. -/
private theorem liftConnectedComponentUnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives connectedComponentFourBasis left right)
    (pref : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (pref ++ left.bind sigma)
      (pref ++ right.bind sigma) := by
  induction derivation generalizing pref sigma with
  | fromBasis member =>
      simp only [connectedComponentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [connectedComponentPowerLaw, connectedComponentXX,
          connectedComponentXXX, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          Derives.prepend pref
            (derivesPowerExpansion (sigma 0))
      · simpa [connectedComponentLeftDuplicationLaw,
          connectedComponentXYX, connectedComponentXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pref
            (derivesLeftDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentMiddleDuplicationLaw,
          connectedComponentXYX, connectedComponentXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pref
            (derivesMiddleDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentRightDuplicationLaw,
          connectedComponentXYX, connectedComponentXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pref
            (derivesRightDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentAlternatingLaw,
          connectedComponentXYX, connectedComponentXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pref
            (derivesAlternating (sigma 0) (sigma 1))
      · simpa [connectedComponentRotationLaw,
          connectedComponentXYX, connectedComponentYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesPrefixedRotation pref (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih pref sigma)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst pref sigma) (ihSecond pref sigma)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (pref ++ pre.bind sigma) sigma
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih pref sigma) (post.bind sigma)
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih pref (fun letter => (tau letter).bind sigma)

private theorem liftConnectedComponentListUnderPrefix
    (pref : Word Nat) {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right) :
    S5_107.ListDerives basis
      (pref.toList ++ left)
      (pref.toList ++ right) := by
  cases derivation with
  | empty =>
      simpa using
        S5_107.ListDerives.refl
          (basis := basis) pref.toList
  | words wordDerivation =>
      have lifted :=
        liftConnectedComponentUnderPrefix
          wordDerivation pref Word.singleton
      rw [bind_singleton, bind_singleton] at lifted
      simpa [Word.toList_append] using
        S5_107.ListDerives.ofWord lifted

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
    have prefixed :=
      tailDerivation.prepend [head]
    simpa [source, target, connectedComponentWordOfCons] using
      prefixed.toWord
  have equalEval :
      ∀ valuation : Nat → Fin 4,
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

private theorem s4_70_valid_of_sameComponents
    {left right : Word Nat}
    (same :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right) :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_70.table.semigroup := by
  have leftDerivation :=
    connectedComponentFour_derivesCanonical left
  have rightDerivation :=
    connectedComponentFour_derivesCanonical right
  have normalEqual :
      connectedComponentCanonicalRender left =
        connectedComponentCanonicalRender right :=
    connectedComponentCanonicalRender_eq_of_signature_eq same
  have rootDerivation :
      Derives connectedComponentFourBasis left right := by
    exact leftDerivation.trans <| by
      rw [normalEqual]
      exact rightDerivation.symm
  intro valuation
  simpa [Generated.S4_70.table] using
    rootDerivation.sound connectedComponentFourBasis_models valuation

private theorem unaryCut_empty_head_iff_count_one
    (word : Word Nat) :
    connectedComponentFourUnaryCut [] word.head word.toList ↔
      word.toList.count word.head = 1 := by
  cases word with
  | mk head tail =>
      constructor
      · rintro
          ⟨actualLeft, actualRight, shape,
            leftExact, headNotRight, _⟩
        have headNotLeft : head ∉ actualLeft := by
          intro member
          have impossible := (leftExact head).1 member
          simpa using impossible
        rw [shape, List.count_append]
        simp [List.count_eq_zero.mpr headNotLeft,
          List.count_eq_zero.mpr headNotRight]
      · intro countOne
        have headNotTail : head ∉ tail := by
          intro member
          have positive : 0 < tail.count head :=
            List.count_pos_iff.mpr member
          simp only [Word.toList, List.count_cons_self] at countOne
          omega
        refine ⟨[], tail, rfl, ?_, headNotTail, ?_⟩
        · intro letter
          simp
        · intro letter member
          simp at member

private theorem headCountOne_iff_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_790Invariant.SameComponentFirstSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have rootValid :=
    s4_70_valid_of_sameComponents same.components
  have equalEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation left =
          connectedComponentFour.semigroup.eval valuation right := by
    simpa [Generated.S4_70.table] using rootValid
  have cutIff :=
    connectedComponentFourEqualEval_unaryCut_iff
      left right equalEval [] left.head (by simp)
      (by cases left <;> simp [Word.toList])
      (by simp)
  have rightCutIff :
      connectedComponentFourUnaryCut [] left.head right.toList ↔
        right.toList.count right.head = 1 := by
    rw [same.first]
    exact unaryCut_empty_head_iff_count_one right
  exact
    (unaryCut_empty_head_iff_count_one left).symm.trans <|
      cutIff.trans rightCutIff

private theorem head_not_mem_tail_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  intro member
  have positive : 0 < word.tail.count word.head :=
    List.count_pos_iff.mpr member
  simp only [Word.toList, List.count_cons_self] at countOne
  omega

/-- The deterministic family normal form. A simple global first letter is
left untouched while the suffix is normalized behind it. If it repeats, one
extra initial copy supplies the fixed prefix needed to normalize the whole
`S4_70` component render. -/
def componentFirstNormalList (word : Word Nat) : List Nat :=
  if word.toList.count word.head = 1 then
    word.head ::
      connectedComponentCanonicalRenderList word.tail
  else
    word.head ::
      connectedComponentCanonicalRenderList word.toList

private theorem componentFirstNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_790Invariant.SameComponentFirstSignature left right) :
    componentFirstNormalList left =
      componentFirstNormalList right := by
  have countIff :=
    headCountOne_iff_of_sameSignature same
  have canonicalEqual :
      connectedComponentCanonicalRenderList left.toList =
        connectedComponentCanonicalRenderList right.toList :=
    connectedComponentCanonicalRenderList_eq_of_signature_eq
      same.components
  by_cases leftCount : left.toList.count left.head = 1
  · have rightCount :
        right.toList.count right.head = 1 :=
      countIff.mp leftCount
    have leftSplit :=
      canonicalRenderList_cons_of_head_absent
        left.head left.tail
        (head_not_mem_tail_of_count_one left leftCount)
    have rightSplit :=
      canonicalRenderList_cons_of_head_absent
        right.head right.tail
        (head_not_mem_tail_of_count_one right rightCount)
    simp only [componentFirstNormalList, if_pos leftCount,
      if_pos rightCount]
    exact leftSplit.symm.trans <|
      canonicalEqual.trans rightSplit
  · have rightCount :
        right.toList.count right.head ≠ 1 := by
      intro countOne
      exact leftCount (countIff.mpr countOne)
    simp only [componentFirstNormalList, if_neg leftCount,
      if_neg rightCount]
    rw [same.first, canonicalEqual]

private theorem listDerivesDuplicateInitial
    (head : Nat) {tail : List Nat}
    (headInTail : head ∈ tail) :
    S5_107.ListDerives basis
      (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after
  | cons middleHead middleTail =>
      let middle :=
        S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesLeftDuplication
            (Word.singleton head) middle)
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after

private theorem listDerivesComponentFirstNormal
    (word : Word Nat) :
    S5_107.ListDerives basis
      word.toList (componentFirstNormalList word) := by
  cases word with
  | mk head tail =>
      by_cases countOne :
          (Word.mk head tail).toList.count head = 1
      · rw [componentFirstNormalList, if_pos countOne]
        have tailDerivation :=
          connectedComponentCanonicalRenderList_derives tail
        have lifted :=
          liftConnectedComponentListUnderPrefix
            (Word.singleton head) tailDerivation
        simpa only [Word.toList_singleton,
          List.singleton_append] using lifted
      · rw [componentFirstNormalList, if_neg countOne]
        have headInTail : head ∈ tail := by
          have positive : 0 < tail.count head := by
            simp only [Word.toList,
              List.count_cons_self] at countOne
            omega
          exact List.count_pos_iff.mp positive
        have duplicate :=
          listDerivesDuplicateInitial head headInTail
        have wholeDerivation :=
          connectedComponentCanonicalRenderList_derives
            (Word.mk head tail).toList
        have lifted :=
          liftConnectedComponentListUnderPrefix
            (Word.singleton head) wholeDerivation
        exact duplicate.trans <| by
          simpa only [Word.toList_singleton,
            List.singleton_append] using lifted

/-- Unrestricted syntactic completeness of the ordered component-signature
plus global-first-letter invariant. -/
theorem derives_of_sameComponentFirstSignature
    {left right : Word Nat}
    (same :
      S5_790Invariant.SameComponentFirstSignature left right) :
    Derives basis left right := by
  have leftNormal :=
    listDerivesComponentFirstNormal left
  have rightNormal :=
    listDerivesComponentFirstNormal right
  have normalEqual :=
    componentFirstNormalList_eq_of_sameSignature same
  have middle :
      S5_107.ListDerives basis
        (componentFirstNormalList left)
        (componentFirstNormalList right) := by
    rw [normalEqual]
    exact
      S5_107.ListDerives.refl
        (basis := basis) _
  have listDerivation :
      S5_107.ListDerives basis left.toList right.toList :=
    leftNormal.trans <| middle.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord listDerivation

end SemigroupBasis.CoRoots.S5_790

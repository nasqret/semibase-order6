import SemigroupBasis.Examples.ConnectedComponentFourSemantics

namespace SemigroupBasis.Examples

open SemigroupBasis

private theorem connectedComponentFirst_mem_left
    {first : Nat} {tail left right : List Nat}
    (shape : first :: tail = left ++ right)
    (leftNonempty : left ≠ []) :
    first ∈ left := by
  cases left with
  | nil => contradiction
  | cons leftHead leftTail =>
      change first :: tail = leftHead :: (leftTail ++ right) at shape
      cases shape
      exact List.Mem.head _

private theorem connectedComponentLast_mem_right
    {last : Nat} {body left right : List Nat}
    (shape : body ++ [last] = left ++ right)
    (rightNonempty : right ≠ []) :
    last ∈ right := by
  have reversed :
      last :: body.reverse = right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have rightReverseNonempty : right.reverse ≠ [] := by
    simpa using rightNonempty
  have member :=
    connectedComponentFirst_mem_left reversed rightReverseNonempty
  simpa using member

/-- Every valid canonical component render is support-connected. -/
theorem connectedComponentRenderSignature_supportConnected
    {signature : connectedComponentSignature}
    (valid : connectedComponentSignatureValid signature) :
    ConnectedComponentSupportConnected
      (connectedComponentRenderSignature signature) := by
  cases signature with
  | mk support repeatedUnary =>
      cases support with
      | nil =>
          exact False.elim (valid.1 rfl)
      | cons first remaining =>
          cases remaining with
          | nil =>
              cases repeatedUnary with
              | false =>
                  intro left right shape leftNonempty rightNonempty
                  have lengths := congrArg List.length shape
                  have leftPositive :=
                    List.length_pos_iff.mpr leftNonempty
                  have rightPositive :=
                    List.length_pos_iff.mpr rightNonempty
                  simp [connectedComponentRenderSignature] at lengths
                  omega
              | true =>
                  intro left right shape leftNonempty rightNonempty
                  have lengths := congrArg List.length shape
                  have leftPositive :=
                    List.length_pos_iff.mpr leftNonempty
                  have rightPositive :=
                    List.length_pos_iff.mpr rightNonempty
                  have leftLength : left.length = 1 := by
                    simp [connectedComponentRenderSignature] at lengths
                    omega
                  have rightLength : right.length = 1 := by
                    simp [connectedComponentRenderSignature] at lengths
                    omega
                  rcases List.length_eq_one_iff.mp leftLength with
                    ⟨leftHead, rfl⟩
                  rcases List.length_eq_one_iff.mp rightLength with
                    ⟨rightHead, rfl⟩
                  have shape' : [first, first] = [leftHead, rightHead] := by
                    simpa [connectedComponentRenderSignature] using shape
                  cases shape'
                  exact ⟨first, by simp, by simp⟩
          | cons next rest =>
              intro left right shape leftNonempty rightNonempty
              refine ⟨first, ?_, ?_⟩
              · apply connectedComponentFirst_mem_left
                  shape leftNonempty
              · apply connectedComponentLast_mem_right
                  shape rightNonempty

theorem connectedComponentRenderSignatures_nonempty
    {signatures : List connectedComponentSignature}
    (valid :
      ∀ signature, signature ∈ signatures →
        connectedComponentSignatureValid signature)
    (nonempty : signatures ≠ []) :
    connectedComponentRenderSignatures signatures ≠ [] := by
  rcases List.exists_cons_of_ne_nil nonempty with
    ⟨first, rest, rfl⟩
  intro renderedEmpty
  have firstNonempty :=
    connectedComponentRenderSignature_nonempty
      (valid first (by simp))
  simp only [connectedComponentRenderSignatures,
    List.flatMap_cons] at renderedEmpty
  exact firstNonempty (List.append_eq_nil_iff.mp renderedEmpty).1

theorem connectedComponentSignatureBlocks_disjoint
    {left right : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures (left ++ right)) :
    ConnectedComponentSupportsDisjoint
      (connectedComponentRenderSignatures left)
      (connectedComponentRenderSignatures right) := by
  have cross :=
    (List.pairwise_append.mp canonical.2).2.2
  intro letter leftMember rightMember
  simp only [connectedComponentRenderSignatures,
    List.mem_flatMap] at leftMember rightMember
  rcases leftMember with
    ⟨leftSignature, leftSignatureMember, leftRenderedMember⟩
  rcases rightMember with
    ⟨rightSignature, rightSignatureMember, rightRenderedMember⟩
  have leftSupportMember :=
    (connectedComponentRenderSignature_mem_iff
      (canonical.1 leftSignature
        (List.mem_append_left right leftSignatureMember)).1
      letter).1 leftRenderedMember
  have rightSupportMember :=
    (connectedComponentRenderSignature_mem_iff
      (canonical.1 rightSignature
        (List.mem_append_right left rightSignatureMember)).1
      letter).1 rightRenderedMember
  exact
    (cross leftSignature leftSignatureMember
      rightSignature rightSignatureMember)
      letter leftSupportMember rightSupportMember

private theorem connectedComponentCanonicalSignatures_left
    {left right : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures (left ++ right)) :
    connectedComponentFourCanonicalSignatures left := by
  exact
    ⟨fun signature member =>
        canonical.1 signature (List.mem_append_left right member),
      (List.pairwise_append.mp canonical.2).1⟩

private theorem connectedComponentCanonicalSignatures_right
    {left right : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures (left ++ right)) :
    connectedComponentFourCanonicalSignatures right := by
  exact
    ⟨fun signature member =>
        canonical.1 signature (List.mem_append_right left member),
      (List.pairwise_append.mp canonical.2).2.1⟩

/-- Every nontrivial support-disjoint cut of a canonical render occurs
between whole component signatures. -/
theorem connectedComponentCanonicalRender_disjointCut
    {signatures : List connectedComponentSignature}
    {leftLetters rightLetters : List Nat}
    (canonical :
      connectedComponentFourCanonicalSignatures signatures)
    (shape :
      connectedComponentRenderSignatures signatures =
        leftLetters ++ rightLetters)
    (leftNonempty : leftLetters ≠ [])
    (rightNonempty : rightLetters ≠ [])
    (disjoint :
      ConnectedComponentSupportsDisjoint leftLetters rightLetters) :
    ∃ leftSignatures rightSignatures,
      signatures = leftSignatures ++ rightSignatures ∧
      leftSignatures ≠ [] ∧
      rightSignatures ≠ [] ∧
      connectedComponentRenderSignatures leftSignatures =
        leftLetters ∧
      connectedComponentRenderSignatures rightSignatures =
        rightLetters := by
  induction signatures generalizing leftLetters rightLetters with
  | nil =>
      simp [connectedComponentRenderSignatures] at shape
      exact False.elim (leftNonempty shape.1)
  | cons first rest ih =>
      have firstValid := canonical.1 first (by simp)
      have restCanonical :
          connectedComponentFourCanonicalSignatures rest := by
        exact
          ⟨fun signature member =>
              canonical.1 signature (List.Mem.tail first member),
            canonical.2.tail⟩
      have firstNonempty :=
        connectedComponentRenderSignature_nonempty firstValid
      change
        connectedComponentRenderSignature first ++
            connectedComponentRenderSignatures rest =
          leftLetters ++ rightLetters at shape
      rcases List.append_eq_append_iff.mp shape with
        afterFirst | beforeFirst
      · rcases afterFirst with
          ⟨afterFirst, leftShape, restShape⟩
        by_cases afterEmpty : afterFirst = []
        · subst afterFirst
          simp only [List.append_nil] at leftShape restShape
          subst leftLetters
          have restNonempty : rest ≠ [] := by
            intro restEmpty
            subst rest
            simp at restShape
            exact rightNonempty restShape.symm
          exact
            ⟨[first], rest, by simp, by simp, restNonempty,
              by simp [connectedComponentRenderSignatures],
              by simpa using restShape⟩
        · have tailDisjoint :
              ConnectedComponentSupportsDisjoint
                afterFirst rightLetters := by
            intro letter afterMember rightMember
            apply disjoint letter
            · rw [leftShape]
              exact List.mem_append_right _ afterMember
            · exact rightMember
          obtain
            ⟨leftTail, rightTail, restSplit,
              leftTailNonempty, rightTailNonempty,
              leftTailRender, rightTailRender⟩ :=
            ih restCanonical restShape afterEmpty rightNonempty
              tailDisjoint
          refine
            ⟨first :: leftTail, rightTail, ?_,
              by simp, rightTailNonempty, ?_, rightTailRender⟩
          · simp [restSplit]
          · change
              connectedComponentRenderSignature first ++
                  connectedComponentRenderSignatures leftTail =
                leftLetters
            rw [leftTailRender, ← leftShape]
      · rcases beforeFirst with
          ⟨beforeEnd, firstShape, rightShape⟩
        by_cases beforeEmpty : beforeEnd = []
        · subst beforeEnd
          simp only [List.append_nil] at firstShape
          simp only [List.nil_append] at rightShape
          subst leftLetters
          have restNonempty : rest ≠ [] := by
            intro restEmpty
            subst rest
            exact rightNonempty <| by
              simpa [connectedComponentRenderSignatures] using rightShape
          exact
            ⟨[first], rest, by simp, by simp, restNonempty,
              by simp [connectedComponentRenderSignatures],
              by simpa using rightShape.symm⟩
        · have crossing :=
            connectedComponentRenderSignature_supportConnected
              firstValid leftLetters beforeEnd firstShape
              leftNonempty beforeEmpty
          rcases crossing with
            ⟨letter, leftMember, beforeMember⟩
          exact False.elim <|
            disjoint letter leftMember <| by
              rw [rightShape]
              exact List.mem_append_left _ beforeMember

/-- Exact prefix-union cuts of canonical renders therefore correspond to a
nonempty proper prefix of the signature list. -/
theorem connectedComponentCanonicalRender_prefixCut
    {signatures : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures signatures)
    (prefixSupport : List Nat)
    (cut :
      connectedComponentFourPrefixUnionCut prefixSupport
        (connectedComponentRenderSignatures signatures)) :
    ∃ leftSignatures rightSignatures,
      signatures = leftSignatures ++ rightSignatures ∧
      leftSignatures ≠ [] ∧
      rightSignatures ≠ [] ∧
      (∀ letter,
        letter ∈ connectedComponentFourSignatureSupport leftSignatures ↔
          letter ∈ prefixSupport) := by
  rcases cut with
    ⟨leftLetters, rightLetters, shape,
      leftNonempty, rightNonempty, leftExact, disjoint⟩
  obtain
    ⟨leftSignatures, rightSignatures, signatureShape,
      leftSignaturesNonempty, rightSignaturesNonempty,
      leftRender, _⟩ :=
    connectedComponentCanonicalRender_disjointCut
      canonical shape leftNonempty rightNonempty disjoint
  refine
    ⟨leftSignatures, rightSignatures, signatureShape,
      leftSignaturesNonempty, rightSignaturesNonempty, ?_⟩
  intro letter
  have leftCanonical :=
    connectedComponentCanonicalSignatures_left
      (signatureShape ▸ canonical)
  have renderSupport :=
    connectedComponentFourRenderSignatures_mem_iff
      leftCanonical.1 letter
  rw [leftRender] at renderSupport
  exact renderSupport.symm.trans (leftExact letter)

/-- A canonical signature is determined by its support and, in the unary
case, by whether its render is the one-letter component. -/
private theorem connectedComponentSignature_eq_of_support
    {left right : connectedComponentSignature}
    (leftValid : connectedComponentSignatureValid left)
    (rightValid : connectedComponentSignatureValid right)
    (supportEqual : left.support = right.support)
    (unarySimpleEqual :
      left.support.length = 1 →
        (left.repeatedUnary = false ↔ right.repeatedUnary = false)) :
    left = right := by
  cases left with
  | mk leftSupport leftRepeated =>
      cases right with
      | mk rightSupport rightRepeated =>
          simp only at supportEqual leftValid rightValid unarySimpleEqual
          subst rightSupport
          congr
          by_cases unary : leftSupport.length = 1
          · have repeatedIff := unarySimpleEqual unary
            cases leftRepeated <;> cases rightRepeated <;>
              simp_all
          · have leftFalse := leftValid.2.2.2 unary
            have rightFalse := rightValid.2.2.2 unary
            simp_all

private theorem connectedComponentCanonicalSignatures_prefix
    {prefixSignatures suffix : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures
        (prefixSignatures ++ suffix)) :
    connectedComponentFourCanonicalSignatures prefixSignatures :=
  connectedComponentCanonicalSignatures_left canonical

private theorem connectedComponentSignatureSupport_disjoint
    {left right : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures (left ++ right)) :
    ConnectedComponentSupportsDisjoint
      (connectedComponentFourSignatureSupport left)
      (connectedComponentFourSignatureSupport right) := by
  intro letter leftMember rightMember
  simp only [connectedComponentFourSignatureSupport,
    List.mem_flatMap] at leftMember rightMember
  rcases leftMember with
    ⟨leftSignature, leftSignatureMember, leftSupportMember⟩
  rcases rightMember with
    ⟨rightSignature, rightSignatureMember, rightSupportMember⟩
  exact
    ((List.pairwise_append.mp canonical.2).2.2
      leftSignature leftSignatureMember
      rightSignature rightSignatureMember)
      letter leftSupportMember rightSupportMember

private theorem connectedComponentSignatureSupport_nonempty
    {signatures : List connectedComponentSignature}
    (valid :
      ∀ signature, signature ∈ signatures →
        connectedComponentSignatureValid signature)
    (nonempty : signatures ≠ []) :
    connectedComponentFourSignatureSupport signatures ≠ [] := by
  rcases List.exists_cons_of_ne_nil nonempty with
    ⟨first, rest, rfl⟩
  have firstNonempty := (valid first (by simp)).1
  intro supportEmpty
  simp only [connectedComponentFourSignatureSupport,
    List.flatMap_cons] at supportEmpty
  exact firstNonempty (List.append_eq_nil_iff.mp supportEmpty).1

/-- Prefixes of one canonical signature list are ordered by inclusion of
their support unions. -/
private theorem connectedComponentCanonicalPrefixes_compare
    {full firstPrefix firstSuffix secondPrefix secondSuffix :
      List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures full)
    (firstSplit : full = firstPrefix ++ firstSuffix)
    (secondSplit : full = secondPrefix ++ secondSuffix)
    (supportSubset :
      ∀ letter,
        letter ∈ connectedComponentFourSignatureSupport firstPrefix →
          letter ∈ connectedComponentFourSignatureSupport secondPrefix) :
    ∃ extra, secondPrefix = firstPrefix ++ extra := by
  have prefixEquality :
      firstPrefix ++ firstSuffix =
        secondPrefix ++ secondSuffix :=
    firstSplit.symm.trans secondSplit
  rcases List.append_eq_append_iff.mp prefixEquality with
    firstShorter | secondShorter
  · rcases firstShorter with ⟨extra, secondPrefixShape, _⟩
    exact ⟨extra, secondPrefixShape⟩
  · rcases secondShorter with
      ⟨extra, firstPrefixShape, _⟩
    by_cases extraEmpty : extra = []
    · subst extra
      exact ⟨[], by simpa using firstPrefixShape.symm⟩
    · have prefixCanonical :
          connectedComponentFourCanonicalSignatures
            (secondPrefix ++ extra) := by
        apply connectedComponentCanonicalSignatures_prefix
        rw [← firstPrefixShape, ← firstSplit]
        exact canonical
      have extraSupportNonempty :
          connectedComponentFourSignatureSupport extra ≠ [] :=
        connectedComponentSignatureSupport_nonempty
          (connectedComponentCanonicalSignatures_right
            prefixCanonical).1 extraEmpty
      obtain ⟨letter, letterExtra⟩ :=
        List.exists_mem_of_ne_nil
          (connectedComponentFourSignatureSupport extra)
          extraSupportNonempty
      have letterFirst :
          letter ∈
            connectedComponentFourSignatureSupport firstPrefix := by
        rw [firstPrefixShape,
          connectedComponentFourSignatureSupport_append]
        exact List.mem_append_right _ letterExtra
      have letterSecond := supportSubset letter letterFirst
      exact False.elim <|
        (connectedComponentSignatureSupport_disjoint
          prefixCanonical)
          letter letterSecond letterExtra

/-- A strict support extension of a common canonical prefix must include the
next component. -/
private theorem connectedComponentCanonicalCut_includes_next
    {common : List connectedComponentSignature}
    {next : connectedComponentSignature}
    {rest cutPrefix cutSuffix : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures
        (common ++ next :: rest))
    (cutSplit :
      common ++ next :: rest = cutPrefix ++ cutSuffix)
    (commonSubset :
      ∀ letter,
        letter ∈ connectedComponentFourSignatureSupport common →
          letter ∈ connectedComponentFourSignatureSupport cutPrefix)
    (strict :
      ∃ letter,
        letter ∈ connectedComponentFourSignatureSupport cutPrefix ∧
          letter ∉ connectedComponentFourSignatureSupport common) :
    next.support ⊆ connectedComponentFourSignatureSupport cutPrefix := by
  obtain ⟨extra, cutPrefixShape⟩ :=
    connectedComponentCanonicalPrefixes_compare
      canonical rfl cutSplit commonSubset
  have extraNonempty : extra ≠ [] := by
    intro extraEmpty
    subst extra
    simp only [List.append_nil] at cutPrefixShape
    rcases strict with ⟨letter, cutMember, commonAbsent⟩
    exact commonAbsent <| by
      rwa [cutPrefixShape] at cutMember
  have tailEquality :
      next :: rest = extra ++ cutSuffix := by
    simpa [cutPrefixShape, List.append_assoc] using cutSplit
  rcases List.exists_cons_of_ne_nil extraNonempty with
    ⟨extraHead, extraTail, extraShape⟩
  subst extra
  simp only [List.cons_append] at tailEquality
  have headEqual : next = extraHead := by
    exact (List.cons.inj tailEquality).1
  subst extraHead
  intro letter member
  rw [cutPrefixShape,
    connectedComponentFourSignatureSupport_append]
  apply List.mem_append_right
  simp [connectedComponentFourSignatureSupport, member]

/-- Every nontrivial split of a canonical signature list gives the exact
prefix-support cut displayed by that split. -/
theorem connectedComponentCanonicalRender_prefixCut_of_split
    {left right : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures (left ++ right))
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    connectedComponentFourPrefixUnionCut
      (connectedComponentFourSignatureSupport left)
      (connectedComponentRenderSignatures (left ++ right)) := by
  have leftCanonical :=
    connectedComponentCanonicalSignatures_left canonical
  have rightCanonical :=
    connectedComponentCanonicalSignatures_right canonical
  refine
    ⟨connectedComponentRenderSignatures left,
      connectedComponentRenderSignatures right,
      connectedComponentFourRenderSignatures_append left right,
      connectedComponentRenderSignatures_nonempty
        leftCanonical.1 leftNonempty,
      connectedComponentRenderSignatures_nonempty
        rightCanonical.1 rightNonempty,
      ?_, connectedComponentSignatureBlocks_disjoint canonical⟩
  intro letter
  exact
    connectedComponentFourRenderSignatures_mem_iff
      leftCanonical.1 letter

private theorem connectedComponentPrefixUnionCut_covered
    {prefixSupport letters : List Nat}
    (cut :
      connectedComponentFourPrefixUnionCut prefixSupport letters) :
    ∀ letter, letter ∈ prefixSupport → letter ∈ letters := by
  rcases cut with
    ⟨actualLeft, actualRight, shape, _, _, leftExact, _⟩
  intro letter prefixMember
  rw [shape]
  exact
    List.mem_append_left actualRight <|
      (leftExact letter).2 prefixMember

private theorem connectedComponentUnaryCut_testedOccurs
    {prefixSupport letters : List Nat} {tested : Nat}
    (cut :
      connectedComponentFourUnaryCut prefixSupport tested letters) :
    tested ∈ letters := by
  rcases cut with
    ⟨actualLeft, actualRight, shape, _, _, _⟩
  rw [shape]
  exact List.mem_append_right actualLeft (List.Mem.head _)

private theorem connectedComponentUnaryCut_covered
    {prefixSupport letters : List Nat} {tested : Nat}
    (cut :
      connectedComponentFourUnaryCut prefixSupport tested letters) :
    ∀ letter, letter ∈ prefixSupport → letter ∈ letters := by
  rcases cut with
    ⟨actualLeft, actualRight, shape, leftExact, _, _⟩
  intro letter prefixMember
  rw [shape]
  exact
    List.mem_append_left (tested :: actualRight) <|
      (leftExact letter).2 prefixMember

/-- The semantic information used to compare two canonical S4_70 renders:
global support, all exact prefix-support cuts, and all exact unary cuts. -/
def ConnectedComponentCanonicalSameSignature
    (left right : List connectedComponentSignature) : Prop :=
  (∀ tested,
      tested ∈ connectedComponentFourSignatureSupport left ↔
        tested ∈ connectedComponentFourSignatureSupport right) ∧
    (∀ prefixSupport,
      connectedComponentFourPrefixUnionCut prefixSupport
          (connectedComponentRenderSignatures left) ↔
        connectedComponentFourPrefixUnionCut prefixSupport
          (connectedComponentRenderSignatures right)) ∧
    (∀ prefixSupport tested,
      tested ∉ prefixSupport →
        (connectedComponentFourUnaryCut prefixSupport tested
            (connectedComponentRenderSignatures left) ↔
          connectedComponentFourUnaryCut prefixSupport tested
            (connectedComponentRenderSignatures right)))

theorem ConnectedComponentCanonicalSameSignature.symm
    {left right : List connectedComponentSignature}
    (same : ConnectedComponentCanonicalSameSignature left right) :
    ConnectedComponentCanonicalSameSignature right left :=
  ⟨fun tested => (same.1 tested).symm,
    fun prefixSupport => (same.2.1 prefixSupport).symm,
    fun prefixSupport tested testedNotPrefix =>
      (same.2.2 prefixSupport tested testedNotPrefix).symm⟩

/-- Equal S4_70 term functions induce the same canonical semantic
signature. -/
theorem connectedComponentCanonicalSameSignature_of_equalEval
    {left right : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures left)
    (rightCanonical :
      connectedComponentFourCanonicalSignatures right)
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = connectedComponentRenderSignatures left)
    (rightRendered :
      rightWord.toList = connectedComponentRenderSignatures right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation leftWord =
          connectedComponentFour.semigroup.eval valuation rightWord) :
    ConnectedComponentCanonicalSameSignature left right := by
  have supportEqual :
      ∀ tested,
        tested ∈ connectedComponentFourSignatureSupport left ↔
          tested ∈ connectedComponentFourSignatureSupport right := by
    intro tested
    have wordSupport :=
      connectedComponentFourEqualEval_support_iff
        leftWord rightWord equalEval tested
    rw [leftRendered, rightRendered,
      connectedComponentFourRenderSignatures_mem_iff
        leftCanonical.1 tested,
      connectedComponentFourRenderSignatures_mem_iff
        rightCanonical.1 tested] at wordSupport
    exact wordSupport
  have prefixCuts :
      ∀ prefixSupport,
        connectedComponentFourPrefixUnionCut prefixSupport
            (connectedComponentRenderSignatures left) ↔
          connectedComponentFourPrefixUnionCut prefixSupport
            (connectedComponentRenderSignatures right) := by
    intro prefixSupport
    constructor
    · intro leftCut
      have covered :
          ∀ letter, letter ∈ prefixSupport →
            letter ∈ leftWord.toList := by
        intro letter prefixMember
        rw [leftRendered]
        exact
          connectedComponentPrefixUnionCut_covered
            leftCut letter prefixMember
      have preserved :=
        connectedComponentFourEqualEval_prefixUnionCut_iff
          leftWord rightWord equalEval prefixSupport covered
      rw [leftRendered, rightRendered] at preserved
      exact preserved.1 leftCut
    · intro rightCut
      have covered :
          ∀ letter, letter ∈ prefixSupport →
            letter ∈ leftWord.toList := by
        intro letter prefixMember
        apply
          (connectedComponentFourEqualEval_support_iff
            leftWord rightWord equalEval letter).2
        rw [rightRendered]
        exact
          connectedComponentPrefixUnionCut_covered
            rightCut letter prefixMember
      have preserved :=
        connectedComponentFourEqualEval_prefixUnionCut_iff
          leftWord rightWord equalEval prefixSupport covered
      rw [leftRendered, rightRendered] at preserved
      exact preserved.2 rightCut
  have unaryCuts :
      ∀ prefixSupport tested,
        tested ∉ prefixSupport →
          (connectedComponentFourUnaryCut prefixSupport tested
              (connectedComponentRenderSignatures left) ↔
            connectedComponentFourUnaryCut prefixSupport tested
              (connectedComponentRenderSignatures right)) := by
    intro prefixSupport tested testedNotPrefix
    constructor
    · intro leftCut
      have testedOccurs : tested ∈ leftWord.toList := by
        rw [leftRendered]
        exact connectedComponentUnaryCut_testedOccurs leftCut
      have covered :
          ∀ letter, letter ∈ prefixSupport →
            letter ∈ leftWord.toList := by
        intro letter prefixMember
        rw [leftRendered]
        exact
          connectedComponentUnaryCut_covered
            leftCut letter prefixMember
      have preserved :=
        connectedComponentFourEqualEval_unaryCut_iff
          leftWord rightWord equalEval prefixSupport tested
          testedNotPrefix testedOccurs covered
      rw [leftRendered, rightRendered] at preserved
      exact preserved.1 leftCut
    · intro rightCut
      have testedOccurs : tested ∈ leftWord.toList := by
        apply
          (connectedComponentFourEqualEval_support_iff
            leftWord rightWord equalEval tested).2
        rw [rightRendered]
        exact connectedComponentUnaryCut_testedOccurs rightCut
      have covered :
          ∀ letter, letter ∈ prefixSupport →
            letter ∈ leftWord.toList := by
        intro letter prefixMember
        apply
          (connectedComponentFourEqualEval_support_iff
            leftWord rightWord equalEval letter).2
        rw [rightRendered]
        exact
          connectedComponentUnaryCut_covered
            rightCut letter prefixMember
      have preserved :=
        connectedComponentFourEqualEval_unaryCut_iff
          leftWord rightWord equalEval prefixSupport tested
          testedNotPrefix testedOccurs covered
      rw [leftRendered, rightRendered] at preserved
      exact preserved.2 rightCut
  exact ⟨supportEqual, prefixCuts, unaryCuts⟩

/-- Semantic characterization of the support of the component immediately
after `common`: it is the part of the total support outside `common` that is
contained in every strict exact prefix extension of `common`. -/
def ConnectedComponentNextSupportSemantic
    (common full : List connectedComponentSignature)
    (tested : Nat) : Prop :=
  tested ∈ connectedComponentFourSignatureSupport full ∧
    tested ∉ connectedComponentFourSignatureSupport common ∧
    ∀ prefixSupport,
      connectedComponentFourPrefixUnionCut prefixSupport
          (connectedComponentRenderSignatures full) →
      (∀ letter,
        letter ∈ connectedComponentFourSignatureSupport common →
          letter ∈ prefixSupport) →
      (∃ letter,
        letter ∈ prefixSupport ∧
          letter ∉ connectedComponentFourSignatureSupport common) →
      tested ∈ prefixSupport

theorem connectedComponentNextSupportSemantic_iff
    {common : List connectedComponentSignature}
    {next : connectedComponentSignature}
    {rest : List connectedComponentSignature}
    (canonical :
      connectedComponentFourCanonicalSignatures
        (common ++ next :: rest))
    (tested : Nat) :
    tested ∈ next.support ↔
      ConnectedComponentNextSupportSemantic
        common (common ++ next :: rest) tested := by
  constructor
  · intro nextMember
    have commonTailDisjoint :
        ConnectedComponentSupportsDisjoint
          (connectedComponentFourSignatureSupport common)
          (connectedComponentFourSignatureSupport (next :: rest)) :=
      connectedComponentSignatureSupport_disjoint canonical
    refine ⟨?_, ?_, ?_⟩
    · rw [connectedComponentFourSignatureSupport_append]
      exact List.mem_append_right _ <| by
        simp [connectedComponentFourSignatureSupport, nextMember]
    · intro commonMember
      exact
        commonTailDisjoint tested commonMember <| by
          simp [connectedComponentFourSignatureSupport, nextMember]
    · intro prefixSupport cut commonSubset strict
      obtain
        ⟨cutPrefix, cutSuffix, cutSplit, _, _, cutExact⟩ :=
        connectedComponentCanonicalRender_prefixCut
          canonical prefixSupport cut
      have commonCutSubset :
          ∀ letter,
            letter ∈ connectedComponentFourSignatureSupport common →
              letter ∈ connectedComponentFourSignatureSupport cutPrefix := by
        intro letter commonMember
        exact
          (cutExact letter).2 (commonSubset letter commonMember)
      have cutStrict :
          ∃ letter,
            letter ∈ connectedComponentFourSignatureSupport cutPrefix ∧
              letter ∉ connectedComponentFourSignatureSupport common := by
        rcases strict with
          ⟨letter, prefixMember, commonAbsent⟩
        exact ⟨letter, (cutExact letter).2 prefixMember, commonAbsent⟩
      exact
        (cutExact tested).1 <|
          connectedComponentCanonicalCut_includes_next
            canonical cutSplit commonCutSubset cutStrict nextMember
  · intro semantic
    rcases semantic with
      ⟨totalMember, commonAbsent, everyStrictCut⟩
    by_cases restEmpty : rest = []
    · subst rest
      rw [connectedComponentFourSignatureSupport_append] at totalMember
      rcases List.mem_append.mp totalMember with
        commonMember | tailMember
      · exact False.elim (commonAbsent commonMember)
      · simpa [connectedComponentFourSignatureSupport] using tailMember
    · have splitCanonical :
          connectedComponentFourCanonicalSignatures
            ((common ++ [next]) ++ rest) := by
        simpa [List.append_assoc] using canonical
      have prefixCut :
          connectedComponentFourPrefixUnionCut
            (connectedComponentFourSignatureSupport
              (common ++ [next]))
            (connectedComponentRenderSignatures
              (common ++ next :: rest)) := by
        have cut :=
          connectedComponentCanonicalRender_prefixCut_of_split
            splitCanonical (by simp) restEmpty
        simpa [List.append_assoc] using cut
      have commonSubset :
          ∀ letter,
            letter ∈ connectedComponentFourSignatureSupport common →
              letter ∈ connectedComponentFourSignatureSupport
                (common ++ [next]) := by
        intro letter commonMember
        rw [connectedComponentFourSignatureSupport_append]
        exact List.mem_append_left _ commonMember
      have nextValid :
          connectedComponentSignatureValid next :=
        canonical.1 next <| by simp
      obtain ⟨witness, witnessMember⟩ :=
        List.exists_mem_of_ne_nil next.support nextValid.1
      have commonNextDisjoint :
          ConnectedComponentSupportsDisjoint
            (connectedComponentFourSignatureSupport common)
            (connectedComponentFourSignatureSupport [next]) :=
        connectedComponentSignatureSupport_disjoint <| by
          simpa using
            connectedComponentCanonicalSignatures_prefix splitCanonical
      have strict :
          ∃ letter,
            letter ∈ connectedComponentFourSignatureSupport
                (common ++ [next]) ∧
              letter ∉ connectedComponentFourSignatureSupport common := by
        refine ⟨witness, ?_, ?_⟩
        · rw [connectedComponentFourSignatureSupport_append]
          exact List.mem_append_right _ <| by
            simpa [connectedComponentFourSignatureSupport]
        · intro commonMember
          exact
            commonNextDisjoint witness commonMember <| by
              simpa [connectedComponentFourSignatureSupport]
      have testedInPrefix :=
        everyStrictCut
          (connectedComponentFourSignatureSupport (common ++ [next]))
          prefixCut commonSubset strict
      rw [connectedComponentFourSignatureSupport_append] at testedInPrefix
      rcases List.mem_append.mp testedInPrefix with
        commonMember | nextMember
      · exact False.elim (commonAbsent commonMember)
      · simpa [connectedComponentFourSignatureSupport] using nextMember

theorem ConnectedComponentCanonicalSameSignature.nextSupportSemantic_iff
    {left right : List connectedComponentSignature}
    (same : ConnectedComponentCanonicalSameSignature left right)
    (common : List connectedComponentSignature)
    (tested : Nat) :
    ConnectedComponentNextSupportSemantic common left tested ↔
      ConnectedComponentNextSupportSemantic common right tested := by
  constructor
  · rintro ⟨totalMember, commonAbsent, everyStrictCut⟩
    refine ⟨(same.1 tested).1 totalMember, commonAbsent, ?_⟩
    intro prefixSupport rightCut commonSubset strict
    exact
      everyStrictCut prefixSupport
        ((same.2.1 prefixSupport).2 rightCut)
        commonSubset strict
  · rintro ⟨totalMember, commonAbsent, everyStrictCut⟩
    refine ⟨(same.1 tested).2 totalMember, commonAbsent, ?_⟩
    intro prefixSupport leftCut commonSubset strict
    exact
      everyStrictCut prefixSupport
        ((same.2.1 prefixSupport).1 leftCut)
        commonSubset strict

/-- In a canonical render, an exact unary cut after `common` detects exactly
the one-letter version of a singleton-support component. -/
theorem connectedComponentCanonicalUnaryCut_iff
    {common : List connectedComponentSignature}
    {current : connectedComponentSignature}
    {rest : List connectedComponentSignature}
    {tested : Nat}
    (canonical :
      connectedComponentFourCanonicalSignatures
        (common ++ current :: rest))
    (supportShape : current.support = [tested]) :
    connectedComponentFourUnaryCut
        (connectedComponentFourSignatureSupport common) tested
        (connectedComponentRenderSignatures
          (common ++ current :: rest)) ↔
      current.repeatedUnary = false := by
  have currentValid :
      connectedComponentSignatureValid current :=
    canonical.1 current <| by simp
  have commonCanonical :=
    connectedComponentCanonicalSignatures_left canonical
  have currentRestCanonical :
      connectedComponentFourCanonicalSignatures
        (current :: rest) := by
    simpa using
      connectedComponentCanonicalSignatures_right canonical
  have testedCurrentSupport : tested ∈ current.support := by
    rw [supportShape]
    simp
  have commonTailSupportDisjoint :
      ConnectedComponentSupportsDisjoint
        (connectedComponentFourSignatureSupport common)
        (connectedComponentFourSignatureSupport (current :: rest)) :=
    connectedComponentSignatureSupport_disjoint canonical
  have testedNotCommon :
      tested ∉ connectedComponentFourSignatureSupport common := by
    intro commonMember
    exact
      commonTailSupportDisjoint tested commonMember <| by
        simp [connectedComponentFourSignatureSupport,
          testedCurrentSupport]
  have fullRender :
      connectedComponentRenderSignatures
          (common ++ current :: rest) =
        connectedComponentRenderSignatures common ++
          connectedComponentRenderSignature current ++
            connectedComponentRenderSignatures rest := by
    simp [connectedComponentRenderSignatures, List.append_assoc]
  constructor
  · intro cut
    cases repeatedValue : current.repeatedUnary with
    | false => rfl
    | true =>
        exfalso
        have repeatedRender :
            connectedComponentRenderSignature current =
              [tested, tested] := by
          simp [connectedComponentRenderSignature,
            supportShape, repeatedValue]
        rcases cut with
          ⟨actualLeft, actualRight, cutShape,
            leftExact, testedNotRight, _⟩
        have testedNotLeft : tested ∉ actualLeft := by
          intro testedLeft
          exact testedNotCommon ((leftExact tested).1 testedLeft)
        have leftCountZero :
            List.count tested actualLeft = 0 :=
          List.count_eq_zero.mpr testedNotLeft
        have rightCountZero :
            List.count tested actualRight = 0 :=
          List.count_eq_zero.mpr testedNotRight
        have countEquality :=
          congrArg (List.count tested) cutShape
        rw [fullRender, repeatedRender] at countEquality
        simp [List.count_append, leftCountZero,
          rightCountZero] at countEquality
        omega
  · intro repeatedFalse
    have simpleRender :
        connectedComponentRenderSignature current = [tested] := by
      simp [connectedComponentRenderSignature,
        supportShape, repeatedFalse]
    have currentRestDisjoint :
        ConnectedComponentSupportsDisjoint
          (connectedComponentRenderSignatures [current])
          (connectedComponentRenderSignatures rest) := by
      have canonicalSplit :
          connectedComponentFourCanonicalSignatures
            ([current] ++ rest) := by
        simpa using currentRestCanonical
      exact connectedComponentSignatureBlocks_disjoint canonicalSplit
    have testedNotRest :
        tested ∉ connectedComponentRenderSignatures rest := by
      intro testedRest
      exact
        currentRestDisjoint tested
          (by simp [connectedComponentRenderSignatures, simpleRender])
          testedRest
    have commonRestDisjoint :
        ∀ letter,
          letter ∈ connectedComponentRenderSignatures common →
            letter ∉ connectedComponentRenderSignatures rest := by
      have commonTailDisjoint :=
        connectedComponentSignatureBlocks_disjoint canonical
      intro letter commonMember restMember
      exact
        commonTailDisjoint letter commonMember <| by
          simp only [connectedComponentRenderSignatures,
            List.flatMap_cons, List.mem_append]
          exact Or.inr restMember
    refine
      ⟨connectedComponentRenderSignatures common,
        connectedComponentRenderSignatures rest,
        ?_, ?_, testedNotRest, commonRestDisjoint⟩
    · rw [fullRender, simpleRender]
      simp [List.append_assoc]
    · intro letter
      exact
        connectedComponentFourRenderSignatures_mem_iff
          commonCanonical.1 letter

private theorem connectedComponentSortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameSupport head).2 (by simp)
          contradiction
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameSupport leftHead).1 (by simp)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameSupport leftHead).1 (by simp)
          have rightHeadInLeft :=
            (sameSupport rightHead).2 (by simp)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightSorted tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by
            omega
          subst rightHead
          congr 1
          apply ih leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameSupport letter

private theorem connectedComponentCanonicalNext_support_eq
    {common : List connectedComponentSignature}
    {leftNext rightNext : connectedComponentSignature}
    {leftRest rightRest : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures
        (common ++ leftNext :: leftRest))
    (rightCanonical :
      connectedComponentFourCanonicalSignatures
        (common ++ rightNext :: rightRest))
    (same :
      ConnectedComponentCanonicalSameSignature
        (common ++ leftNext :: leftRest)
        (common ++ rightNext :: rightRest)) :
    leftNext.support = rightNext.support := by
  have leftValid :
      connectedComponentSignatureValid leftNext :=
    leftCanonical.1 leftNext <| by simp
  have rightValid :
      connectedComponentSignatureValid rightNext :=
    rightCanonical.1 rightNext <| by simp
  apply connectedComponentSortedNodup_eq_of_mem_iff
    leftValid.2.2.1 rightValid.2.2.1
    leftValid.2.1 rightValid.2.1
  intro tested
  rw [connectedComponentNextSupportSemantic_iff
        leftCanonical tested,
      connectedComponentNextSupportSemantic_iff
        rightCanonical tested]
  exact same.nextSupportSemantic_iff common tested

private theorem connectedComponentCanonicalNext_eq
    {common : List connectedComponentSignature}
    {leftNext rightNext : connectedComponentSignature}
    {leftRest rightRest : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures
        (common ++ leftNext :: leftRest))
    (rightCanonical :
      connectedComponentFourCanonicalSignatures
        (common ++ rightNext :: rightRest))
    (same :
      ConnectedComponentCanonicalSameSignature
        (common ++ leftNext :: leftRest)
        (common ++ rightNext :: rightRest)) :
    leftNext = rightNext := by
  have leftValid :
      connectedComponentSignatureValid leftNext :=
    leftCanonical.1 leftNext <| by simp
  have rightValid :
      connectedComponentSignatureValid rightNext :=
    rightCanonical.1 rightNext <| by simp
  have supportEqual :=
    connectedComponentCanonicalNext_support_eq
      leftCanonical rightCanonical same
  apply connectedComponentSignature_eq_of_support
    leftValid rightValid supportEqual
  intro unaryLength
  obtain ⟨tested, supportShape⟩ :=
    List.length_eq_one_iff.mp unaryLength
  have rightSupportShape : rightNext.support = [tested] := by
    rw [← supportEqual, supportShape]
  have testedNotCommon :
      tested ∉ connectedComponentFourSignatureSupport common := by
    have disjoint :=
      connectedComponentSignatureSupport_disjoint leftCanonical
    intro commonMember
    exact
      disjoint tested commonMember <| by
        simp [connectedComponentFourSignatureSupport, supportShape]
  have cutEqual :=
    same.2.2
      (connectedComponentFourSignatureSupport common)
      tested testedNotCommon
  have leftDetected :=
    connectedComponentCanonicalUnaryCut_iff
      leftCanonical supportShape
  have rightDetected :=
    connectedComponentCanonicalUnaryCut_iff
      rightCanonical rightSupportShape
  constructor
  · intro leftSimple
    exact
      rightDetected.1 <|
        cutEqual.1 (leftDetected.2 leftSimple)
  · intro rightSimple
    exact
      leftDetected.1 <|
        cutEqual.2 (rightDetected.2 rightSimple)

private theorem connectedComponentCanonicalTails_eq
    {common left right : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures (common ++ left))
    (rightCanonical :
      connectedComponentFourCanonicalSignatures (common ++ right))
    (same :
      ConnectedComponentCanonicalSameSignature
        (common ++ left) (common ++ right)) :
    left = right := by
  induction left generalizing common right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightNext rightRest =>
          have rightValid :
              connectedComponentSignatureValid rightNext :=
            rightCanonical.1 rightNext <| by simp
          obtain ⟨tested, testedMember⟩ :=
            List.exists_mem_of_ne_nil
              rightNext.support rightValid.1
          have rightTotalMember :
              tested ∈
                connectedComponentFourSignatureSupport
                  (common ++ rightNext :: rightRest) := by
            rw [connectedComponentFourSignatureSupport_append]
            exact List.mem_append_right _ <| by
              simp [connectedComponentFourSignatureSupport,
                testedMember]
          have commonMember :
              tested ∈
                connectedComponentFourSignatureSupport common := by
            have leftTotalMember :=
              (same.1 tested).2 rightTotalMember
            simpa using leftTotalMember
          have disjoint :=
            connectedComponentSignatureSupport_disjoint rightCanonical
          exact False.elim <|
            disjoint tested commonMember <| by
              simp [connectedComponentFourSignatureSupport,
                testedMember]
  | cons leftNext leftRest ih =>
      cases right with
      | nil =>
          have leftValid :
              connectedComponentSignatureValid leftNext :=
            leftCanonical.1 leftNext <| by simp
          obtain ⟨tested, testedMember⟩ :=
            List.exists_mem_of_ne_nil
              leftNext.support leftValid.1
          have leftTotalMember :
              tested ∈
                connectedComponentFourSignatureSupport
                  (common ++ leftNext :: leftRest) := by
            rw [connectedComponentFourSignatureSupport_append]
            exact List.mem_append_right _ <| by
              simp [connectedComponentFourSignatureSupport,
                testedMember]
          have commonMember :
              tested ∈
                connectedComponentFourSignatureSupport common := by
            have rightTotalMember :=
              (same.1 tested).1 leftTotalMember
            simpa using rightTotalMember
          have disjoint :=
            connectedComponentSignatureSupport_disjoint leftCanonical
          exact False.elim <|
            disjoint tested commonMember <| by
              simp [connectedComponentFourSignatureSupport,
                testedMember]
      | cons rightNext rightRest =>
          have nextEqual :=
            connectedComponentCanonicalNext_eq
              leftCanonical rightCanonical same
          subst rightNext
          congr 1
          apply ih
            (common := common ++ [leftNext])
            (right := rightRest)
          · simpa [List.append_assoc] using leftCanonical
          · simpa [List.append_assoc] using rightCanonical
          · simpa [List.append_assoc] using same

/-- Canonical S4_70 signature lists are injective with respect to their
semantic signature. -/
theorem connectedComponentCanonical_eq_of_sameSignature
    {left right : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures left)
    (rightCanonical :
      connectedComponentFourCanonicalSignatures right)
    (same : ConnectedComponentCanonicalSameSignature left right) :
    left = right := by
  apply connectedComponentCanonicalTails_eq
    (common := [])
  · simpa using leftCanonical
  · simpa using rightCanonical
  · simpa using same

/-- Public semantic injectivity theorem for canonical S4_70 renders. -/
theorem connectedComponentCanonical_eq_of_equalEval
    {left right : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures left)
    (rightCanonical :
      connectedComponentFourCanonicalSignatures right)
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = connectedComponentRenderSignatures left)
    (rightRendered :
      rightWord.toList = connectedComponentRenderSignatures right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation leftWord =
          connectedComponentFour.semigroup.eval valuation rightWord) :
    left = right :=
  connectedComponentCanonical_eq_of_sameSignature
    leftCanonical rightCanonical <|
      connectedComponentCanonicalSameSignature_of_equalEval
        leftCanonical rightCanonical
        leftWord rightWord leftRendered rightRendered equalEval

theorem connectedComponentCanonical_render_eq_of_equalEval
    {left right : List connectedComponentSignature}
    (leftCanonical :
      connectedComponentFourCanonicalSignatures left)
    (rightCanonical :
      connectedComponentFourCanonicalSignatures right)
    (leftWord rightWord : Word Nat)
    (leftRendered :
      leftWord.toList = connectedComponentRenderSignatures left)
    (rightRendered :
      rightWord.toList = connectedComponentRenderSignatures right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation leftWord =
          connectedComponentFour.semigroup.eval valuation rightWord) :
    connectedComponentRenderSignatures left =
      connectedComponentRenderSignatures right := by
  rw [connectedComponentCanonical_eq_of_equalEval
    leftCanonical rightCanonical leftWord rightWord
    leftRendered rightRendered equalEval]

end SemigroupBasis.Examples

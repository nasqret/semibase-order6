import SemigroupBasis.CoRoots.S5_523Normalization
import SemigroupBasis.Examples.FirstCappedMultiplicityFour
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Examples.SemilatticeTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.Order6ContentFirstTailRoots

open SemigroupBasis
open SemigroupBasis.Examples

universe u

/-! ## Exact content-first/sorted-tail presentation -/

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := word 0 [0]
def xxx : Word Nat := word 0 [0, 0]
def xxy : Word Nat := word 0 [0, 1]
def xyx : Word Nat := word 0 [1, 0]
def xyy : Word Nat := word 0 [1, 1]
def xyz : Word Nat := word 0 [1, 2]
def xzy : Word Nat := word 0 [2, 1]
def xxyz : Word Nat := word 0 [0, 1, 2]

def yxx : Word Nat := word 1 [0, 0]
def yyx : Word Nat := word 1 [1, 0]
def zyx : Word Nat := word 2 [1, 0]
def zyxx : Word Nat := word 2 [1, 0, 0]
def yzx : Word Nat := word 1 [2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def longContractionLaw : Identity Nat := ⟨xxyz, xyz⟩
def tailSwapLaw : Identity Nat := ⟨xyz, xzy⟩

/-- The canonical direct basis
`xx = xxx`, `xxy = xyx`, `xxy = xyy`, `xxyz = xyz`,
`xyz = xzy`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, transferLaw, longContractionLaw,
    tailSwapLaw]

/-- The packet-source orientation. All four packets are opposite-oriented. -/
def oppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨yxx, xyx⟩, ⟨yxx, yyx⟩,
    ⟨zyxx, zyx⟩, ⟨zyx, yzx⟩]

theorem reversedBasis_basis :
    reversedBasis basis = oppositeBasis := by
  decide

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-! ## Transported unrestricted normalization -/

private theorem directPowerDerives : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem s5_523AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_523.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_523.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · have extended :=
      Derives.appendRight directPowerDerives (Word.singleton 0)
    simpa [SemigroupBasis.CoRoots.S5_523.powerLaw,
      SemigroupBasis.CoRoots.S5_523.xxx,
      SemigroupBasis.CoRoots.S5_523.xxxx, powerLaw, xx, xxx, word,
      Word.append, Word.singleton] using extended
  · simpa [SemigroupBasis.CoRoots.S5_523.gatherLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xyx, gatherLaw, xxy, xyx, word] using
      (Derives.fromBasis (basis := basis) (e := gatherLaw) (by
        simp [basis]))
  · simpa [SemigroupBasis.CoRoots.S5_523.transferLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xyy, transferLaw, xxy, xyy, word] using
      (Derives.fromBasis (basis := basis) (e := transferLaw) (by
        simp [basis]))
  · have extended :=
      Derives.appendRight directPowerDerives (Word.singleton 1)
    simpa [SemigroupBasis.CoRoots.S5_523.prefixCapLaw,
      SemigroupBasis.CoRoots.S5_523.xxy,
      SemigroupBasis.CoRoots.S5_523.xxxy, powerLaw, xx, xxx, xxy,
      word, Word.append, Word.singleton] using extended
  · simpa [SemigroupBasis.CoRoots.S5_523.longInsertionLaw,
      SemigroupBasis.CoRoots.S5_523.xyz,
      SemigroupBasis.CoRoots.S5_523.xxyz, longContractionLaw,
      xyz, xxyz, word] using
      (Derives.fromBasis (basis := basis) (e := longContractionLaw) (by
        simp [basis])).symm

private theorem firstCappedAxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ firstCappedMultiplicityFourBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [firstCappedMultiplicityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa [firstCappedPowerLaw, firstCappedXX, firstCappedXXX,
      powerLaw, xx, xxx, word] using directPowerDerives
  · simpa [firstCappedRepeatedFirstLaw, firstCappedXXY,
      firstCappedXYX, gatherLaw, xxy, xyx, word] using
      (Derives.fromBasis (basis := basis) (e := gatherLaw) (by
        simp [basis]))
  · simpa [firstCappedSuffixCommutationLaw, firstCappedXYZ,
      firstCappedXZY, tailSwapLaw, xyz, xzy, word] using
      (Derives.fromBasis (basis := basis) (e := tailSwapLaw) (by
        simp [basis]))

/-- Tail rendered by the `S5_523` long normal form. Unary support carries
two tail copies, binary support carries the head and the other variable,
and larger support retains the first-occurrence tail. -/
private def collapseLongTail (head : Nat) : List Nat → List Nat
  | [] => [head, head]
  | [other] => [head, other]
  | first :: second :: rest => first :: second :: rest

private theorem collapseLongTail_perm (head : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    (collapseLongTail head left).Perm
      (collapseLongTail head right) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact List.Perm.refl _
      | cons rightHead rightTail =>
          have impossible := permutation.length_eq
          simp at impossible
  | cons leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | nil =>
              have impossible := permutation.length_eq
              simp at impossible
          | cons rightHead rightTail =>
              cases rightTail with
              | nil =>
                  have heads : leftHead = rightHead := by
                    simpa using permutation
                  subst rightHead
                  exact List.Perm.refl _
              | cons rightSecond rightRest =>
                  have impossible := permutation.length_eq
                  simp at impossible
      | cons leftSecond leftRest =>
          cases right with
          | nil =>
              have impossible := permutation.length_eq
              simp at impossible
          | cons rightHead rightTail =>
              cases rightTail with
              | nil =>
                  have impossible := permutation.length_eq
                  simp at impossible
              | cons rightSecond rightRest =>
                  simpa [collapseLongTail] using permutation

private theorem mem_firstOccurrenceSequence_iff (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem firstOccurrenceSequence_toList (input : Word Nat) :
    firstOccurrenceSequence input.toList =
      input.head :: (firstOccurrenceSequence input.toList).tail := by
  cases input
  rfl

private theorem firstOccurrenceTails_perm_of_head_support
    (left right : Word Nat) (heads : left.head = right.head)
    (support : SameSupport left right) :
    (firstOccurrenceSequence left.toList).tail.Perm
      (firstOccurrenceSequence right.toList).tail := by
  have sequencePerm :
      (firstOccurrenceSequence left.toList).Perm
        (firstOccurrenceSequence right.toList) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(firstOccurrenceSequence_nodup left.toList).count,
      (firstOccurrenceSequence_nodup right.toList).count]
    simp only [mem_firstOccurrenceSequence_iff, support letter]
  rw [firstOccurrenceSequence_toList left,
    firstOccurrenceSequence_toList right] at sequencePerm
  rw [← heads] at sequencePerm
  rw [List.perm_iff_count]
  intro letter
  have counts := sequencePerm.count letter
  simp only [List.count_cons] at counts
  omega

private def contentFirstLongTail (input : Word Nat) : List Nat :=
  collapseLongTail input.head
    (firstOccurrenceSequence input.toList).tail

private theorem s5_523NormalList_eq_contentFirstLong
    (input : Word Nat) (long : 3 ≤ input.toList.length) :
    SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
        input.toList =
      input.head :: contentFirstLongTail input := by
  cases input with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third more =>
              let orderTail :=
                (firstOccurrenceSequence
                  (head :: second :: third :: more)).tail
              have orderShape :
                  firstOccurrenceSequence
                      (head :: second :: third :: more) =
                    head :: orderTail :=
                firstOccurrenceSequence_toList
                  (word head (second :: third :: more))
              cases tailShape : orderTail with
              | nil =>
                  simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
                    contentFirstLongTail, collapseLongTail, Word.toList,
                    orderShape, tailShape]
              | cons orderSecond orderRest =>
                  cases restShape : orderRest with
                  | nil =>
                      simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
                        contentFirstLongTail, collapseLongTail, Word.toList,
                        orderShape, tailShape, restShape]
                  | cons orderThird orderMore =>
                      simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
                        contentFirstLongTail, collapseLongTail, Word.toList,
                        orderShape, tailShape, restShape]

/-- Every long word derives, without any semantic premise, to the transported
`S5_523` content-first normal form. -/
theorem derivesContentFirstLongNormal (input : Word Nat)
    (long : 3 ≤ input.toList.length) :
    Derives basis input
      (wordOfCons input.head (contentFirstLongTail input)) := by
  have old :=
    SemigroupBasis.CoRoots.S5_523.derivesLongFirstOccurrenceNormal input
  rw [s5_523NormalList_eq_contentFirstLong input long] at old
  change
    Derives SemigroupBasis.CoRoots.S5_523.basis input
      (wordOfCons input.head (contentFirstLongTail input)) at old
  exact old.transport s5_523AxiomDerives

/-- Unconditional long-word completeness: first letter and content determine
every word of length at least three. The middle derivation is exactly the
transported `S4_74` tail-permutation theorem. -/
theorem derivesLongOfHeadSupportEq (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (heads : left.head = right.head)
    (support : SameSupport left right) :
    Derives basis left right := by
  have leftNormal := derivesContentFirstLongNormal left leftLong
  have rightNormal := derivesContentFirstLongNormal right rightLong
  have occurrenceTailPerm :=
    firstOccurrenceTails_perm_of_head_support left right heads support
  have normalTailPerm :
      (contentFirstLongTail left).Perm
        (contentFirstLongTail right) := by
    simpa [contentFirstLongTail, heads] using
      collapseLongTail_perm left.head occurrenceTailPerm
  have oldMiddle :=
    firstCappedDerivesTailPermutation left.head normalTailPerm
  have middle := oldMiddle.transport firstCappedAxiomDerives
  have rightNormal' :
      Derives basis right
        (wordOfCons left.head (contentFirstLongTail right)) := by
    simpa [heads] using rightNormal
  exact leftNormal.trans (middle.trans rightNormal'.symm)

theorem derivesSquareToCube (letter : Nat) :
    Derives basis (wordOfCons letter [letter])
      (wordOfCons letter [letter, letter]) := by
  have substituted :=
    directPowerDerives.subst (fun _ => Word.singleton letter)
  simpa [powerLaw, xx, xxx, word, wordOfCons, Word.bind,
    Word.singleton] using substituted

private theorem derivesNonSingletonUnaryNormal (input : Word Nat)
    (nonSingleton : input.tail ≠ [])
    (onlyHead : ∀ letter, letter ∈ input.toList →
      letter = input.head) :
    Derives basis input (wordOfCons input.head [input.head]) := by
  cases input with
  | mk head tail =>
      cases tail with
      | nil => exact False.elim (nonSingleton rfl)
      | cons second rest =>
          have secondEq : second = head :=
            onlyHead second (by simp [Word.toList])
          subst second
          cases rest with
          | nil => exact Derives.refl _
          | cons third more =>
              have inputLong :
                  3 ≤ (word head (head :: third :: more)).toList.length := by
                simp [word, Word.toList]
              have bridgeLong :
                  3 ≤ (wordOfCons head [head, head]).toList.length := by
                simp [wordOfCons, Word.toList]
              have bridgeSupport :
                  SameSupport (word head (head :: third :: more))
                    (wordOfCons head [head, head]) := by
                intro letter
                constructor
                · intro member
                  have equal := onlyHead letter member
                  subst letter
                  simp [wordOfCons, Word.toList]
                · intro member
                  have equal : letter = head := by
                    simpa [wordOfCons, Word.toList] using member
                  subst letter
                  simp [word, Word.toList]
              exact
                (derivesLongOfHeadSupportEq
                  (word head (head :: third :: more))
                  (wordOfCons head [head, head]) inputLong bridgeLong
                  rfl bridgeSupport).trans
                    (derivesSquareToCube head).symm

/-! ## Semantic separators and the shared completeness theorem -/

private theorem head_eq_of_leftZeroEmbedding
    {S : Type u} (candidate : Semigroup S)
    (embedding : Embedding leftZeroTwo.semigroup candidate)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := embedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

private theorem singleton_right_of_left
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (unary : S) (unarySeparates : unary ≠ candidate.mul unary unary)
    (left right : Word Nat)
    (valid : ∀ valuation : Nat → S,
      candidate.eval valuation left = candidate.eval valuation right)
    (heads : left.head = right.head)
    (support : SameSupport left right)
    (leftSingleton : left.tail = []) :
    right.tail = [] := by
  apply Decidable.byContradiction
  intro rightNonSingleton
  have onlyRightHead :
      ∀ letter, letter ∈ right.toList → letter = right.head := by
    intro letter member
    have inLeft := (support letter).mpr member
    have equalLeft : letter = left.head := by
      cases left with
      | mk head tail =>
          simp only at leftSingleton
          subst tail
          simpa [Word.toList] using inLeft
    simpa [heads] using equalLeft
  have rightNormal :=
    derivesNonSingletonUnaryNormal right rightNonSingleton onlyRightHead
  have evaluated := valid (fun _ => unary)
  have normalized := rightNormal.sound models (fun _ => unary)
  have equality := evaluated.trans normalized
  cases left with
  | mk head tail =>
      simp only at leftSingleton
      subst tail
      change unary = candidate.mul unary unary at equality
      exact unarySeparates equality

private theorem singleton_iff_of_valid
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (unary : S) (unarySeparates : unary ≠ candidate.mul unary unary)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate)
    (heads : identity.lhs.head = identity.rhs.head)
    (support : SameSupport identity.lhs identity.rhs) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  constructor
  · exact singleton_right_of_left candidate models unary unarySeparates
      identity.lhs identity.rhs valid heads support
  · exact singleton_right_of_left candidate models unary unarySeparates
      identity.rhs identity.lhs (fun valuation => (valid valuation).symm)
      heads.symm (fun letter => (support letter).symm)

private theorem binaryShortForcesEq
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (binaryLeft binaryRight : S)
    (binarySeparates :
      candidate.mul binaryLeft binaryRight ≠
        candidate.mul (candidate.mul binaryLeft binaryRight) binaryRight)
    (left right : Word Nat)
    (valid : ∀ valuation : Nat → S,
      candidate.eval valuation left = candidate.eval valuation right)
    (heads : left.head = right.head)
    (support : SameSupport left right)
    (other : Nat) (different : other ≠ left.head)
    (leftShape : left = wordOfCons left.head [other]) :
    right = left := by
  cases right with
  | mk rightHead rightTail =>
      simp only at heads
      rw [← heads]
      cases rightTail with
      | nil =>
          have otherInRight :
              other ∈ (word rightHead []).toList :=
            (support other).mp <| by
              rw [leftShape]
              simp [wordOfCons, Word.toList]
          have equal : other = rightHead := by
            simpa [word, Word.toList] using otherInRight
          exact False.elim (different (equal.trans heads.symm))
      | cons rightSecond rightRest =>
          cases rightRest with
          | nil =>
              have otherInRight :
                  other ∈ (word rightHead [rightSecond]).toList :=
                (support other).mp <| by
                  rw [leftShape]
                  simp [wordOfCons, Word.toList]
              have secondEq : rightSecond = other := by
                have classified :
                    other = rightHead ∨ other = rightSecond := by
                  simpa [word, Word.toList] using otherInRight
                rcases classified with equalHead | equalSecond
                · exact False.elim <|
                    different (Eq.trans equalHead heads.symm)
                · exact Eq.symm equalSecond
              subst rightSecond
              simpa [wordOfCons, word, heads] using leftShape.symm
          | cons rightThird rightMore =>
              let canonical := wordOfCons left.head [other, other]
              have rightLong :
                  3 ≤
                    (word rightHead
                      (rightSecond :: rightThird :: rightMore)).toList.length := by
                simp [word, Word.toList]
              have canonicalLong : 3 ≤ canonical.toList.length := by
                simp [canonical, wordOfCons, Word.toList]
              have canonicalSupport :
                  SameSupport
                    (word rightHead
                      (rightSecond :: rightThird :: rightMore))
                    canonical := by
                intro letter
                have leftMembership :
                    letter ∈ left.toList ↔
                      letter = left.head ∨ letter = other := by
                  rw [leftShape]
                  simp [wordOfCons, Word.toList]
                constructor
                · intro rightMember
                  have leftMember := (support letter).mpr rightMember
                  have classified := leftMembership.mp leftMember
                  simpa [canonical, wordOfCons, Word.toList] using classified
                · intro canonicalMember
                  have classified :
                      letter = left.head ∨ letter = other := by
                    simpa [canonical, wordOfCons, Word.toList] using
                      canonicalMember
                  exact (support letter).mp (leftMembership.mpr classified)
              have rightNormal :=
                derivesLongOfHeadSupportEq
                  (word rightHead
                    (rightSecond :: rightThird :: rightMore))
                  canonical rightLong canonicalLong heads.symm
                  canonicalSupport
              let valuation : Nat → S := fun letter =>
                if letter = left.head then binaryLeft else binaryRight
              have evaluated := valid valuation
              rw [leftShape] at evaluated
              have normalized := rightNormal.sound models valuation
              have equality := evaluated.trans normalized
              change
                candidate.mul (valuation left.head) (valuation other) =
                  candidate.mul
                    (candidate.mul (valuation left.head) (valuation other))
                    (valuation other) at equality
              simp [valuation, different] at equality
              exact False.elim (binarySeparates equality)

/-- Shared source-complete theorem. It proves derivational completeness from
the explicit subsemigroup embeddings and unequal concrete term-function
outputs; it has no completeness or derivational-obligation premise. -/
theorem basisFor_of_contentFirstTailWitnesses
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (leftZeroEmbedding : Embedding leftZeroTwo.semigroup candidate)
    (semilatticeEmbedding : Embedding semilatticeTwo.semigroup candidate)
    (unary : S) (unarySeparates : unary ≠ candidate.mul unary unary)
    (binaryLeft binaryRight : S)
    (binarySeparates :
      candidate.mul binaryLeft binaryRight ≠
        candidate.mul (candidate.mul binaryLeft binaryRight) binaryRight) :
    BasisFor candidate basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have heads :=
    head_eq_of_leftZeroEmbedding candidate leftZeroEmbedding identity valid
  have support : SameSupport identity.lhs identity.rhs :=
    semilatticeValid_support_eq identity
      (semilatticeEmbedding.pullback_identity identity valid)
  have singletons :=
    singleton_iff_of_valid candidate models unary unarySeparates
      identity valid heads support
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              simp only at heads
              subst rightHead
              cases leftTail with
              | nil =>
                  have rightNil : rightTail = [] := singletons.mp rfl
                  subst rightTail
                  exact Derives.refl _
              | cons leftSecond leftRest =>
                  have rightNonempty : rightTail ≠ [] := by
                    intro rightNil
                    have leftNil := singletons.mpr rightNil
                    simp at leftNil
                  cases leftRest with
                  | nil =>
                      by_cases repeated : leftSecond = leftHead
                      · subst leftSecond
                        cases rightTail with
                        | nil => exact False.elim (rightNonempty rfl)
                        | cons rightSecond rightRest =>
                            cases rightRest with
                            | nil =>
                                have rightSecondEq :
                                    rightSecond = leftHead := by
                                  have inLeft :=
                                    (support rightSecond).mpr (by
                                      simp [Word.toList])
                                  simpa [Word.toList] using inLeft
                                subst rightSecond
                                exact Derives.refl _
                            | cons rightThird rightMore =>
                                let bridge :=
                                  wordOfCons leftHead [leftHead, leftHead]
                                have bridgeSupport :
                                    SameSupport bridge
                                      (word leftHead
                                        (rightSecond :: rightThird ::
                                          rightMore)) := by
                                  intro letter
                                  simpa [bridge, wordOfCons, word,
                                    Word.toList] using support letter
                                have bridgeToRight :=
                                  derivesLongOfHeadSupportEq bridge
                                    (word leftHead
                                      (rightSecond :: rightThird ::
                                        rightMore))
                                    (by simp [bridge, wordOfCons,
                                      Word.toList])
                                    (by simp [word, Word.toList]) rfl
                                    bridgeSupport
                                exact
                                  (derivesSquareToCube leftHead).trans
                                    bridgeToRight
                      · have words :=
                          binaryShortForcesEq candidate models
                            binaryLeft binaryRight binarySeparates
                            (word leftHead [leftSecond])
                            (word leftHead rightTail) valid rfl support
                            leftSecond repeated rfl
                        change Derives basis
                          (word leftHead [leftSecond])
                          (word leftHead rightTail)
                        rw [words]
                        exact Derives.refl _
                  | cons leftThird leftMore =>
                      cases rightTail with
                      | nil => exact False.elim (rightNonempty rfl)
                      | cons rightSecond rightRest =>
                          cases rightRest with
                          | nil =>
                              by_cases repeated : rightSecond = leftHead
                              · subst rightSecond
                                let bridge :=
                                  wordOfCons leftHead [leftHead, leftHead]
                                have leftBridgeSupport :
                                    SameSupport
                                      (word leftHead
                                        (leftSecond :: leftThird :: leftMore))
                                      bridge := by
                                  intro letter
                                  simpa [bridge, wordOfCons, word,
                                    Word.toList] using support letter
                                have leftToBridge :=
                                  derivesLongOfHeadSupportEq
                                    (word leftHead
                                      (leftSecond :: leftThird :: leftMore))
                                    bridge
                                    (by simp [word, Word.toList])
                                    (by simp [bridge, wordOfCons,
                                      Word.toList]) rfl leftBridgeSupport
                                exact leftToBridge.trans
                                  (derivesSquareToCube leftHead).symm
                              · have words :=
                                  binaryShortForcesEq candidate models
                                    binaryLeft binaryRight binarySeparates
                                    (word leftHead [rightSecond])
                                    (word leftHead
                                      (leftSecond :: leftThird :: leftMore))
                                    (fun valuation => (valid valuation).symm)
                                    rfl (fun letter =>
                                      (support letter).symm)
                                    rightSecond repeated rfl
                                change Derives basis
                                  (word leftHead
                                    (leftSecond :: leftThird :: leftMore))
                                  (word leftHead [rightSecond])
                                rw [words]
                                exact Derives.refl _
                          | cons rightThird rightMore =>
                              exact derivesLongOfHeadSupportEq
                                (word leftHead
                                  (leftSecond :: leftThird :: leftMore))
                                (word leftHead
                                  (rightSecond :: rightThird :: rightMore))
                                (by simp [word, Word.toList])
                                (by simp [word, Word.toList]) rfl support

/-! ## Finite table helpers -/

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (roundTrip : basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-! ## `S6_3362` -/

namespace S6_3362

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],
  [1,1,2,1,1,1],[1,1,1,1,5,1],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 0 right else
        if left = 3 then row6 0 0 1 0 0 0 right else
          if left = 4 then row6 0 0 0 0 4 0 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bdb64465eba559dda5ba34aedc8aff62a918530188bba1c2c4b2c1b55123f021"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1], [1, 1, 2, 1, 1, 1],
        [1, 1, 1, 1, 5, 1], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (3 : Fin 6) (2 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_3362

/-! ## `S6_3619` -/

namespace S6_3619

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],
  [1,1,2,1,1,1],[1,1,1,1,5,1],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 1 0 0 right else
        if left = 3 then row6 0 0 1 0 0 0 right else
          if left = 4 then row6 0 0 0 0 4 0 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f3e3cf64698994e0c410a6f700216dd321c5c8f96a0c358627a73f0c500e957a"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 2, 1, 1], [1, 1, 2, 1, 1, 1],
        [1, 1, 1, 1, 5, 1], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (3 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_3619

/-! ## `S6_6155` -/

namespace S6_6155

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],
  [1,1,1,4,4,1],[1,1,1,4,4,1],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 0 0 0 3 3 0 right else
          if left = 4 then row6 0 0 0 3 3 0 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b53cd67b1e22e556395b35356aa19b2ef2473e8de5ca0b036722cf0c9774cc0a"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 1], [1, 1, 1, 4, 4, 1],
        [1, 1, 1, 4, 4, 1], [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6155

/-! ## `S6_6173` -/

namespace S6_6173

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,2,1],
  [4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,1,1,1,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 3 3 3 3 3 3 right else
            row6 0 0 0 0 0 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "113063ed44af9ad98e7e261a12487bf3b5be0ca437413e63b1f664a7254f7fc5"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 1], [4, 4, 4, 4, 4, 4],
        [4, 4, 4, 4, 4, 4], [1, 1, 1, 1, 1, 6]] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)

def leftZeroEmbedding : Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def semilatticeEmbedding :
    Embedding semilatticeTwo.semigroup table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem direct_basis : BasisFor table.semigroup basis :=
  basisFor_of_contentFirstTailWitnesses table.semigroup models
    leftZeroEmbedding semilatticeEmbedding (1 : Fin 6) (by decide)
    (2 : Fin 6) (4 : Fin 6) (by decide)

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact direct_basis.oppositeReversed

end S6_6173

end SemigroupBasis.CoRoots.Order6ContentFirstTailRoots

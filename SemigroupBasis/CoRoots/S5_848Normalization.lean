import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.LeftNormalBandThree
import SemigroupBasis.Examples.SimpleSequenceFirstGap
import SemigroupBasis.Generated.S4_71

namespace SemigroupBasis.CoRoots.S5_848

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyyzz : Word Nat := w 0 [1, 1, 2, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def tailSquarePromotionLaw : Identity Nat := ⟨xyyzz, xzyyz⟩

/-- The exact recorded basis for `S5_848`:
`xx = xxx`, `xxy = xyx`, and `xyyzz = xzyyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, tailSquarePromotionLaw]

/-- The literal word-reversal basis used for the opposite endpoint. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisGather :
    Derives basis xxy xyx :=
  Derives.fromBasis (e := gatherLaw) <| by
    simp [basis]

private theorem basisTailSquarePromotion :
    Derives basis xyyzz xzyyz :=
  Derives.fromBasis (e := tailSquarePromotionLaw) <| by
    simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Gather a repeated block into its first-occurrence block:
`u v u = u² v`. -/
theorem derivesGather (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisGather (instantiateThreeWords u v v)
  exact Derives.symm <| by
    simpa [xxy, xyx, w, instantiateThreeWords, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate an initial block when another copy occurs later:
`u v u = u² v u`. -/
theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have gathered := derivesGather u v
  have expanded :=
    Derives.appendRight (derivesPowerExpansion u) v
  have restored :=
    Derives.symm (derivesGather u (u ++ v))
  have expanded' :
      Derives basis ((u ++ u) ++ v)
        ((u ++ u) ++ (u ++ v)) := by
    simpa [Word.append_assoc] using expanded
  have restored' :
      Derives basis ((u ++ u) ++ (u ++ v))
        (((u ++ u) ++ v) ++ u) := by
    simpa [Word.append_assoc] using restored
  exact gathered.trans (expanded'.trans restored')

/-- The recorded third identity after arbitrary nonempty substitutions. -/
theorem derivesTailSquarePromotion
    (guard u v : Word Nat) :
    Derives basis
      ((((guard ++ u) ++ u) ++ v) ++ v)
      ((((guard ++ v) ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisTailSquarePromotion
      (instantiateThreeWords guard u v)
  simpa [xyyzz, xzyyz, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The promotion certificate advertised in the catalogue:
after every nonempty prefix, adjacent square blocks commute. The third
recorded law gives `p u² v² = p v u² v`, and gathering the two copies of
`v` gives `p v² u²`. -/
theorem derivesTailSquareCommutation
    (guard u v : Word Nat) :
    Derives basis
      (guard ++ ((u ++ u) ++ (v ++ v)))
      (guard ++ ((v ++ v) ++ (u ++ u))) := by
  have promoted := derivesTailSquarePromotion guard u v
  have gathered :=
    Derives.prepend guard (derivesGather v (u ++ u))
  have combined := promoted.trans <| by
    simpa [Word.append_assoc] using gathered
  simpa [Word.append_assoc] using combined

private theorem reversed_edmunds_basis_eq_squareBlockBasis :
    reversedBasis edmundsFourSeventyOneBasis =
      squareBlockBasis := by
  decide

/-- The established complete square-block basis, stated on the exact
generated opposite-`S4_71` factor used below. -/
theorem generatedSquareBlockBasis_complete :
    BasisFor Generated.S4_71.table.semigroup.opposite
      squareBlockBasis := by
  have complete := Generated.S4_71.opposite_basis
  rw [reversed_edmunds_basis_eq_squareBlockBasis] at complete
  exact complete

/-- The exact semantic invariant for the tail-square family. The
opposite-`S4_71` component records capped multiplicities, the ordered
globally simple variables, and every first-occurrence gap of a multiple
variable. The separate head component keeps the leading block
distinguished from the square-block commutations allowed in the tail. -/
structure SameTailSquareSignature
    (left right : Word Nat) : Prop where
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup.opposite
  head : left.head = right.head
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleSequence :
    ∀ x y,
      SimpleSequenceFirstGap.SimplePrecedes left x y ↔
        SimpleSequenceFirstGap.SimplePrecedes right x y
  firstGap :
    ∀ simple multiple,
      SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          left simple multiple ↔
        SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          right simple multiple

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameTailSquareSignature left right

/-- Opposite-`S4_71` validity plus equality of heads supplies every
explicit field of the tail-square signature. -/
theorem sameSignature_of_block_valid_head_eq
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy
        Generated.S4_71.table.semigroup.opposite)
    (headEqual : identity.lhs.head = identity.rhs.head) :
    SameTailSquareSignature identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.S4_71.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity Generated.S4_71.table.semigroup).mp blockValid
  have reversedCapped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.reversed.lhs letter =
          S5_107.cappedMultiplicity identity.reversed.rhs letter :=
    fun letter =>
      S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity.reversed reversedValid letter
  have capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter := by
    intro letter
    simpa [Identity.reversed] using reversedCapped letter
  exact
    ⟨blockValid, headEqual, capped,
      fun x y => by
        have order :=
          S5_793Invariant.s4_71Valid_simplePrecedes
            identity.reversed reversedValid reversedCapped y x
        simpa [Identity.reversed,
          SimpleSequenceFirstGap.SimplePrecedes] using order,
      fun simple multiple => by
        have gap :=
          S5_793Invariant.s4_71Valid_multipleLastBeforeSimple
            identity.reversed reversedValid reversedCapped
            multiple simple
        simpa [Identity.reversed,
          SimpleSequenceFirstGap.SimpleBeforeMultipleFirst] using gap⟩

namespace SameTailSquareSignature

theorem refl (word : Word Nat) :
    SameTailSquareSignature word word :=
  sameSignature_of_block_valid_head_eq
    ⟨word, word⟩ (fun _ => rfl) rfl

theorem symm {left right : Word Nat}
    (same : SameTailSquareSignature left right) :
    SameTailSquareSignature right left :=
  ⟨fun valuation => (same.blockTheory valuation).symm,
    same.head.symm,
    fun letter => (same.capped letter).symm,
    fun x y => (same.simpleSequence x y).symm,
    fun simple multiple => (same.firstGap simple multiple).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameTailSquareSignature left middle)
    (second : SameTailSquareSignature middle right) :
    SameTailSquareSignature left right :=
  ⟨fun valuation =>
      (first.blockTheory valuation).trans
        (second.blockTheory valuation),
    first.head.trans second.head,
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.simpleSequence x y).trans
        (second.simpleSequence x y),
    fun simple multiple =>
      (first.firstGap simple multiple).trans
        (second.firstGap simple multiple)⟩

theorem absent {left right : Word Nat}
    (same : SameTailSquareSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same : SameTailSquareSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameTailSquareSignature left right)
    (letter : Nat) :
    S5_107.SimpleIn left letter ↔
      S5_107.SimpleIn right letter := by
  unfold S5_107.SimpleIn
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff,
    same.capped letter]

end SameTailSquareSignature

private theorem bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay every derivation in the complete square-block basis behind a
fixed nonempty prefix. Power and gathering are direct consequences of
the first two recorded laws; the square swap is the promoted third law. -/
theorem liftSquareBlockUnderPrefix
    {left right : Word Nat}
    (derivation : Derives squareBlockBasis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (guard ++ left.bind sigma)
      (guard ++ right.bind sigma) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      simp only [squareBlockBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [squareBlockPowerLaw, squareBlockXX,
          squareBlockXXX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend guard
            (derivesPowerExpansion (sigma 0))
      · simpa [squareBlockGatherLaw, squareBlockXYX,
          squareBlockXXY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend guard
            (derivesGather (sigma 0) (sigma 1))
      · simpa [squareBlockCommutationLaw, squareBlockYYXX,
          squareBlockXXYY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesTailSquareCommutation
            guard (sigma 1) (sigma 0)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih guard sigma)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst guard sigma) (ihSecond guard sigma)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (guard ++ pre.bind sigma) sigma
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih guard sigma) (post.bind sigma)
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih guard (fun letter => (tau letter).bind sigma)

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

private theorem block_left_identity (value : Fin 4) :
    Generated.S4_71.table.semigroup.opposite.mul (3 : Fin 4) value =
      value := by
  apply Fin.ext
  revert value
  decide

/-- If the common head is globally simple, assigning it the left identity
of the square-block factor cancels it and exposes a valid suffix identity. -/
private theorem block_suffix_valid
    (head : Nat) (left right : Word Nat)
    (headNotLeft : head ∉ left.toList)
    (headNotRight : head ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy
          Generated.S4_71.table.semigroup.opposite) :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup.opposite := by
  intro valuation
  let lifted : Nat → Fin 4 :=
    fun letter => if letter = head then 3 else valuation letter
  have leftAgree :
      Generated.S4_71.table.semigroup.opposite.eval valuation left =
        Generated.S4_71.table.semigroup.opposite.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact headNotLeft member
    simp [lifted, different]
  have rightAgree :
      Generated.S4_71.table.semigroup.opposite.eval valuation right =
        Generated.S4_71.table.semigroup.opposite.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact headNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedHead : lifted head = (3 : Fin 4) := by
    simp [lifted]
  rw [liftedHead, block_left_identity,
    block_left_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem head_not_mem_tail_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  cases word with
  | mk head tail =>
      intro member
      have positive : 0 < tail.count head :=
        List.count_pos_iff.mpr member
      simp only [Word.toList, List.count_cons_self] at countOne
      omega

private theorem head_mem_tail_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem head_count_one_iff
    {left right : Word Nat}
    (same : SameTailSquareSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have simpleIff := same.simple left.head
  simpa [S5_107.SimpleIn, same.head] using simpleIff

private theorem tail_nil_of_sameSignature
    {left right : Word Nat}
    (same : SameTailSquareSignature left right)
    (rightHeadSimple :
      right.toList.count right.head = 1)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.support letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    cases left with
    | mk leftHead leftTail =>
        change leftTail = [] at leftTailEmpty
        subst leftTail
        simpa [Word.toList] using leftMember
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.head
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  cases right with
  | mk head tail =>
      have positive : 0 < tail.count head :=
        List.count_pos_iff.mpr rightHeadInTail
      simp only [Word.toList, List.count_cons_self] at rightHeadSimple
      omega

private theorem tail_nil_iff_of_sameSignature
    {left right : Word Nat}
    (same : SameTailSquareSignature left right)
    (leftHeadSimple :
      left.toList.count left.head = 1)
    (rightHeadSimple :
      right.toList.count right.head = 1) :
    left.tail = [] ↔ right.tail = [] := by
  constructor
  · exact tail_nil_of_sameSignature
      same rightHeadSimple
  · exact tail_nil_of_sameSignature
      same.symm leftHeadSimple

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

private theorem derivesDuplicateInitial
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesDuplicateInitial head headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append] using
        S5_107.ListDerives.toWord listDerivation

/-- Unrestricted normalization for the exact tail-square signature.
If the common head is simple, cancel it in the square-block quotient and
replay the complete suffix derivation behind that fixed head. If it is
multiple, duplicate it once and use that duplicate as the fixed guard for
the complete square-block derivation of the whole identity. -/
theorem derives_of_sameTailSquareSignature
    {left right : Word Nat}
    (same : SameTailSquareSignature left right) :
    Derives basis left right := by
  have countIff := head_count_one_iff same
  by_cases leftHeadSimple :
      left.toList.count left.head = 1
  · have rightHeadSimple :
        right.toList.count right.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty :=
      tail_nil_iff_of_sameSignature
        same leftHeadSimple rightHeadSimple
    cases left with
    | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
        have headsEqual : leftHead = rightHead :=
          same.head
        subst rightHead
        cases leftTail with
        | nil =>
          have rightEmpty : rightTail = [] :=
            tailsEmpty.mp rfl
          subst rightTail
          exact Derives.refl _
        | cons leftSuffixHead leftSuffixTail =>
          cases rightTail with
          | nil =>
            have impossible :
                leftSuffixHead :: leftSuffixTail = [] :=
              tailsEmpty.mpr rfl
            contradiction
          | cons rightSuffixHead rightSuffixTail =>
            let leftSuffix : Word Nat :=
              ⟨leftSuffixHead, leftSuffixTail⟩
            let rightSuffix : Word Nat :=
              ⟨rightSuffixHead, rightSuffixTail⟩
            have leftHeadAbsent :
                leftHead ∉ leftSuffix.toList := by
              simpa [leftSuffix, Word.toList] using
                head_not_mem_tail_of_count_one
                  (Word.mk leftHead
                    (leftSuffixHead :: leftSuffixTail))
                  leftHeadSimple
            have rightHeadAbsent :
                leftHead ∉ rightSuffix.toList := by
              simpa [rightSuffix, Word.toList] using
                head_not_mem_tail_of_count_one
                  (Word.mk leftHead
                    (rightSuffixHead :: rightSuffixTail))
                  rightHeadSimple
            have wholeValid :
                (Identity.mk
                  (Word.singleton leftHead ++ leftSuffix)
                  (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                    Generated.S4_71.table.semigroup.opposite := by
              simpa [leftSuffix, rightSuffix, Word.singleton,
                Word.append] using same.blockTheory
            have suffixValid :=
              block_suffix_valid leftHead leftSuffix rightSuffix
                leftHeadAbsent rightHeadAbsent wholeValid
            have suffixDerivation :=
              generatedSquareBlockBasis_complete.2
                ⟨leftSuffix, rightSuffix⟩ suffixValid
            have lifted :=
              liftSquareBlockUnderPrefix suffixDerivation
                (Word.singleton leftHead) Word.singleton
            rw [bind_singleton, bind_singleton] at lifted
            simpa [leftSuffix, rightSuffix, Word.singleton,
              Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail :
        left.head ∈ left.tail :=
      head_mem_tail_of_count_ne_one left leftHeadSimple
    have rightHeadInTail :
        right.head ∈ right.tail :=
      head_mem_tail_of_count_ne_one right rightHeadNotSimple
    have leftDuplicate :=
      derivesDuplicateInitial left leftHeadInTail
    have rightDuplicate :=
      derivesDuplicateInitial right rightHeadInTail
    have rootDerivation :=
      generatedSquareBlockBasis_complete.2
        (Identity.mk left right) same.blockTheory
    have lifted :=
      liftSquareBlockUnderPrefix rootDerivation
        (Word.singleton left.head) Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (Word.singleton left.head ++ left)
          (Word.singleton right.head ++ right) := by
      simpa [same.head] using lifted
    exact leftDuplicate.trans <|
      guarded.trans rightDuplicate.symm

end SemigroupBasis.CoRoots.S5_848

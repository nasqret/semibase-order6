import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_793EndpointCap
import SemigroupBasis.CoRoots.S5_793Invariant

namespace SemigroupBasis.CoRoots.S5_793

open SemigroupBasis
open SemigroupBasis.Examples

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

/-- Replay every derivation in Edmunds' complete stored-orientation
`S4_71` basis behind a fixed nonempty prefix. The gather law is the seventh
family law; square commutation is the derived two-step square-block swap. -/
theorem liftS4_71UnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourSeventyOneBasis left right)
    (ctx : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (ctx ++ left.bind sigma)
      (ctx ++ right.bind sigma) := by
  induction derivation generalizing ctx sigma with
  | fromBasis member =>
      simp only [edmundsFourSeventyOneBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [edmundsFourSeventyOnePowerLaw,
          edmundsFourSeventyOneXX, edmundsFourSeventyOneXXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend ctx
            (derivesPowerExpansion (sigma 0))
      · simpa [edmundsFourSeventyOneGatherLaw,
          edmundsFourSeventyOneXYX, edmundsFourSeventyOneYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesPrefixedGather ctx (sigma 0) (sigma 1)
      · simpa [edmundsFourSeventyOneSquareCommutationLaw,
          edmundsFourSeventyOneXXYY, edmundsFourSeventyOneYYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesPrefixedSquareCommutation
            ctx (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih ctx sigma)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst ctx sigma) (ihSecond ctx sigma)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (ctx ++ pre.bind sigma) sigma
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih ctx sigma) (post.bind sigma)
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih ctx (fun letter => (tau letter).bind sigma)

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

private theorem s4_71_left_identity (value : Fin 4) :
    Generated.S4_71.table.semigroup.mul (3 : Fin 4) value = value := by
  apply Fin.ext
  revert value
  decide

/-- If the common first variable is simple, assigning it the identity of
`S4_71` cancels that initial letter and exposes a valid suffix identity. -/
private theorem s4_71_suffix_valid
    (head : Nat) (left right : Word Nat)
    (headNotLeft : head ∉ left.toList)
    (headNotRight : head ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy
          Generated.S4_71.table.semigroup) :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup := by
  intro valuation
  let lifted : Nat → Fin 4 :=
    fun letter => if letter = head then 3 else valuation letter
  have leftAgree :
      Generated.S4_71.table.semigroup.eval valuation left =
        Generated.S4_71.table.semigroup.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact headNotLeft member
    simp [lifted, different]
  have rightAgree :
      Generated.S4_71.table.semigroup.eval valuation right =
        Generated.S4_71.table.semigroup.eval lifted right := by
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
  rw [liftedHead, s4_71_left_identity,
    s4_71_left_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem head_not_mem_tail_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  have countZero : word.tail.count word.head = 0 := by
    cases word with
    | mk head tail =>
        simpa [Word.toList] using countOne
  exact List.count_eq_zero.mp countZero

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
    (same :
      S5_793Invariant.SameFirstSimpleLastGapSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have simpleIff := same.simple left.head
  simpa [S5_107.SimpleIn, same.first] using simpleIff

private theorem tail_nil_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_793Invariant.SameFirstSimpleLastGapSignature left right)
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
    (head_not_mem_tail_of_count_one right rightHeadSimple)
      rightHeadInTail

private theorem tail_nil_iff_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_793Invariant.SameFirstSimpleLastGapSignature left right)
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

/-- Unrestricted normalization/completeness for the exact family invariant.
For a simple first variable, the `S4_71` suffix identity is normalized
behind that letter. For a multiple first variable, one initial duplicate
guards the complete `S4_71` normalization of the whole word. -/
theorem derives_of_sameFirstSimpleLastGapSignature
    {left right : Word Nat}
    (same :
      S5_793Invariant.SameFirstSimpleLastGapSignature left right) :
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
          same.first
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
              change leftHead ∉
                leftSuffixHead :: leftSuffixTail
              exact head_not_mem_tail_of_count_one
                (Word.mk leftHead
                  (leftSuffixHead :: leftSuffixTail))
                leftHeadSimple
            have rightHeadAbsent :
                leftHead ∉ rightSuffix.toList := by
              change leftHead ∉
                rightSuffixHead :: rightSuffixTail
              exact head_not_mem_tail_of_count_one
                (Word.mk leftHead
                  (rightSuffixHead :: rightSuffixTail))
                rightHeadSimple
            have wholeValid :
                (Identity.mk
                  (Word.singleton leftHead ++ leftSuffix)
                  (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                    Generated.S4_71.table.semigroup := by
              simpa [leftSuffix, rightSuffix, Word.singleton,
                Word.append] using same.blockTheory
            have suffixValid :=
              s4_71_suffix_valid leftHead leftSuffix rightSuffix
                leftHeadAbsent rightHeadAbsent wholeValid
            have suffixDerivation :=
              Generated.S4_71.representative_basis.2
                ⟨leftSuffix, rightSuffix⟩ suffixValid
            have lifted :=
              liftS4_71UnderPrefix suffixDerivation
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
      Generated.S4_71.representative_basis.2
        (Identity.mk left right) same.blockTheory
    have lifted :=
      liftS4_71UnderPrefix rootDerivation
        (Word.singleton left.head) Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (Word.singleton left.head ++ left)
          (Word.singleton right.head ++ right) := by
      simpa [same.first] using lifted
    exact leftDuplicate.trans <|
      guarded.trans rightDuplicate.symm

end SemigroupBasis.CoRoots.S5_793

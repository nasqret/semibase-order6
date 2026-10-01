import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196OppositePrelude
import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite

open SemigroupBasis
open SemigroupBasis.Examples

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-! ## Primitive block moves -/

/-- Delete a doubled middle block while retaining a nonempty prefix and
suffix. -/
private theorem derivesMiddleContraction
    (stem middle suffix : Word Nat) :
    Derives basis
      (((stem ++ middle) ++ middle) ++ suffix)
      ((stem ++ middle) ++ suffix) := by
  have base :
      Derives basis
        (Word.mk 0 [1, 1, 2])
        (Word.mk 0 [1, 2]) :=
    Derives.fromBasis
      (e := Identity.mk
        (Word.mk 0 [1, 1, 2])
        (Word.mk 0 [1, 2])) (by
          unfold basis
          exact List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.head _)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords stem middle suffix)
  simpa [instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Swap two nonempty suffix blocks after a fixed nonempty prefix. -/
private theorem derivesSuffixSwap
    (stem left right : Word Nat) :
    Derives basis
      ((stem ++ left) ++ right)
      ((stem ++ right) ++ left) := by
  have base :
      Derives basis
        (Word.mk 0 [1, 2])
        (Word.mk 0 [2, 1]) :=
    Derives.fromBasis
      (e := Identity.mk
        (Word.mk 0 [1, 2])
        (Word.mk 0 [2, 1])) (by
          unfold basis
          exact List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.head _)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords stem left right)
  simpa [instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the final block of a product of three nonempty blocks. Move it
into the middle, use `xyyz = xyz` backwards, and restore suffix order. -/
private theorem derivesRightDuplication
    (stem middle final : Word Nat) :
    Derives basis
      ((stem ++ middle) ++ final)
      (((stem ++ middle) ++ final) ++ final) := by
  have expose :=
    derivesSuffixSwap stem middle final
  have duplicate :=
    (derivesMiddleContraction stem final middle).symm
  have restore :=
    derivesSuffixSwap stem (final ++ final) middle
  exact expose.trans <|
    duplicate.trans <| by
      simpa [Word.append_assoc] using restore

/-- Every suffix permutation is derivable while the first letter remains
fixed. -/
private theorem derivesTailPermutation
    (head : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfCons head left)
      (wordOfCons head right) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      have suffix := induction (head := letter)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap left right suffix =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
            derivesSuffixSwap
              (Word.singleton head)
              (Word.singleton right)
              (Word.singleton left)
      | cons next rest =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap
                (Word.singleton head)
                (Word.singleton right)
                (Word.singleton left))
              (wordOfCons next rest)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ first second =>
      exact Derives.trans (first (head := head))
        (second (head := head))

private theorem permConsToEnd (letter : Nat) :
    ∀ letters : List Nat,
      (letter :: letters).Perm (letters ++ [letter])
  | [] => List.Perm.refl _
  | next :: rest =>
      (List.Perm.swap next letter rest).trans <|
        List.Perm.cons next (permConsToEnd letter rest)

private theorem permAppendComm (left right : List Nat) :
    (left ++ right).Perm (right ++ left) := by
  rw [List.perm_iff_count]
  intro letter
  simp only [List.count_append]
  omega

/-! ## Content expansion without changing initial simplicity -/

/-- A long word may append a copy of any letter already occurring in its
tail. This is the common operation used in both initial-simplicity branches. -/
private theorem derivesAppendTailMember
    (word : Word Nat) (letter : Nat)
    (long : 3 ≤ word.toList.length)
    (member : letter ∈ word.tail) :
    Derives basis word (word ++ Word.singleton letter) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp at member
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              let remaining :=
                (second :: third :: more).erase letter
              have remainingNonempty : remaining ≠ [] := by
                intro empty
                have erasedLength :=
                  List.length_erase_of_mem member
                rw [show
                  (second :: third :: more).erase letter =
                    remaining by rfl, empty] at erasedLength
                simp at erasedLength
              have arrange :
                  (second :: third :: more).Perm
                    (remaining ++ [letter]) := by
                exact
                  (List.perm_cons_erase member).trans <|
                    permConsToEnd letter remaining
              cases remainingEq : remaining with
              | nil =>
                  exact False.elim
                    (remainingNonempty remainingEq)
              | cons next later =>
                  have arranged :
                      Derives basis
                        (wordOfCons head
                          (second :: third :: more))
                        (wordOfCons head
                          ((next :: later) ++ [letter])) :=
                    derivesTailPermutation head <| by
                      simpa [remainingEq] using arrange
                  have duplicate :=
                    derivesRightDuplication
                      (Word.singleton head)
                      (wordOfCons next later)
                      (Word.singleton letter)
                  have restore :
                      (((next :: later) ++ [letter]) ++
                          [letter]).Perm
                        ((second :: third :: more) ++
                          [letter]) := by
                    have arranged' :
                        (second :: third :: more).Perm
                          ((next :: later) ++ [letter]) := by
                      simpa [remainingEq] using arrange
                    simpa using
                      arranged'.symm.append_right [letter]
                  have restored :=
                    derivesTailPermutation head restore
                  have duplicated :
                      Derives basis
                        (wordOfCons head
                          ((next :: later) ++ [letter]))
                        (wordOfCons head
                          (((next :: later) ++ [letter]) ++
                            [letter])) := by
                    simpa [wordOfCons, Word.singleton,
                      Word.append, Word.append_assoc,
                      List.append_assoc] using duplicate
                  exact arranged.trans <|
                    duplicated.trans <| by
                      simpa [wordOfCons, Word.singleton,
                        Word.append, List.append_assoc] using restored

/-- Append a list of already-supported tail letters to a long word. -/
private theorem derivesAppendTailList
    (word : Word Nat) (letters : List Nat)
    (long : 3 ≤ word.toList.length)
    (supported :
      ∀ letter, letter ∈ letters → letter ∈ word.tail) :
    Derives basis word
      (wordOfCons word.head (word.tail ++ letters)) := by
  induction letters generalizing word with
  | nil =>
      simpa [wordOfCons] using
        (Derives.refl word : Derives basis word word)
  | cons letter rest induction =>
      have letterSupported : letter ∈ word.tail :=
        supported letter (List.Mem.head rest)
      have firstStep :=
        derivesAppendTailMember word letter long letterSupported
      have appendedLong :
          3 ≤
            (word ++ Word.singleton letter).toList.length := by
        simp only [Word.toList_append, Word.toList_singleton,
          List.length_append, List.length_cons, List.length_nil]
        omega
      have restSupported :
          ∀ tested, tested ∈ rest →
            tested ∈
              (word ++ Word.singleton letter).tail := by
        intro tested testedMember
        rw [Word.append_tail]
        exact List.mem_append_left _ <|
          supported tested
            (List.Mem.tail letter testedMember)
      have restStep :=
        induction
          (word ++ Word.singleton letter)
          appendedLong restSupported
      exact firstStep.trans <| by
        simpa [wordOfCons, Word.singleton,
          List.append_assoc] using restStep

/-- Concatenated words with the same first letter commute as whole blocks. -/
private theorem derivesConcatSwap
    (left right : Word Nat)
    (heads : left.head = right.head) :
    Derives basis (left ++ right) (right ++ left) := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at heads
          subst rightHead
          have permutation :
              (leftTail ++ leftHead :: rightTail).Perm
                (rightTail ++ leftHead :: leftTail) := by
            rw [List.perm_iff_count]
            intro letter
            simp only [List.count_append, List.count_cons]
            omega
          simpa [wordOfCons, Word.append] using
            derivesTailPermutation leftHead permutation

private theorem tailMemberOfSameHeadSupport
    {source target : Word Nat}
    (heads : source.head = target.head)
    (targetSimple : target.head ∉ target.tail)
    (support :
      SemigroupBasis.CoRoots.S5_196.SameSupport source target)
    {letter : Nat} (member : letter ∈ target.tail) :
    letter ∈ source.tail := by
  have different : letter ≠ source.head := by
    intro equal
    have targetHeadEq :
        target.head = letter :=
      heads.symm.trans equal.symm
    apply targetSimple
    rw [targetHeadEq]
    exact member
  have sourceMember : letter ∈ source.toList :=
    (support letter).mpr <| by
      change letter ∈ target.head :: target.tail
      exact List.Mem.tail target.head member
  simp only [Word.toList, List.mem_cons] at sourceMember
  exact sourceMember.resolve_left different

private theorem tailMemberOfSupportWithRepeatedHead
    {source target : Word Nat}
    (sourceRepeated : source.head ∈ source.tail)
    (support :
      SemigroupBasis.CoRoots.S5_196.SameSupport source target)
    {letter : Nat} (member : letter ∈ target.toList) :
    letter ∈ source.tail := by
  have sourceMember : letter ∈ source.toList :=
    (support letter).mpr member
  simp only [Word.toList, List.mem_cons] at sourceMember
  rcases sourceMember with equal | tailMember
  · simpa [equal] using sourceRepeated
  · exact tailMember

/-- Long words with equal heads and support are derivably equal when their
common head is globally simple. Only the two tails are merged, so the head
never acquires an extra occurrence. -/
private theorem derivesLongOfSimpleHead
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (heads : left.head = right.head)
    (support :
      SemigroupBasis.CoRoots.S5_196.SameSupport left right)
    (leftSimple : left.head ∉ left.tail)
    (rightSimple : right.head ∉ right.tail) :
    Derives basis left right := by
  have leftExpansion :=
    derivesAppendTailList left right.tail leftLong <| by
      intro letter member
      exact tailMemberOfSameHeadSupport
        heads rightSimple support member
  have rightExpansion :=
    derivesAppendTailList right left.tail rightLong <| by
      intro letter member
      exact tailMemberOfSameHeadSupport
        heads.symm leftSimple
        (fun tested => (support tested).symm) member
  have bridge :
      Derives basis
        (wordOfCons left.head
          (left.tail ++ right.tail))
        (wordOfCons left.head
          (right.tail ++ left.tail)) :=
    derivesTailPermutation left.head
      (permAppendComm left.tail right.tail)
  have rightBack :
      Derives basis
        (wordOfCons left.head
          (right.tail ++ left.tail))
        right := by
    rw [heads]
    exact rightExpansion.symm
  exact leftExpansion.trans <|
    bridge.trans rightBack

/-- Long words with equal heads and support are derivably equal when their
common head is repeated. In this branch the whole opposite word may be
appended, since adding another head occurrence preserves the branch. -/
private theorem derivesLongOfRepeatedHead
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (heads : left.head = right.head)
    (support :
      SemigroupBasis.CoRoots.S5_196.SameSupport left right)
    (leftRepeated : left.head ∈ left.tail)
    (rightRepeated : right.head ∈ right.tail) :
    Derives basis left right := by
  have leftExpansionRaw :=
    derivesAppendTailList left right.toList leftLong <| by
      intro letter member
      exact tailMemberOfSupportWithRepeatedHead
        leftRepeated support member
  have rightExpansionRaw :=
    derivesAppendTailList right left.toList rightLong <| by
      intro letter member
      exact tailMemberOfSupportWithRepeatedHead
        rightRepeated
        (fun tested => (support tested).symm) member
  have leftExpansion :
      Derives basis left (left ++ right) := by
    simpa [wordOfCons, Word.toList, Word.append] using
      leftExpansionRaw
  have rightExpansion :
      Derives basis right (right ++ left) := by
    simpa [wordOfCons, Word.toList, Word.append] using
      rightExpansionRaw
  exact leftExpansion.trans <|
    (derivesConcatSwap left right heads).trans
      rightExpansion.symm

/-! ## Reverse-word invariant bridge -/

private theorem splitPrefixFinal_singleton_append
    (letter : Nat) (word : Word Nat) :
    splitPrefixFinal (Word.singleton letter ++ word) =
      (letter :: (splitPrefixFinal word).1,
        (splitPrefixFinal word).2) := by
  rfl

private theorem splitPrefixFinal_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    splitPrefixFinal (wordOfPrefixFinal stem final) =
      (stem, final) := by
  induction stem with
  | nil =>
      rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons,
        splitPrefixFinal_singleton_append, induction]

private theorem reverse_eq_wordOfPrefixFinal
    (word : Word Nat) :
    word.reverse =
      wordOfPrefixFinal word.tail.reverse word.head := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_wordOfPrefixFinal]
  cases word with
  | mk head tail =>
      simp [Word.toList]

/-- The final-marker predicate on the reversed word is exactly simplicity of
the original head. -/
private theorem simpleFinal_reverse_head_iff
    (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_196.SimpleFinal
        word.reverse word.head ↔
      word.head ∉ word.tail := by
  rw [reverse_eq_wordOfPrefixFinal]
  simp [SemigroupBasis.CoRoots.S5_196.SimpleFinal,
    splitPrefixFinal_wordOfPrefixFinal]

private theorem sameSupport_of_reversed
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_196.SameSupport
        left.reverse right.reverse) :
    SemigroupBasis.CoRoots.S5_196.SameSupport left right := by
  intro letter
  simpa using same letter

private theorem sameSimpleHead_of_reversed
    {left right : Word Nat}
    (heads : left.head = right.head)
    (same :
      SemigroupBasis.CoRoots.S5_196.SameSimpleFinal
        left.reverse right.reverse) :
    (left.head ∉ left.tail) ↔
      (right.head ∉ right.tail) := by
  calc
    left.head ∉ left.tail ↔
        SemigroupBasis.CoRoots.S5_196.SimpleFinal
          left.reverse left.head :=
      (simpleFinal_reverse_head_iff left).symm
    _ ↔
        SemigroupBasis.CoRoots.S5_196.SimpleFinal
          right.reverse left.head :=
      same left.head
    _ ↔
        SemigroupBasis.CoRoots.S5_196.SimpleFinal
          right.reverse right.head := by
      rw [heads]
    _ ↔ right.head ∉ right.tail :=
      simpleFinal_reverse_head_iff right

/-- The syntactic heart of the factor intersection. The reversed
`S5_196` exact class supplies the long-word, support, and simple-head
invariants; the left-zero factor supplies the literal common head. -/
private theorem derivesOfReversedExactAndHead
    (left right : Word Nat)
    (heads : left.head = right.head)
    (exact :
      SemigroupBasis.CoRoots.S5_196.ExactBasisClass
        left.reverse right.reverse) :
    Derives basis left right := by
  classical
  rcases exact with equal |
      ⟨leftReverseLong, rightReverseLong,
        reversedSupport, reversedSimple⟩
  · have words : left = right := by
      have reversed :=
        congrArg (fun word : Word Nat => word.reverse) equal
      simpa using reversed
    rw [words]
    exact Derives.refl _
  · have leftLong : 3 ≤ left.toList.length := by
      simpa using leftReverseLong
    have rightLong : 3 ≤ right.toList.length := by
      simpa using rightReverseLong
    have support :
        SemigroupBasis.CoRoots.S5_196.SameSupport
          left right :=
      sameSupport_of_reversed reversedSupport
    have simpleHeads :=
      sameSimpleHead_of_reversed heads reversedSimple
    by_cases leftSimple : left.head ∉ left.tail
    · have rightSimple : right.head ∉ right.tail :=
        simpleHeads.mp leftSimple
      exact derivesLongOfSimpleHead
        left right leftLong rightLong heads support
        leftSimple rightSimple
    · have leftRepeated : left.head ∈ left.tail :=
        Classical.byContradiction leftSimple
      have rightNotSimple :
          ¬(right.head ∉ right.tail) := by
        intro rightSimple
        exact leftSimple (simpleHeads.mpr rightSimple)
      have rightRepeated : right.head ∈ right.tail :=
        Classical.byContradiction rightNotSimple
      exact derivesLongOfRepeatedHead
        left right leftLong rightLong heads support
        leftRepeated rightRepeated

/-! ## Factor semantics and the public endpoint -/

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def s5_196OppositeTable : FiniteTable where
  order :=
    SemigroupBasis.Generated.Catalogue.S5_196.table.order
  mul := fun left right =>
    SemigroupBasis.Generated.Catalogue.S5_196.table.mul
      right left
  assoc := fun left middle right =>
    (SemigroupBasis.Generated.Catalogue.S5_196.table.assoc
      right middle left).symm

private theorem s5_196OppositeTable_semigroup :
    s5_196OppositeTable.semigroup =
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite :=
  rfl

private theorem modelsS2_4 :
    Models
      SemigroupBasis.Generated.S2_4.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_4.table basis
      toFinThree (by decide)

private theorem modelsS5_196Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite
      basis := by
  rw [← s5_196OppositeTable_semigroup]
  exact FiniteCertificate.checkModels_sound
    s5_196OppositeTable basis toFinThree (by decide)

private theorem head_eq_of_left_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have leftZeroValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_4.table, leftZeroTwo] using
      leftValid
  have evaluated := leftZeroValid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  have rhsDifferent :
      identity.rhs.head ≠ identity.lhs.head :=
    Ne.symm different
  have zeroEqualsOne : (0 : Fin 2) = 1 := by
    simpa [valuation, rhsDifferent] using evaluated
  exact (by decide : (0 : Fin 2) ≠ 1) zeroEqualsOne

/-- Every identity valid in both factors is derivable from the displayed
seven laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup).mp
        rightValid
  exact derivesOfReversedExactAndHead
    identity.lhs identity.rhs
    (head_eq_of_left_valid identity leftValid)
    (SemigroupBasis.CoRoots.S5_196Family.S5_196.valid_exactBasisClass
      identity.reversed reversedValid)

/-- Unrestricted basis for the intersection of the identity theories of
`S2_4` and `S5_196^op`. -/
def factorIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_196Opposite
  complete := derivesOfFactorValid

/-- Compatibility name consumed by the generated order-six endpoints. -/
abbrev intersectionBasis := factorIntersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite

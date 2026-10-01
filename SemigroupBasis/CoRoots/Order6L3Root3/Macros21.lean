import SemigroupBasis.CoRoots.Order6L3Root3.Common

/-!
# Collapse and insertion macros for `S3_4 × S4_21`

The six direct block instances are exactly the msg-0601 laws.  The derived
macros close the three `S4_21` factor moves after protecting the unique
forbidden short stratum: a bare unary square is represented by its cube.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-! ## Direct accepted-law block instances -/

theorem derives21LongPower (block : Word Nat) :
    Derives basis21
      ((block ++ block) ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have base :
      Derives basis21 (word 0 [0, 0]) (word 0 [0, 0, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0]) (word 0 [0, 0, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords block block block)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives21RightCollapse (block suffix : Word Nat) :
    Derives basis21
      (((block ++ block) ++ block) ++ suffix)
      ((block ++ block) ++ suffix) := by
  have base :
      Derives basis21 (word 0 [0, 0, 1]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0, 1]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block suffix suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives21TerminalCollapse (block middle : Word Nat) :
    Derives basis21
      (((block ++ block) ++ middle) ++ block)
      ((block ++ middle) ++ block) := by
  have base :
      Derives basis21 (word 0 [0, 1, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 0]) (word 0 [1, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle middle)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives21SquareTransfer (first second : Word Nat) :
    Derives basis21
      (((first ++ first) ++ second) ++ second)
      (((first ++ second) ++ second) ++ first) := by
  have base :
      Derives basis21 (word 0 [0, 1, 1]) (word 0 [1, 1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 1]) (word 0 [1, 1, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second second)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives21Rotation (first second : Word Nat) :
    Derives basis21
      ((first ++ second) ++ first)
      ((second ++ first) ++ first) := by
  have base :
      Derives basis21 (word 0 [1, 0]) (word 1 [0, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0]) (word 1 [0, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second second)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives21PrefixSwap
    (first second suffix : Word Nat) :
    Derives basis21
      ((first ++ second) ++ suffix)
      ((second ++ first) ++ suffix) := by
  have base :
      Derives basis21 (word 0 [1, 2]) (word 1 [0, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 2]) (word 1 [0, 2])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Derived collapse macros -/

theorem derives21SquareSwitch (first second : Word Nat) :
    Derives basis21
      (((first ++ first) ++ second) ++ second)
      (((second ++ second) ++ first) ++ first) := by
  have transfer := derives21SquareTransfer first second
  have rotate := derives21Rotation first (second ++ second)
  exact transfer.trans <| by
    simpa [Word.append_assoc] using rotate

theorem derives21CompositePowerContraction
    (first rest : Word Nat) :
    Derives basis21
      (((first ++ rest) ++ (first ++ rest)) ++ (first ++ rest))
      ((first ++ rest) ++ (first ++ rest)) := by
  have firstStep :=
    Derives.appendRight
      (Derives.prepend first (derives21Rotation rest first))
      (first ++ rest)
  have firstStep' :
      Derives basis21
        (((first ++ rest) ++ (first ++ rest)) ++ (first ++ rest))
        (((((first ++ first) ++ rest) ++ rest) ++ first) ++ rest) := by
    simpa [Word.append_assoc] using firstStep
  have secondStep :=
    Derives.appendRight
      (derives21TerminalCollapse first (rest ++ rest)) rest
  have secondStep' :
      Derives basis21
        (((((first ++ first) ++ rest) ++ rest) ++ first) ++ rest)
        ((((first ++ rest) ++ rest) ++ first) ++ rest) := by
    simpa [Word.append_assoc] using secondStep
  have thirdStep :=
    Derives.prepend first
      (derives21TerminalCollapse rest first)
  have thirdStep' :
      Derives basis21
        ((((first ++ rest) ++ rest) ++ first) ++ rest)
        ((first ++ rest) ++ (first ++ rest)) := by
    simpa [Word.append_assoc] using thirdStep
  exact firstStep'.trans <| secondStep'.trans thirdStep'

theorem derives21PowerContractionOfLengthAtLeastTwo
    (block : Word Nat) (long : 2 ≤ block.toList.length) :
    Derives basis21
      ((block ++ block) ++ block)
      (block ++ block) := by
  cases block with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          let first := Word.singleton head
          let remaining := Word.mk second rest
          have contraction :=
            derives21CompositePowerContraction first remaining
          simpa [first, remaining, Word.singleton, Word.append,
            Word.append_assoc] using contraction

/-! ## Protected factor-law macros -/

def protect21 (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] =>
      if value.head = last then
        value ++ Word.singleton last
      else
        value
  | _ => value

theorem protect21_of_long
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    protect21 value = value := by
  cases value with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

theorem lift21ContextPrefixSwap
    (pre suf : Option (Word Nat))
    (first second suffix : Word Nat) :
    Derives basis21
      (protect21
        (surround pre ((first ++ second) ++ suffix) suf))
      (protect21
        (surround pre ((second ++ first) ++ suffix) suf)) := by
  rw [protect21_of_long _
      (surroundLong pre suf _
        (threeBlocksLong first second suffix)),
    protect21_of_long _
      (surroundLong pre suf _
        (threeBlocksLong second first suffix))]
  exact surroundDerives pre suf
    (derives21PrefixSwap first second suffix)

theorem lift21ContextSquareSwitch
    (pre suf : Option (Word Nat)) (first second : Word Nat) :
    Derives basis21
      (protect21
        (surround pre
          (((first ++ first) ++ second) ++ second) suf))
      (protect21
        (surround pre
          (((second ++ second) ++ first) ++ first) suf)) := by
  rw [protect21_of_long _
      (surroundLong pre suf _
        (fourBlocksLong first first second second)),
    protect21_of_long _
      (surroundLong pre suf _
        (fourBlocksLong second second first first))]
  exact surroundDerives pre suf
    (derives21SquareSwitch first second)

theorem lift21ContextPower
    (pre suf : Option (Word Nat)) (block : Word Nat) :
    Derives basis21
      (protect21 (surround pre (block ++ block) suf))
      (protect21
        (surround pre ((block ++ block) ++ block) suf)) := by
  cases pre with
  | some preWord =>
      have prefixPositive := wordLengthPositive preWord
      have blockPositive := wordLengthPositive block
      have sourceLong :
          3 ≤
            (surround (some preWord)
              (block ++ block) suf).toList.length := by
        cases suf <;>
          simp [surround, Word.toList_append] <;> omega
      have targetLong :
          3 ≤
            (surround (some preWord)
              ((block ++ block) ++ block) suf).toList.length := by
        cases suf <;>
          simp [surround, Word.toList_append] <;> omega
      rw [protect21_of_long _ sourceLong,
        protect21_of_long _ targetLong]
      cases suf with
      | some suffix =>
          have expansion :=
            Derives.prepend preWord <|
              Derives.symm (derives21RightCollapse block suffix)
          simpa [surround, Word.append_assoc] using expansion
      | none =>
          have expose :=
            derives21PrefixSwap preWord block block
          have duplicate :=
            Derives.symm (derives21TerminalCollapse block preWord)
          have restore :=
            derives21PrefixSwap (block ++ block) preWord block
          exact by
            simpa [surround, Word.append_assoc] using
              expose.trans (duplicate.trans restore)
  | none =>
      cases suf with
      | some suffix =>
          have blockPositive := wordLengthPositive block
          have suffixPositive := wordLengthPositive suffix
          have sourceLong :
              3 ≤
                (surround none (block ++ block)
                  (some suffix)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround none ((block ++ block) ++ block)
                  (some suffix)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [protect21_of_long _ sourceLong,
            protect21_of_long _ targetLong]
          simpa [surround, Word.append_assoc] using
            Derives.symm (derives21RightCollapse block suffix)
      | none =>
          cases block with
          | mk head tail =>
              cases tail with
              | nil =>
                  simpa [surround, protect21, Word.singleton,
                    Word.append] using
                    (Derives.refl (word head [head, head]) :
                      Derives basis21
                        (word head [head, head])
                        (word head [head, head]))
              | cons second rest =>
                  have sourceLong :
                      3 ≤
                        ((Word.mk head (second :: rest) ++
                          Word.mk head (second :: rest))).toList.length := by
                    simp [Word.toList_append, Word.toList] <;> omega
                  have targetLong :
                      3 ≤
                        (((Word.mk head (second :: rest) ++
                            Word.mk head (second :: rest)) ++
                          Word.mk head (second :: rest))).toList.length := by
                    simp [Word.toList_append, Word.toList] <;> omega
                  simp only [surround]
                  rw [protect21_of_long _ sourceLong,
                    protect21_of_long _ targetLong]
                  exact Derives.symm <|
                    derives21PowerContractionOfLengthAtLeastTwo
                      (Word.mk head (second :: rest))
                      (by simp [Word.toList])

end SemigroupBasis.CoRoots.Order6L3Root3

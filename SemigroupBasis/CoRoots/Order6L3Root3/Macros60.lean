import SemigroupBasis.CoRoots.Order6L3Root3.Common

/-!
# Collapse and insertion macros for `S3_4 × S4_60`

The seven direct block instances are exactly the msg-0619 laws.  The
derived macros close the four `S4_60` factor moves after protecting the
forbidden short stratum: every bare quadratic word `xy` is represented
by `xxy`.
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

theorem derives60LongPower (block : Word Nat) :
    Derives basis60
      ((block ++ block) ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have base :
      Derives basis60 (word 0 [0, 0]) (word 0 [0, 0, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0]) (word 0 [0, 0, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords block block block)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60RightCollapse (block suffix : Word Nat) :
    Derives basis60
      (((block ++ block) ++ block) ++ suffix)
      ((block ++ block) ++ suffix) := by
  have base :
      Derives basis60 (word 0 [0, 0, 1]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0, 1]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block suffix suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60TerminalCollapse (block middle : Word Nat) :
    Derives basis60
      (((block ++ block) ++ middle) ++ block)
      ((block ++ middle) ++ block) := by
  have base :
      Derives basis60 (word 0 [0, 1, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 0]) (word 0 [1, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle middle)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60OpenContraction
    (block middle suffix : Word Nat) :
    Derives basis60
      (((block ++ block) ++ middle) ++ suffix)
      ((block ++ middle) ++ suffix) := by
  have base :
      Derives basis60 (word 0 [0, 1, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60FinalDuplicateSwitch
    (first second : Word Nat) :
    Derives basis60
      ((first ++ second) ++ first)
      ((first ++ second) ++ second) := by
  have base :
      Derives basis60 (word 0 [1, 0]) (word 0 [1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0]) (word 0 [1, 1])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second second)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60AnchoredContraction
    (first middle suffix : Word Nat) :
    Derives basis60
      (((first ++ middle) ++ first) ++ suffix)
      ((first ++ middle) ++ suffix) := by
  have base :
      Derives basis60 (word 0 [1, 0, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first middle suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derives60InteriorSwap
    (first second third : Word Nat) :
    Derives basis60
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have base :
      Derives basis60 (word 0 [1, 2, 0]) (word 0 [2, 1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 2, 0]) (word 0 [2, 1, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second third)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Derived factor-law macros -/

theorem derives60InitialGather
    (first second suffix : Word Nat) :
    Derives basis60
      (((first ++ second) ++ first) ++ suffix)
      (((first ++ first) ++ second) ++ suffix) := by
  exact (derives60AnchoredContraction first second suffix).trans <|
    Derives.symm (derives60OpenContraction first second suffix)

theorem derives60FinalGather
    (guard first second : Word Nat) :
    Derives basis60
      (((guard ++ first) ++ second) ++ first)
      (((guard ++ second) ++ first) ++ first) := by
  have expand :=
    Derives.symm
      (derives60AnchoredContraction
        guard (first ++ second) first)
  have swap :=
    Derives.appendRight
      (derives60InteriorSwap guard first second) first
  have contract :=
    derives60AnchoredContraction
      guard (second ++ first) first
  have normalizedExpand :
      Derives basis60
        (((guard ++ first) ++ second) ++ first)
        ((((guard ++ first) ++ second) ++ guard) ++ first) := by
    simpa [Word.append_assoc] using expand
  have normalizedContract :
      Derives basis60
        ((((guard ++ second) ++ first) ++ guard) ++ first)
        (((guard ++ second) ++ first) ++ first) := by
    simpa [Word.append_assoc] using contract
  exact normalizedExpand.trans (swap.trans normalizedContract)

theorem derives60FinalSwitch
    (guard first second : Word Nat) :
    Derives basis60
      (((guard ++ first) ++ second) ++ second)
      (((guard ++ second) ++ first) ++ first) := by
  have expand :=
    Derives.symm
      (derives60FinalDuplicateSwitch
        (guard ++ first) second)
  have swap :=
    Derives.appendRight
      (derives60InteriorSwap guard first second) first
  have contract :=
    derives60AnchoredContraction
      guard (second ++ first) first
  have normalizedExpand :
      Derives basis60
        (((guard ++ first) ++ second) ++ second)
        ((((guard ++ first) ++ second) ++ guard) ++ first) := by
    simpa [Word.append_assoc] using expand
  have normalizedContract :
      Derives basis60
        ((((guard ++ second) ++ first) ++ guard) ++ first)
        (((guard ++ second) ++ first) ++ first) := by
    simpa [Word.append_assoc] using contract
  exact normalizedExpand.trans (swap.trans normalizedContract)

/-! ## Protected factor-law macros -/

def protect60 (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] => Word.mk value.head [value.head, last]
  | _ => value

theorem protect60_of_long
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    protect60 value = value := by
  cases value with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

theorem lift60ContextInitialGather
    (pre suf : Option (Word Nat))
    (first second suffix : Word Nat) :
    Derives basis60
      (protect60
        (surround pre
          (((first ++ second) ++ first) ++ suffix) suf))
      (protect60
        (surround pre
          (((first ++ first) ++ second) ++ suffix) suf)) := by
  rw [protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong first second first suffix)),
    protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong first first second suffix))]
  exact surroundDerives pre suf
    (derives60InitialGather first second suffix)

theorem lift60ContextFinalGather
    (pre suf : Option (Word Nat))
    (guard first second : Word Nat) :
    Derives basis60
      (protect60
        (surround pre
          (((guard ++ first) ++ second) ++ first) suf))
      (protect60
        (surround pre
          (((guard ++ second) ++ first) ++ first) suf)) := by
  rw [protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong guard first second first)),
    protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong guard second first first))]
  exact surroundDerives pre suf
    (derives60FinalGather guard first second)

theorem lift60ContextFinalSwitch
    (pre suf : Option (Word Nat))
    (guard first second : Word Nat) :
    Derives basis60
      (protect60
        (surround pre
          (((guard ++ first) ++ second) ++ second) suf))
      (protect60
        (surround pre
          (((guard ++ second) ++ first) ++ first) suf)) := by
  rw [protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong guard first second second)),
    protect60_of_long _
      (surroundLong pre suf _
        (fourBlocksLong guard second first first))]
  exact surroundDerives pre suf
    (derives60FinalSwitch guard first second)

theorem lift60ContextLeftContraction
    (pre suf : Option (Word Nat))
    (block suffix : Word Nat) :
    Derives basis60
      (protect60
        (surround pre ((block ++ block) ++ suffix) suf))
      (protect60
        (surround pre (block ++ suffix) suf)) := by
  cases suf with
  | some right =>
      have sourceLong :
          3 ≤
            (surround pre ((block ++ block) ++ suffix)
              (some right)).toList.length :=
        surroundLong pre (some right) _
          (threeBlocksLong block block suffix)
      have targetCoreLong :
          3 ≤ ((block ++ suffix) ++ right).toList.length :=
        threeBlocksLong block suffix right
      have targetLong :
          3 ≤
            (surround pre (block ++ suffix)
              (some right)).toList.length := by
        have contextual :=
          surroundLong pre none
            ((block ++ suffix) ++ right) targetCoreLong
        have targetEq :
            surround pre ((block ++ suffix) ++ right) none =
              surround pre (block ++ suffix) (some right) := by
          simpa [addSuffix] using
            surround_append pre none (block ++ suffix) right
        rw [← targetEq]
        exact contextual
      rw [protect60_of_long _ sourceLong,
        protect60_of_long _ targetLong]
      have contextual :=
        surroundDerives pre none
          (derives60OpenContraction block suffix right)
      have sourceEq :
          surround pre
              (((block ++ block) ++ suffix) ++ right) none =
            surround pre ((block ++ block) ++ suffix)
              (some right) := by
        simpa [addSuffix] using
          surround_append pre none
            ((block ++ block) ++ suffix) right
      have targetEq :
          surround pre ((block ++ suffix) ++ right) none =
            surround pre (block ++ suffix) (some right) := by
        simpa [addSuffix] using
          surround_append pre none (block ++ suffix) right
      rw [← sourceEq, ← targetEq]
      exact contextual
  | none =>
      cases pre with
      | some left =>
          have leftPositive := wordLengthPositive left
          have blockPositive := wordLengthPositive block
          have suffixPositive := wordLengthPositive suffix
          have sourceLong :
              3 ≤
                (surround (some left)
                  ((block ++ block) ++ suffix) none).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround (some left)
                  (block ++ suffix) none).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [protect60_of_long _ sourceLong,
            protect60_of_long _ targetLong]
          have expose :=
            Derives.appendRight
              (Derives.symm
                (derives60FinalDuplicateSwitch left block))
              suffix
          have contract :=
            derives60AnchoredContraction left block suffix
          exact by
            simpa [surround, Word.append_assoc] using
              expose.trans contract
      | none =>
          simp only [surround]
          cases block with
          | mk head tail =>
              cases tail with
              | nil =>
                  cases suffix with
                  | mk final suffixTail =>
                      cases suffixTail with
                      | nil =>
                          simpa [protect60, word, Word.append] using
                            (Derives.refl
                              (word head [head, final]) :
                              Derives basis60
                                (word head [head, final])
                                (word head [head, final]))
                      | cons second rest =>
                          let firstSuffix := Word.singleton final
                          let remaining := Word.mk second rest
                          have sourceLong :
                              3 ≤
                                (((Word.mk head [] ++
                                    Word.mk head []) ++
                                  Word.mk final (second :: rest))).toList.length := by
                            simp [Word.toList_append, Word.toList]
                          have targetLong :
                              3 ≤
                                ((Word.mk head [] ++
                                  Word.mk final (second :: rest))).toList.length := by
                            simp [Word.toList_append, Word.toList]
                          rw [protect60_of_long _ sourceLong,
                            protect60_of_long _ targetLong]
                          have contraction :=
                            derives60OpenContraction
                              (Word.mk head [])
                              firstSuffix remaining
                          simpa [firstSuffix, remaining,
                            Word.singleton, Word.append,
                            Word.append_assoc] using contraction
              | cons second rest =>
                  let first := Word.singleton head
                  let remaining := Word.mk second rest
                  have sourceLong :
                      3 ≤
                        (((Word.mk head (second :: rest) ++
                            Word.mk head (second :: rest)) ++
                          suffix).toList.length) :=
                    threeBlocksLong
                      (Word.mk head (second :: rest))
                      (Word.mk head (second :: rest)) suffix
                  have targetLong :
                      3 ≤
                        ((Word.mk head (second :: rest) ++
                          suffix).toList.length) :=
                    threeBlocksLong first remaining suffix
                  rw [protect60_of_long _ sourceLong,
                    protect60_of_long _ targetLong]
                  have firstStep :=
                    Derives.prepend first
                      (derives60AnchoredContraction
                        remaining first suffix)
                  have secondStep :=
                    derives60AnchoredContraction
                      first remaining suffix
                  exact by
                    simpa [first, remaining, Word.singleton,
                      Word.append, Word.append_assoc] using
                      firstStep.trans secondStep

end SemigroupBasis.CoRoots.Order6L3Root3

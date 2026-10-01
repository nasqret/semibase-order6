import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleBlockContexts

/-! Compare complete terminal simple words, including empty words, using
only the proved tail and terminal-block invariants. No semantic equivalence
of reversed words in the same noncommutative model is asserted. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem simplePrefixes_eq_of_invariants {left right leftPrefix rightPrefix leftAfter rightAfter : List Nat}
    (headSame : ∀ x, SimpleHead x left ↔ SimpleHead x right)
    (initialSame : ∀ part, InitialSimpleBlock left part ↔ InitialSimpleBlock right part)
    (leftShape : left = leftPrefix ++ leftAfter) (rightShape : right = rightPrefix ++ rightAfter)
    (leftSimple : ∀ x ∈ leftPrefix, left.count x = 1)
    (rightSimple : ∀ x ∈ rightPrefix, right.count x = 1)
    (leftBlocked : ∀ x suffix, leftAfter = x :: suffix → left.count x ≠ 1)
    (rightBlocked : ∀ x suffix, rightAfter = x :: suffix → right.count x ≠ 1) :
    leftPrefix = rightPrefix := by
  cases leftPrefix with
  | nil =>
      cases rightPrefix with
      | nil => rfl
      | cons y ys =>
          have rightHead : SimpleHead y right :=
            ⟨rightSimple y List.mem_cons_self,by rw [rightShape]; rfl⟩
          have leftHead := (headSame y).mpr rightHead
          have afterHead : leftAfter.head? = some y := by simpa only [leftShape,List.nil_append] using leftHead.2
          cases leftAfter with
          | nil => cases afterHead
          | cons z zs =>
              have equal : z = y := Option.some.inj afterHead
              subst z
              exact False.elim (leftBlocked y zs rfl leftHead.1)
  | cons x xs =>
      cases rightPrefix with
      | nil =>
          have leftHead : SimpleHead x left :=
            ⟨leftSimple x List.mem_cons_self,by rw [leftShape]; rfl⟩
          have rightHead := (headSame x).mp leftHead
          have afterHead : rightAfter.head? = some x := by simpa only [rightShape,List.nil_append] using rightHead.2
          cases rightAfter with
          | nil => cases afterHead
          | cons z zs =>
              have equal : z = x := Option.some.inj afterHead
              subst z
              exact False.elim (rightBlocked x zs rfl rightHead.1)
      | cons y ys =>
          have first := initialSimpleBlock_of_context left (x :: xs) leftAfter leftShape (by simp) leftSimple leftBlocked
          have second := initialSimpleBlock_of_context right (y :: ys) rightAfter rightShape (by simp) rightSimple rightBlocked
          exact ((initialSame (x :: xs)).mp first).unique second

theorem InitialSimpleBlock.reverse_terminal {word part : List Nat} (initial : InitialSimpleBlock word part) :
    TerminalSimpleBlock word.reverse part.reverse := by
  rcases initial.2 with ⟨after,shape⟩
  exact ⟨initial.1.reverse,after.reverse,by simpa only [List.reverse_append] using congrArg List.reverse shape⟩

theorem initialSimpleBlock_reverse_iff (word part : List Nat) :
    InitialSimpleBlock word.reverse part.reverse ↔ TerminalSimpleBlock word part := by
  constructor
  · intro initial
    simpa only [List.reverse_reverse] using initial.reverse_terminal
  · exact TerminalSimpleBlock.reverse_initial

theorem terminalSimpleBlock_of_context (word before part : List Nat)
    (shape : word = before ++ part) (nonempty : part ≠ [])
    (simple : ∀ x ∈ part, word.count x = 1)
    (blocked : ∀ leading x, before = leading ++ [x] → word.count x ≠ 1) :
    TerminalSimpleBlock word part := by
  refine ⟨maximalSimpleBlock_of_context word before part [] ?_ nonempty simple blocked ?_,before,shape⟩
  · simpa only [List.append_nil] using shape
  · intro x tail impossible
    cases impossible

namespace Semantics

theorem SameEval.reversedSimpleHeads {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x : Nat) :
    SimpleHead x left.reverse ↔ SimpleHead x right.reverse := by
  simpa only [SimpleHead,SimpleTail,List.count_reverse] using same.simpleTail x

theorem SameEval.reversedInitialBlocks {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) :
    InitialSimpleBlock left.reverse part ↔ InitialSimpleBlock right.reverse part := by
  have first := initialSimpleBlock_reverse_iff left part.reverse
  have second := initialSimpleBlock_reverse_iff right part.reverse
  simpa only [List.reverse_reverse] using first.trans ((same.terminalSimpleBlock part.reverse).trans second.symm)

theorem SameEval.simpleSuffixes_eq {which : Bool} {left right leftSuffix rightSuffix leftBefore rightBefore : List Nat}
    (same : SameEval which left right)
    (leftShape : left = leftBefore ++ leftSuffix) (rightShape : right = rightBefore ++ rightSuffix)
    (leftSimple : ∀ x ∈ leftSuffix, left.count x = 1)
    (rightSimple : ∀ x ∈ rightSuffix, right.count x = 1)
    (leftBlocked : ∀ leading x, leftBefore = leading ++ [x] → left.count x ≠ 1)
    (rightBlocked : ∀ leading x, rightBefore = leading ++ [x] → right.count x ≠ 1) :
    leftSuffix = rightSuffix := by
  have reversed : leftSuffix.reverse = rightSuffix.reverse := by
    apply simplePrefixes_eq_of_invariants
      (leftAfter := leftBefore.reverse) (rightAfter := rightBefore.reverse)
      same.reversedSimpleHeads same.reversedInitialBlocks
    · simpa only [List.reverse_append] using congrArg List.reverse leftShape
    · simpa only [List.reverse_append] using congrArg List.reverse rightShape
    · intro x member
      have original : x ∈ leftSuffix := by simpa only [List.mem_reverse] using member
      simpa only [List.count_reverse] using leftSimple x original
    · intro x member
      have original : x ∈ rightSuffix := by simpa only [List.mem_reverse] using member
      simpa only [List.count_reverse] using rightSimple x original
    · intro x tail shape one
      have originalShape : leftBefore = tail.reverse ++ [x] := by
        simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse shape
      apply leftBlocked tail.reverse x originalShape
      simpa only [List.count_reverse] using one
    · intro x tail shape one
      have originalShape : rightBefore = tail.reverse ++ [x] := by
        simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse shape
      apply rightBlocked tail.reverse x originalShape
      simpa only [List.count_reverse] using one
  simpa only [List.reverse_reverse] using congrArg List.reverse reversed

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simplePrefixes_eq_of_invariants
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.InitialSimpleBlock.reverse_terminal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.initialSimpleBlock_reverse_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.terminalSimpleBlock_of_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.reversedSimpleHeads
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.reversedInitialBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleSuffixes_eq

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

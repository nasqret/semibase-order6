import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleAdjacency

/-! Reconstruct actual simple factors from the F_SS graph. Consequently the
sets of maximal simple blocks, and the initial and terminal blocks, are
semantic invariants. Internal blocks need not occur in the same order. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem first_split_unique (marker : Nat) (before : List Nat) :
    ∀ (after otherBefore otherAfter : List Nat), marker ∉ before → marker ∉ otherBefore →
      before ++ marker :: after = otherBefore ++ marker :: otherAfter →
      before = otherBefore ∧ after = otherAfter := by
  induction before with
  | nil =>
      intro after otherBefore otherAfter absentLeft absentRight shape
      cases otherBefore with
      | nil => exact ⟨rfl,(List.cons.inj shape).2⟩
      | cons y ys =>
          have equal : marker = y := (List.cons.inj shape).1
          exact False.elim (absentRight (by simp [← equal]))
  | cons x xs ih =>
      intro after otherBefore otherAfter absentLeft absentRight shape
      cases otherBefore with
      | nil =>
          have equal : x = marker := (List.cons.inj shape).1
          exact False.elim (absentLeft (by simp [equal]))
      | cons y ys =>
          have equal : x = y := (List.cons.inj shape).1
          subst y
          have rest := ih after ys otherAfter
            (fun member => absentLeft (List.mem_cons.mpr (Or.inr member)))
            (fun member => absentRight (List.mem_cons.mpr (Or.inr member))) (List.cons.inj shape).2
          exact ⟨congrArg (List.cons x) rest.1,rest.2⟩

def SimpleChain (word : List Nat) : List Nat → Prop
  | [] => True
  | [x] => word.count x = 1
  | x :: y :: rest => SimpleAdjacent x y word ∧ SimpleChain word (y :: rest)

theorem simpleChain_counts (word letters : List Nat) :
    SimpleChain word letters → ∀ marker ∈ letters, word.count marker = 1 := by
  induction letters with
  | nil => intro _ marker member; cases member
  | cons x xs ih =>
      intro chain marker member
      cases xs with
      | nil =>
          have equal : marker = x := by simpa using member
          subst marker
          exact chain
      | cons y ys =>
          change SimpleAdjacent x y word ∧ SimpleChain word (y :: ys) at chain
          rcases List.mem_cons.mp member with equal | member
          · subst marker
            exact (chain.1.2.counts chain.1.1).1
          · exact ih chain.2 marker member

theorem simpleChain_follows (word rest : List Nat) :
    ∀ (x : Nat) (before after : List Nat), SimpleChain word (x :: rest) →
      word = before ++ x :: after → x ∉ before →
      ∃ suffix, after = rest ++ suffix := by
  induction rest with
  | nil => intro x before after _ _ _; exact ⟨after,rfl⟩
  | cons y ys ih =>
      intro x before after chain shape absent
      change SimpleAdjacent x y word ∧ SimpleChain word (y :: ys) at chain
      have different := chain.1.1
      rcases chain.1.2 with ⟨p,q,adjacent,pX,pY,_,_⟩
      have unique := first_split_unique x before after p (y :: q) absent pX (shape.symm.trans adjacent)
      have nextShape : word = (p ++ [x]) ++ y :: q := by simpa [List.append_assoc] using adjacent
      have nextAbsent : y ∉ p ++ [x] := by simp [pY,Ne.symm different]
      rcases ih y (p ++ [x]) q chain.2 nextShape nextAbsent with ⟨suffix,tail⟩
      exact ⟨suffix,by rw [unique.2,tail]; rfl⟩

def SimpleFactor (word part : List Nat) : Prop :=
  ∃ before after, word = before ++ part ++ after ∧
    ∀ marker ∈ part, word.count marker = 1

theorem SimpleFactor.countOne {word part : List Nat} (factor : SimpleFactor word part)
    (marker : Nat) (member : marker ∈ part) : word.count marker = 1 := by
  rcases factor with ⟨_,_,_,counts⟩
  exact counts marker member

theorem simpleChain_of_factor (word letters : List Nat) :
    ∀ before after, word = before ++ letters ++ after →
      (∀ marker ∈ letters, word.count marker = 1) → SimpleChain word letters := by
  induction letters with
  | nil => intro _ _ _ _; trivial
  | cons x xs ih =>
      intro before after shape counts
      cases xs with
      | nil => exact counts x (by simp)
      | cons y ys =>
          have onceX := counts x (by simp)
          have onceY := counts y (by simp)
          have different : x ≠ y := by
            intro equal
            subst y
            have count := onceX
            rw [shape] at count
            simp only [List.count_append,List.count_cons_self] at count
            omega
          have adjacent : CleanAdjacent x y word :=
            cleanAdjacent_of_count_one x y word different onceX onceY
              ⟨before,ys ++ after,by simpa [List.append_assoc] using shape⟩
          have tailShape : word = (before ++ [x]) ++ (y :: ys) ++ after := by
            simpa [List.append_assoc] using shape
          exact ⟨⟨different,adjacent⟩,ih (before ++ [x]) after tailShape
            (fun marker member => counts marker (List.mem_cons.mpr (Or.inr member)))⟩

theorem simpleChain_iff_factor (word letters : List Nat) :
    SimpleChain word letters ↔ SimpleFactor word letters := by
  constructor
  · intro chain
    have counts := simpleChain_counts word letters chain
    cases letters with
    | nil => exact ⟨[],word,rfl,counts⟩
    | cons x xs =>
        rcases countOne_split x word (counts x (by simp)) with ⟨before,after,shape,absent,_⟩
        rcases simpleChain_follows word xs x before after chain shape absent with ⟨suffix,tail⟩
        refine ⟨before,suffix,?_,counts⟩
        rw [tail] at shape
        simpa [List.append_assoc] using shape
  · rintro ⟨before,after,shape,counts⟩
    exact simpleChain_of_factor word letters before after shape counts

theorem SimpleFactor.reverse {word part : List Nat} (factor : SimpleFactor word part) :
    SimpleFactor word.reverse part.reverse := by
  rcases factor with ⟨before,after,shape,counts⟩
  refine ⟨after.reverse,before.reverse,?_,?_⟩
  · have reflected := congrArg List.reverse shape
    simpa [List.reverse_append,List.append_assoc] using reflected
  · intro marker member
    have count := counts marker (by simpa using member)
    simpa using count

theorem SimpleFactor.antisymm {left right : List Nat}
    (first : SimpleFactor left right) (second : SimpleFactor right left) : left = right := by
  rcases first with ⟨before,after,shape,_⟩
  rcases second with ⟨otherBefore,otherAfter,otherShape,_⟩
  have firstLength := congrArg List.length shape
  have secondLength := congrArg List.length otherShape
  simp only [List.length_append] at firstLength secondLength
  have emptyBefore : before = [] := List.length_eq_zero_iff.mp (by omega)
  have emptyAfter : after = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [emptyBefore,emptyAfter] using shape

def MaximalSimpleBlock (word part : List Nat) : Prop :=
  part ≠ [] ∧ SimpleFactor word part ∧
    (∀ x, ¬ SimpleFactor word (x :: part)) ∧
    (∀ x, ¬ SimpleFactor word (part ++ [x]))

def InitialSimpleBlock (word part : List Nat) : Prop :=
  MaximalSimpleBlock word part ∧ ∃ after, word = part ++ after

def TerminalSimpleBlock (word part : List Nat) : Prop :=
  MaximalSimpleBlock word part ∧ ∃ before, word = before ++ part

theorem simpleFactor_prefix_iff {word part : List Nat} (factor : SimpleFactor word part)
    (nonempty : part ≠ []) :
    (∃ after, word = part ++ after) ↔ ∀ x xs, part = x :: xs → SimpleHead x word := by
  constructor
  · rintro ⟨after,shape⟩ x xs partShape
    refine ⟨factor.countOne x (by simp [partShape]),?_⟩
    simp [shape,partShape]
  · intro atHead
    cases part with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs =>
        have head := atHead x xs rfl
        rcases factor with ⟨before,after,shape,_⟩
        have absent : x ∉ before := by
          have count := head.1
          rw [shape] at count
          simp only [List.count_append,List.count_cons_self] at count
          exact List.count_eq_zero.mp (by omega)
        have currentShape : word = before ++ x :: (xs ++ after) := by
          simpa [List.append_assoc] using shape
        have currentHead : (before ++ x :: (xs ++ after)).head? = some x := by
          rw [← currentShape]
          exact head.2
        have emptyBefore := (head_split_iff x before (xs ++ after) absent).mp currentHead
        exact ⟨after,by simpa [emptyBefore] using shape⟩

theorem simpleFactor_suffix_iff {word part : List Nat} (factor : SimpleFactor word part)
    (nonempty : part ≠ []) :
    (∃ before, word = before ++ part) ↔ ∀ x xs, part.reverse = x :: xs → SimpleTail x word := by
  have reflectedPrefix : (∃ before, word = before ++ part) ↔
      (∃ after, word.reverse = part.reverse ++ after) := by
    constructor
    · rintro ⟨before,shape⟩
      exact ⟨before.reverse,by simp [shape,List.reverse_append]⟩
    · rintro ⟨after,shape⟩
      have reflected := congrArg List.reverse shape
      exact ⟨after.reverse,by simpa [List.reverse_append] using reflected⟩
  rw [reflectedPrefix]
  have result := simpleFactor_prefix_iff factor.reverse (by simpa using nonempty)
  simpa [SimpleHead,SimpleTail] using result

namespace Semantics

theorem SameEval.simpleChain {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) : SimpleChain left part ↔ SimpleChain right part := by
  induction part with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => exact same.countOne x
      | cons y ys =>
          change (SimpleAdjacent x y left ∧ SimpleChain left (y :: ys)) ↔
            (SimpleAdjacent x y right ∧ SimpleChain right (y :: ys))
          exact and_congr (same.simpleAdjacent x y) ih

theorem SameEval.simpleFactor {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) : SimpleFactor left part ↔ SimpleFactor right part := by
  rw [← simpleChain_iff_factor,← simpleChain_iff_factor]
  exact same.simpleChain part

theorem SameEval.maximalSimpleBlock {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) :
    MaximalSimpleBlock left part ↔ MaximalSimpleBlock right part := by
  simp only [MaximalSimpleBlock,same.simpleFactor]

theorem SameEval.initialSimpleBlock_forward {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) (initial : InitialSimpleBlock left part) :
    InitialSimpleBlock right part := by
  have rightMaximal := (same.maximalSimpleBlock part).mp initial.1
  have oldHead := (simpleFactor_prefix_iff initial.1.2.1 initial.1.1).mp initial.2
  refine ⟨rightMaximal,(simpleFactor_prefix_iff rightMaximal.2.1 rightMaximal.1).mpr ?_⟩
  intro x xs shape
  exact (same.simpleHead x).mp (oldHead x xs shape)

theorem SameEval.initialSimpleBlock {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) :
    InitialSimpleBlock left part ↔ InitialSimpleBlock right part :=
  ⟨same.initialSimpleBlock_forward part,same.symm.initialSimpleBlock_forward part⟩

theorem SameEval.terminalSimpleBlock_forward {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) (terminal : TerminalSimpleBlock left part) :
    TerminalSimpleBlock right part := by
  have rightMaximal := (same.maximalSimpleBlock part).mp terminal.1
  have oldTail := (simpleFactor_suffix_iff terminal.1.2.1 terminal.1.1).mp terminal.2
  refine ⟨rightMaximal,(simpleFactor_suffix_iff rightMaximal.2.1 rightMaximal.1).mpr ?_⟩
  intro x xs shape
  exact (same.simpleTail x).mp (oldTail x xs shape)

theorem SameEval.terminalSimpleBlock {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) :
    TerminalSimpleBlock left part ↔ TerminalSimpleBlock right part :=
  ⟨same.terminalSimpleBlock_forward part,same.symm.terminalSimpleBlock_forward part⟩

theorem SameEval.simpleWord_literal {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (simple : ∀ marker ∈ left, left.count marker = 1) : left = right := by
  have simpleRight : ∀ marker ∈ right, right.count marker = 1 := by
    intro marker member
    exact (same.countOne marker).mp (simple marker ((same.mem marker).mpr member))
  have leftSelf : SimpleFactor left left := ⟨[],[],by simp,simple⟩
  have rightSelf : SimpleFactor right right := ⟨[],[],by simp,simpleRight⟩
  exact ((same.symm.simpleFactor right).mp rightSelf).antisymm ((same.simpleFactor left).mp leftSelf)

end Semantics

theorem ListDerives.maximalSimpleBlock_iff {left right : List Nat} (derivation : ListDerives left right)
    (part : List Nat) : MaximalSimpleBlock left part ↔ MaximalSimpleBlock right part :=
  (Semantics.derives_sameEval false derivation).maximalSimpleBlock part

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.first_split_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleChain_counts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleChain_follows
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleChain_of_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleChain_iff_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.SimpleFactor.reverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.SimpleFactor.antisymm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleFactor_prefix_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleFactor_suffix_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleFactor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.maximalSimpleBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.initialSimpleBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.terminalSimpleBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleWord_literal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.ListDerives.maximalSimpleBlock_iff

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

import SemigroupBasis.CoRoots.Order6SporadicSection17C5BetaPermutations

/-! Representation-boundary lemmas for actual simple blocks. Fixed nonsimple
neighbors certify maximality, and semantic equivalence fixes the complete
initial simple word, including its empty case. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem fixedPrefix_cancel (leading left right : List Nat)
    (equal : leading ++ left = leading ++ right) : left = right := by
  induction leading with
  | nil => exact equal
  | cons x rest ih => exact ih (List.cons.inj equal).2

theorem countOne_prefix_absent {word before after : List Nat} {x : Nat}
    (one : word.count x = 1) (shape : word = before ++ x :: after) : x ∉ before := by
  have count := one
  rw [shape] at count
  simp only [List.count_append,List.count_cons_self] at count
  exact List.count_eq_zero.mp (by omega)

theorem maximalSimpleBlock_of_context (word before part after : List Nat)
    (shape : word = before ++ part ++ after) (nonempty : part ≠ [])
    (simple : ∀ x ∈ part, word.count x = 1)
    (leftBlocked : ∀ leading x, before = leading ++ [x] → word.count x ≠ 1)
    (rightBlocked : ∀ x suffix, after = x :: suffix → word.count x ≠ 1) :
    MaximalSimpleBlock word part := by
  refine ⟨nonempty,⟨before,after,shape,simple⟩,?_,?_⟩
  · intro x extension
    cases part with
    | nil => exact nonempty rfl
    | cons h tail =>
        rcases extension with ⟨otherBefore,otherAfter,otherShape,counts⟩
        have one := simple h List.mem_cons_self
        have firstShape : word = before ++ h :: (tail ++ after) := by
          simpa only [List.cons_append,List.append_assoc] using shape
        have secondShape : word = (otherBefore ++ [x]) ++ h :: (tail ++ otherAfter) := by
          simpa only [List.cons_append,List.nil_append,List.append_assoc] using otherShape
        have unique := first_split_unique h before (tail ++ after) (otherBefore ++ [x]) (tail ++ otherAfter)
          (countOne_prefix_absent one firstShape) (countOne_prefix_absent one secondShape)
          (firstShape.symm.trans secondShape)
        exact leftBlocked otherBefore x unique.1 (counts x List.mem_cons_self)
  · intro x extension
    cases part with
    | nil => exact nonempty rfl
    | cons h tail =>
        rcases extension with ⟨otherBefore,otherAfter,otherShape,counts⟩
        have one := simple h List.mem_cons_self
        have firstShape : word = before ++ h :: (tail ++ after) := by
          simpa only [List.cons_append,List.append_assoc] using shape
        have secondShape : word = otherBefore ++ h :: (tail ++ x :: otherAfter) := by
          simpa only [List.cons_append,List.nil_append,List.append_assoc] using otherShape
        have unique := first_split_unique h before (tail ++ after) otherBefore (tail ++ x :: otherAfter)
          (countOne_prefix_absent one firstShape) (countOne_prefix_absent one secondShape)
          (firstShape.symm.trans secondShape)
        have afterShape := fixedPrefix_cancel tail after (x :: otherAfter) unique.2
        exact rightBlocked x otherAfter afterShape
          (counts x (List.mem_append.mpr (Or.inr (by simp))))

theorem MaximalSimpleBlock.eq_of_prefix {word part other : List Nat}
    (maximal : MaximalSimpleBlock word part) (factor : SimpleFactor word other)
    (extensionExists : ∃ tail, other = part ++ tail) : other = part := by
  rcases extensionExists with ⟨tail,extension⟩
  cases tail with
  | nil => simpa only [List.append_nil] using extension
  | cons x rest =>
      rcases factor with ⟨before,after,shape,counts⟩
      apply False.elim
      apply maximal.2.2.2 x
      refine ⟨before,rest ++ after,?_,?_⟩
      · simpa only [extension,List.append_assoc,List.cons_append,List.nil_append] using shape
      · intro y member
        apply counts y
        rw [extension]
        rcases List.mem_append.mp member with inPart | inLast
        · exact List.mem_append.mpr (Or.inl inPart)
        · have equal : y = x := List.mem_singleton.mp inLast
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl equal)))

theorem InitialSimpleBlock.unique {word left right : List Nat}
    (first : InitialSimpleBlock word left) (second : InitialSimpleBlock word right) : left = right := by
  rcases first.2 with ⟨leftAfter,leftShape⟩
  rcases second.2 with ⟨rightAfter,rightShape⟩
  have leftPrefix : left <+: word := ⟨leftAfter,leftShape.symm⟩
  have rightPrefix : right <+: word := ⟨rightAfter,rightShape.symm⟩
  rcases List.prefix_or_prefix_of_prefix leftPrefix rightPrefix with leftFirst | rightFirst
  · rcases leftFirst with ⟨tail,equal⟩
    exact (MaximalSimpleBlock.eq_of_prefix first.1 second.1.2.1 ⟨tail,equal.symm⟩).symm
  · rcases rightFirst with ⟨tail,equal⟩
    exact MaximalSimpleBlock.eq_of_prefix second.1 first.1.2.1 ⟨tail,equal.symm⟩

theorem MaximalSimpleBlock.reverse {word part : List Nat} (maximal : MaximalSimpleBlock word part) :
    MaximalSimpleBlock word.reverse part.reverse := by
  refine ⟨?_,maximal.2.1.reverse,?_,?_⟩
  · intro empty
    apply maximal.1
    simpa only [List.reverse_reverse,List.reverse_nil] using congrArg List.reverse empty
  · intro x extension
    apply maximal.2.2.2 x
    simpa only [List.reverse_cons,List.reverse_reverse] using extension.reverse
  · intro x extension
    apply maximal.2.2.1 x
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.reverse_reverse]
      using extension.reverse

theorem TerminalSimpleBlock.reverse_initial {word part : List Nat} (terminal : TerminalSimpleBlock word part) :
    InitialSimpleBlock word.reverse part.reverse := by
  rcases terminal.2 with ⟨before,shape⟩
  exact ⟨terminal.1.reverse,before.reverse,by simpa only [List.reverse_append] using congrArg List.reverse shape⟩

theorem TerminalSimpleBlock.unique {word left right : List Nat}
    (first : TerminalSimpleBlock word left) (second : TerminalSimpleBlock word right) : left = right := by
  have equal := first.reverse_initial.unique second.reverse_initial
  simpa only [List.reverse_reverse] using congrArg List.reverse equal

theorem initialSimpleBlock_of_context (word part after : List Nat)
    (shape : word = part ++ after) (nonempty : part ≠ [])
    (simple : ∀ x ∈ part, word.count x = 1)
    (blocked : ∀ x suffix, after = x :: suffix → word.count x ≠ 1) :
    InitialSimpleBlock word part := by
  refine ⟨maximalSimpleBlock_of_context word [] part after shape nonempty simple ?_ blocked,after,shape⟩
  intro leading x impossible
  have length := congrArg List.length impossible
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

namespace Semantics

theorem SameEval.simplePrefixes_eq {which : Bool} {left right leftPrefix rightPrefix leftAfter rightAfter : List Nat}
    (same : SameEval which left right)
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
          have leftHead := (same.simpleHead y).mpr rightHead
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
          have rightHead := (same.simpleHead x).mp leftHead
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
          exact ((same.initialSimpleBlock (x :: xs)).mp first).unique second

end Semantics

theorem bodyPiecesWord_head_not_simple (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (x : Nat) (tail : List Nat)
    (shape : bodyPiecesWord pieces = x :: tail) : original.count x ≠ 1 := by
  cases pieces with
  | nil => cases shape
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      cases tiles with
      | nil => exact False.elim (good.1.1 rfl)
      | cons tile tiles =>
          cases tile with
          | square y =>
              have equal : y = x := (List.cons.inj shape).1
              subst x
              have restricted : Restricted y original := good.1.2.1 (.square y) List.mem_cons_self
              have two := restricted_count_two y original restricted
              omega
          | cube y =>
              have equal : y = x := (List.cons.inj shape).1
              subst x
              have unrestricted : Unrestricted y original := good.1.2.1 (.cube y) List.mem_cons_self
              exact unrestricted.2.1

namespace Semantics

theorem SameEval.populatedInitial_eq {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    (populatedInputForm left).initial = (populatedInputForm right).initial := by
  have leftDerived := derives_sameEval which (populatedInputForm_derives left)
  have rightDerived := derives_sameEval which (populatedInputForm_derives right)
  have forms : SameEval which (bodyFormWord (populatedInputForm left)) (bodyFormWord (populatedInputForm right)) :=
    fun value => (leftDerived value).symm.trans ((same value).trans (rightDerived value))
  apply forms.simplePrefixes_eq rfl rfl
  · intro x member
    exact (leftDerived.countOne x).mp ((populatedInputForm_good left).1 x member)
  · intro x member
    exact (rightDerived.countOne x).mp ((populatedInputForm_good right).1 x member)
  · intro x tail shape one
    exact bodyPiecesWord_head_not_simple left (populatedInputForm left).pieces
      (populatedInputForm_good left).2 x tail shape ((leftDerived.countOne x).mpr one)
  · intro x tail shape one
    exact bodyPiecesWord_head_not_simple right (populatedInputForm right).pieces
      (populatedInputForm_good right).2 x tail shape ((rightDerived.countOne x).mpr one)

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.fixedPrefix_cancel
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.countOne_prefix_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.maximalSimpleBlock_of_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.MaximalSimpleBlock.eq_of_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.InitialSimpleBlock.unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.MaximalSimpleBlock.reverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.TerminalSimpleBlock.reverse_initial
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.TerminalSimpleBlock.unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.initialSimpleBlock_of_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simplePrefixes_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_head_not_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.populatedInitial_eq

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6

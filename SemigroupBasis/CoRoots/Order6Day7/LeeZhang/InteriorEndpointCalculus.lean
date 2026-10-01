import SemigroupBasis.Examples.SemilatticeTwo

/-!
# Shared interior-content and free-endpoint derivation calculus

The six primitive derivations below are proof obligations, not completeness
fields. Every caller must derive them from its own exact presentation.
The calculus abstracts the S6_1075 proof shape without importing that
semigroup's extra `xx = xxx` law. In particular, empty interiors and the
literal two-letter doubleton remain available to new consumers.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InteriorEndpoint

open SemigroupBasis
open SemigroupBasis.Examples

def framedWord (first : Nat) (interior : List Nat) (last : Nat) : Word Nat :=
  ⟨first, interior ++ [last]⟩

theorem framedWord_of_word (first last : Nat) (interior : Word Nat) :
    framedWord first interior.toList last =
      ((Word.singleton first ++ interior) ++ Word.singleton last) := rfl

private theorem split_last (first : Nat) (tail : List Nat) :
    ∃ interior last, first :: tail = interior ++ [last] := by
  induction tail generalizing first with
  | nil => exact ⟨[], first, rfl⟩
  | cons next rest ih =>
      obtain ⟨interior, last, shape⟩ := ih next
      exact ⟨first :: interior, last, by simp [shape]⟩

/-- Literal decomposition, including `xx` as a frame with empty interior.
No identity or derivational preparation is used. -/
theorem existsSingletonOrFrame (word : Word Nat) :
    (∃ letter, word = Word.singleton letter) ∨
      (∃ first interior last, word = framedWord first interior last) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil => exact Or.inl ⟨first, rfl⟩
      | cons next rest =>
          obtain ⟨interior, last, shape⟩ := split_last next rest
          exact Or.inr ⟨first, interior, last, by simp [framedWord, shape]⟩

/-- Six explicit rewrite proofs suffice for the shared calculus. -/
structure Rules (basis : List (Identity Nat)) : Prop where
  squareFinal : ∀ x y : Word Nat,
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ x) ++ y) ++ y)
  squareTransfer : ∀ x y : Word Nat,
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ y) ++ x) ++ x)
  squareInitial : ∀ x y : Word Nat,
    Derives basis (((x ++ x) ++ y) ++ x) (((y ++ x) ++ y) ++ x)
  returnDuplication : ∀ x y : Word Nat,
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ y) ++ x)
  interiorIdempotence : ∀ before middle after : Word Nat,
    Derives basis (((before ++ middle) ++ middle) ++ after) ((before ++ middle) ++ after)
  initialPairRetarget : ∀ x y z : Word Nat,
    Derives basis (((x ++ x) ++ y) ++ z) (((y ++ x) ++ y) ++ z)

namespace Rules

variable {basis : List (Identity Nat)}

/-- The extra outer letter in the middle steps is retained; no cancellation. -/
theorem derivesSquareCommutation (rules : Rules basis) (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y)) ((y ++ y) ++ (x ++ x)) := by
  have first := (rules.squareFinal x y).symm
  have second := rules.squareTransfer x y
  have third := (rules.returnDuplication x y).appendRight x
  have fourth := Derives.prepend x (rules.squareFinal y x).symm
  have fifth := (rules.returnDuplication x y).symm.appendRight y
  have sixth := (rules.squareInitial y x).symm
  have seventh := rules.squareFinal y x
  have result := first.trans (second.trans (third.trans (by
    simpa only [Word.append_assoc] using fourth.trans (by
      simpa only [Word.append_assoc] using fifth.trans (sixth.trans seventh)))))
  simpa only [Word.append_assoc] using result

/-- Condition16 is derived from the caller's primitive proofs. -/
theorem derivesInteriorCommutation (rules : Rules basis) (before left right after : Word Nat) :
    Derives basis (((before ++ left) ++ right) ++ after)
      (((before ++ right) ++ left) ++ after) := by
  have first := (rules.interiorIdempotence before left (right ++ after)).symm
  have second := (rules.interiorIdempotence ((before ++ left) ++ left) right after).symm
  have third := (Derives.prepend before (rules.derivesSquareCommutation left right)).appendRight after
  have fourth := rules.interiorIdempotence ((before ++ right) ++ right) left after
  have fifth := rules.interiorIdempotence before right (left ++ after)
  have result := first.trans (by
    simpa only [Word.append_assoc] using second.trans (by
      simpa only [Word.append_assoc] using third.trans (by
        simpa only [Word.append_assoc] using fourth.trans (by
          simpa only [Word.append_assoc] using fifth))))
  simpa only [Word.append_assoc] using result

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay every semilattice proof rule within nonempty outer contexts. -/
theorem liftSemilatticeInterior (rules : Rules basis) {left right : Word Nat}
    (derivation : Derives semilatticeBasis left right)
    (before after : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis ((before ++ left.bind substitution) ++ after)
      ((before ++ right.bind substitution) ++ after) := by
  induction derivation generalizing before after substitution with
  | fromBasis member =>
      simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [semilatticeIdempotenceLaw, semilatticeXX, semilatticeX,
          Word.bind, Word.singleton, Word.append_assoc] using
          rules.interiorIdempotence before (substitution 0) after
      · simpa [semilatticeCommutativityLaw, semilatticeXY, semilatticeYX,
          Word.bind, Word.singleton, Word.append_assoc] using
          rules.derivesInteriorCommutation before (substitution 0) (substitution 1) after
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih before after substitution).symm
  | trans _ _ first second =>
      exact (first before after substitution).trans (second before after substitution)
  | prepend outerBefore _ ih =>
      simpa only [bind_append, Word.append_assoc] using
        ih (before ++ outerBefore.bind substitution) after substitution
  | appendRight _ suffix ih =>
      simpa only [bind_append, Word.append_assoc] using
        ih before (suffix.bind substitution ++ after) substitution
  | subst _ replacement ih =>
      simpa only [bind_bind] using
        ih before after (fun letter => (replacement letter).bind substitution)

/-- Arbitrary-length interior words with equal content can be interchanged. -/
theorem derivesSameInteriorContent (rules : Rules basis) (before after left right : Word Nat)
    (content : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    Derives basis ((before ++ left) ++ after) ((before ++ right) ++ after) := by
  have expandLeft := semilatticeDerivesContentExpansion left right
    (fun letter present => (content letter).2 present)
  have expandRight := semilatticeDerivesContentExpansion right left
    (fun letter present => (content letter).1 present)
  have middle := expandLeft.trans
    ((semilatticeDerivesCommutativity left right).trans expandRight.symm)
  simpa only [bind_singleton] using
    rules.liftSemilatticeInterior middle before after Word.singleton

/-- Empty interiors are literal lists, never empty semigroup substitutions. -/
theorem derivesSameInteriorListContent (rules : Rules basis) (first last : Nat) (left right : List Nat)
    (content : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    Derives basis (framedWord first left last) (framedWord first right last) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact Derives.refl _
      | cons head tail =>
          exact False.elim (List.not_mem_nil ((content head).2 (List.Mem.head tail)))
  | cons head tail =>
      cases right with
      | nil =>
          exact False.elim (List.not_mem_nil ((content head).1 (List.Mem.head tail)))
      | cons other rest =>
          change Derives basis
            (framedWord first (Word.mk head tail).toList last)
            (framedWord first (Word.mk other rest).toList last)
          rw [framedWord_of_word, framedWord_of_word]
          exact rules.derivesSameInteriorContent (Word.singleton first) (Word.singleton last)
            (Word.mk head tail) (Word.mk other rest) content

/-- Explicit right-end retargeting, with no assumption of reversed closure. -/
theorem derivesFinalPairRetarget (rules : Rules basis) (before x y : Word Nat) :
    Derives basis (((before ++ x) ++ y) ++ y) (((before ++ x) ++ y) ++ x) := by
  have first := (rules.interiorIdempotence before x (y ++ y)).symm
  have second := Derives.prepend before (rules.derivesSquareCommutation x y)
  have third := rules.interiorIdempotence before y (x ++ x)
  have fourth := rules.derivesInteriorCommutation before y x x
  have result := first.trans (by
    simpa only [Word.append_assoc] using second.trans (by
      simpa only [Word.append_assoc] using third.trans (by
        simpa only [Word.append_assoc] using fourth)))
  simpa only [Word.append_assoc] using result

private def endingWord (letters : List Nat) (last : Nat) : Word Nat :=
  match letters with
  | [] => Word.singleton last
  | first :: rest => ⟨first, rest ++ [last]⟩

private theorem toList_endingWord (letters : List Nat) (last : Nat) :
    (endingWord letters last).toList = letters ++ [last] := by
  cases letters <;> rfl

private theorem derives_of_lists {left right actualLeft actualRight : Word Nat}
    (leftShape : left.toList = actualLeft.toList)
    (rightShape : right.toList = actualRight.toList)
    (derivation : Derives basis actualLeft actualRight) :
    Derives basis left right := by
  rw [Word.toList_injective leftShape, Word.toList_injective rightShape]
  exact derivation

theorem derivesFramedInitialRetarget (rules : Rules basis) (old new last : Nat) (interior : List Nat)
    (oldInside : old ∈ interior) (newInside : new ∈ interior) :
    Derives basis (framedWord old interior last) (framedWord new interior last) := by
  have content : ∀ letter, letter ∈ interior ↔ letter ∈ old :: new :: interior := by
    intro letter
    constructor
    · exact fun present => List.Mem.tail old (List.Mem.tail new present)
    · intro present
      simp only [List.mem_cons] at present
      rcases present with rfl | rfl | present
      · exact oldInside
      · exact newInside
      · exact present
  have first := rules.derivesSameInteriorListContent old last interior (old :: new :: interior) content
  have lastStep := rules.derivesSameInteriorListContent new last (old :: new :: interior) interior
    (fun letter => (content letter).symm)
  have primitive := rules.initialPairRetarget (Word.singleton old) (Word.singleton new)
    (endingWord interior last)
  have middle : Derives basis (framedWord old (old :: new :: interior) last)
      (framedWord new (old :: new :: interior) last) := by
    refine derives_of_lists ?_ ?_ primitive <;>
      simp only [Word.toList_append, Word.toList_singleton, toList_endingWord] <;>
      rfl
  exact first.trans (middle.trans lastStep)

theorem derivesFramedFinalRetarget (rules : Rules basis) (first old new : Nat) (interior : List Nat)
    (oldInside : old ∈ interior) (newInside : new ∈ interior) :
    Derives basis (framedWord first interior old) (framedWord first interior new) := by
  have content : ∀ letter, letter ∈ interior ↔ letter ∈ interior ++ [new, old] := by
    intro letter
    constructor
    · exact fun present => List.mem_append_left _ present
    · intro present
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with present | rfl | rfl
      · exact present
      · exact newInside
      · exact oldInside
  have firstStep := rules.derivesSameInteriorListContent first old interior (interior ++ [new, old]) content
  have lastStep := rules.derivesSameInteriorListContent first new (interior ++ [new, old]) interior
    (fun letter => (content letter).symm)
  have primitive := rules.derivesFinalPairRetarget (Word.mk first interior)
    (Word.singleton new) (Word.singleton old)
  have middle : Derives basis (framedWord first (interior ++ [new, old]) old)
      (framedWord first (interior ++ [new, old]) new) := by
    refine derives_of_lists ?_ ?_ primitive <;>
      simp [framedWord, Word.toList, List.append_assoc]
  exact firstStep.trans (middle.trans lastStep)

/-- Equal interior content and agreement of all free endpoints suffice.
This theorem does not assume any semantic completeness or finite screen. -/
theorem derivesFramedOfEndpointContent (rules : Rules basis)
    (first last otherFirst otherLast : Nat) (interior otherInterior : List Nat)
    (content : ∀ letter, letter ∈ interior ↔ letter ∈ otherInterior)
    (initial : first = otherFirst ∨ (first ∈ interior ∧ otherFirst ∈ otherInterior))
    (final : last = otherLast ∨ (last ∈ interior ∧ otherLast ∈ otherInterior)) :
    Derives basis (framedWord first interior last)
      (framedWord otherFirst otherInterior otherLast) := by
  have firstStep := rules.derivesSameInteriorListContent first last interior otherInterior content
  have initialStep : Derives basis (framedWord first otherInterior last)
      (framedWord otherFirst otherInterior last) := by
    rcases initial with rfl | ⟨oldInside, newInside⟩
    · exact Derives.refl _
    · exact rules.derivesFramedInitialRetarget first otherFirst last otherInterior
        ((content first).1 oldInside) newInside
  have finalStep : Derives basis (framedWord otherFirst otherInterior last)
      (framedWord otherFirst otherInterior otherLast) := by
    rcases final with rfl | ⟨oldInside, newInside⟩
    · exact Derives.refl _
    · exact rules.derivesFramedFinalRetarget otherFirst last otherLast otherInterior
        ((content last).1 oldInside) newInside
  exact firstStep.trans (initialStep.trans finalStep)

end Rules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InteriorEndpoint

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075Interior

/-!
# Endpoint retargeting in the exact S6_1075 presentation

Only endpoints already present in the interior can be retargeted. A free
endpoint is never erased. The two-letter doubleton is explicitly expanded
by raw law00, rather than silently included in the long-word cases.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

open SemigroupBasis

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesInitialPairRetarget (x y z : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ z) (((y ++ x) ++ y) ++ z) := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y z)

/-- The right-end analogue is derived explicitly; it is not imported by
reversing the table or assuming that the raw presentation is self-dual. -/
theorem derivesFinalPairRetarget (before x y : Word Nat) :
    Derives basis (((before ++ x) ++ y) ++ y) (((before ++ x) ++ y) ++ x) := by
  have first := (derivesInteriorIdempotence before x (y ++ y)).symm
  have second := Derives.prepend before (derivesSquareCommutation x y)
  have third := derivesInteriorIdempotence before y (x ++ x)
  have fourth := derivesInteriorCommutation before y x x
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

theorem derivesFramedInitialRetarget (old new last : Nat) (interior : List Nat)
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
  have first := derivesSameInteriorListContent old last interior (old :: new :: interior) content
  have lastStep := derivesSameInteriorListContent new last (old :: new :: interior) interior
    (fun letter => (content letter).symm)
  have primitive := derivesInitialPairRetarget (Word.singleton old) (Word.singleton new)
    (endingWord interior last)
  have middle : Derives basis (framedWord old (old :: new :: interior) last)
      (framedWord new (old :: new :: interior) last) := by
    refine derives_of_lists ?_ ?_ primitive <;>
      simp only [Word.toList_append, Word.toList_singleton, toList_endingWord] <;>
      rfl
  exact first.trans (middle.trans lastStep)

theorem derivesFramedFinalRetarget (first old new : Nat) (interior : List Nat)
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
  have firstStep := derivesSameInteriorListContent first old interior (interior ++ [new, old]) content
  have lastStep := derivesSameInteriorListContent first new (interior ++ [new, old]) interior
    (fun letter => (content letter).symm)
  have primitive := derivesFinalPairRetarget (Word.mk first interior)
    (Word.singleton new) (Word.singleton old)
  have middle : Derives basis (framedWord first (interior ++ [new, old]) old)
      (framedWord first (interior ++ [new, old]) new) := by
    refine derives_of_lists ?_ ?_ primitive <;>
      simp [framedWord, Word.toList, List.append_assoc]
  exact firstStep.trans (middle.trans lastStep)

/-- Equal interior contents and agreement of all free endpoints suffice. -/
theorem derivesFramedOfEndpointContent
    (first last otherFirst otherLast : Nat) (interior otherInterior : List Nat)
    (content : ∀ letter, letter ∈ interior ↔ letter ∈ otherInterior)
    (initial : first = otherFirst ∨ (first ∈ interior ∧ otherFirst ∈ otherInterior))
    (final : last = otherLast ∨ (last ∈ interior ∧ otherLast ∈ otherInterior)) :
    Derives basis (framedWord first interior last)
      (framedWord otherFirst otherInterior otherLast) := by
  have firstStep := derivesSameInteriorListContent first last interior otherInterior content
  have initialStep : Derives basis (framedWord first otherInterior last)
      (framedWord otherFirst otherInterior last) := by
    rcases initial with rfl | ⟨oldInside, newInside⟩
    · exact Derives.refl _
    · exact derivesFramedInitialRetarget first otherFirst last otherInterior
        ((content first).1 oldInside) newInside
  have finalStep : Derives basis (framedWord otherFirst otherInterior last)
      (framedWord otherFirst otherInterior otherLast) := by
    rcases final with rfl | ⟨oldInside, newInside⟩
    · exact Derives.refl _
    · exact derivesFramedFinalRetarget otherFirst last otherLast otherInterior
        ((content last).1 oldInside) newInside
  exact firstStep.trans (initialStep.trans finalStep)

theorem derivesDoublePreparation (letter : Nat) :
    Derives basis (framedWord letter [] letter) (framedWord letter [letter] letter) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law00, framedWord, substituteThree, Word.bind, Word.append, Word.singleton] using
    primitive.subst (substituteThree (Word.singleton letter) (Word.singleton letter) (Word.singleton letter))

/-- The exceptional short `xx` case is excluded after explicit preparation. -/
def RegularFrame (first : Nat) (interior : List Nat) (last : Nat) : Prop :=
  interior ≠ [] ∨ first ≠ last

private theorem split_last (first : Nat) (tail : List Nat) :
    ∃ interior last, first :: tail = interior ++ [last] := by
  induction tail generalizing first with
  | nil => exact ⟨[], first, rfl⟩
  | cons next rest ih =>
      obtain ⟨interior, last, shape⟩ := ih next
      exact ⟨first :: interior, last, by simp [shape]⟩

/-- Every word derives to a singleton or a regular frame; no endpoint or
singleton is silently discarded. -/
theorem existsPrepared (word : Word Nat) :
    (∃ letter, Derives basis word (Word.singleton letter)) ∨
      (∃ first interior last, RegularFrame first interior last ∧
        Derives basis word (framedWord first interior last)) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil => exact Or.inl ⟨first, Derives.refl _⟩
      | cons next rest =>
          obtain ⟨interior, last, shape⟩ := split_last next rest
          have wordShape : Word.mk first (next :: rest) = framedWord first interior last := by
            simp [framedWord, shape]
          rw [wordShape]
          by_cases regular : RegularFrame first interior last
          · exact Or.inr ⟨first, interior, last, regular, Derives.refl _⟩
          · have empty : interior = [] := by
              apply Decidable.byContradiction
              exact fun nonempty => regular (Or.inl nonempty)
            have equal : first = last := by
              apply Decidable.byContradiction
              exact fun unequal => regular (Or.inr unequal)
            subst interior
            subst last
            exact Or.inr ⟨first, [first], first, Or.inl (by simp),
              derivesDoublePreparation first⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

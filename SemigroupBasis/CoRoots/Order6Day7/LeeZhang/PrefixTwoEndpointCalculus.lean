import SemigroupBasis.Examples.SemilatticeTwo

/-!
# Shared front-content and two-endpoint derivation calculus

Three explicit rewrite obligations suffice. None is a completeness field.
The front may be empty; the literal two-letter word, including xx, is kept.
If the penultimate letter is free of the front, the final pair stays exact.
Only bound penultimate letters can be retargeted, and a bound final letter
can be retargeted only when the penultimate letter is also bound.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixTwoEndpoint

open SemigroupBasis
open SemigroupBasis.Examples

def framedWord (front : List Nat) (penultimate last : Nat) : Word Nat :=
  match front with
  | [] => ⟨penultimate, [last]⟩
  | first :: rest => ⟨first, rest ++ [penultimate, last]⟩

theorem framedWord_toList (front : List Nat) (penultimate last : Nat) :
    (framedWord front penultimate last).toList = front ++ [penultimate, last] := by
  cases front <;> rfl

theorem framedWord_of_word (front : Word Nat) (penultimate last : Nat) :
    framedWord front.toList penultimate last =
      (front ++ Word.singleton penultimate) ++ Word.singleton last := by
  apply Word.toList_injective
  simp [framedWord_toList, Word.toList_append, Word.toList_singleton, List.append_assoc]

private theorem split_two (first second : Nat) (tail : List Nat) :
    ∃ front penultimate last, first :: second :: tail = front ++ [penultimate, last] := by
  induction tail generalizing first second with
  | nil => exact ⟨[], first, second, rfl⟩
  | cons next rest ih =>
      obtain ⟨front, penultimate, last, shape⟩ := ih second next
      exact ⟨first :: front, penultimate, last, by simp [shape]⟩

theorem existsSingletonOrFrame (word : Word Nat) :
    (∃ letter, word = Word.singleton letter) ∨
      (∃ front penultimate last, word = framedWord front penultimate last) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil => exact Or.inl ⟨first, rfl⟩
      | cons second rest =>
          obtain ⟨front, penultimate, last, shape⟩ := split_two first second rest
          refine Or.inr ⟨front, penultimate, last, ?_⟩
          apply Word.toList_injective
          rw [framedWord_toList]
          exact shape

structure Rules (basis : List (Identity Nat)) : Prop where
  prefixIdempotence : ∀ x y z : Word Nat,
    Derives basis (((x ++ x) ++ y) ++ z) ((x ++ y) ++ z)
  terminalSwitch : ∀ x y : Word Nat,
    Derives basis (((x ++ y) ++ x) ++ x) (((x ++ y) ++ x) ++ y)
  terminalSwap : ∀ x y : Word Nat,
    Derives basis (((x ++ y) ++ x) ++ x) (((y ++ x) ++ x) ++ x)

namespace Rules

variable {basis : List (Identity Nat)}

theorem derivesPrefixCommutation (rules : Rules basis) (x y penultimate last : Word Nat) :
    Derives basis (((x ++ y) ++ penultimate) ++ last)
      (((y ++ x) ++ penultimate) ++ last) := by
  have first := (rules.prefixIdempotence (x ++ y) penultimate last).symm
  have second := (rules.terminalSwitch x y).symm.appendRight (penultimate ++ last)
  have third := (rules.terminalSwap x y).appendRight (penultimate ++ last)
  have fourth := Derives.prepend y (rules.prefixIdempotence x (x ++ penultimate) last)
  have fifth := Derives.prepend y (rules.prefixIdempotence x penultimate last)
  have result := first.trans (by
    simpa only [Word.append_assoc] using second.trans (third.trans (by
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

/-- Replay arbitrary semilattice derivations before two nonempty suffix words. -/
theorem liftSemilatticePrefix (rules : Rules basis) {left right : Word Nat}
    (derivation : Derives semilatticeBasis left right)
    (penultimate last : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis ((left.bind substitution ++ penultimate) ++ last)
      ((right.bind substitution ++ penultimate) ++ last) := by
  induction derivation generalizing penultimate last substitution with
  | fromBasis member =>
      simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [semilatticeIdempotenceLaw, semilatticeXX, semilatticeX,
          Word.bind, Word.singleton, Word.append_assoc] using
          rules.prefixIdempotence (substitution 0) penultimate last
      · simpa [semilatticeCommutativityLaw, semilatticeXY, semilatticeYX,
          Word.bind, Word.singleton, Word.append_assoc] using
          rules.derivesPrefixCommutation (substitution 0) (substitution 1) penultimate last
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih penultimate last substitution).symm
  | trans _ _ first second =>
      exact (first penultimate last substitution).trans (second penultimate last substitution)
  | prepend before _ ih =>
      simpa only [bind_append, Word.append_assoc] using
        Derives.prepend (before.bind substitution) (ih penultimate last substitution)
  | appendRight _ suffix ih =>
      simpa only [bind_append, Word.append_assoc] using
        ih (suffix.bind substitution ++ penultimate) last substitution
  | subst _ replacement ih =>
      simpa only [bind_bind] using
        ih penultimate last (fun letter => (replacement letter).bind substitution)

theorem derivesSamePrefixContent (rules : Rules basis) (left right penultimate last : Word Nat)
    (content : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    Derives basis ((left ++ penultimate) ++ last) ((right ++ penultimate) ++ last) := by
  have expandLeft := semilatticeDerivesContentExpansion left right
    (fun letter present => (content letter).2 present)
  have expandRight := semilatticeDerivesContentExpansion right left
    (fun letter present => (content letter).1 present)
  have middle := expandLeft.trans
    ((semilatticeDerivesCommutativity left right).trans expandRight.symm)
  simpa only [bind_singleton] using
    rules.liftSemilatticePrefix middle penultimate last Word.singleton

theorem derivesSamePrefixListContent (rules : Rules basis) (left right : List Nat) (penultimate last : Nat)
    (content : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    Derives basis (framedWord left penultimate last) (framedWord right penultimate last) := by
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
            (framedWord (Word.mk head tail).toList penultimate last)
            (framedWord (Word.mk other rest).toList penultimate last)
          rw [framedWord_of_word, framedWord_of_word]
          exact rules.derivesSamePrefixContent (Word.mk head tail) (Word.mk other rest)
            (Word.singleton penultimate) (Word.singleton last) content

private theorem content_append (front extra : List Nat)
    (included : ∀ letter, letter ∈ extra → letter ∈ front) :
    ∀ letter, letter ∈ front ↔ letter ∈ front ++ extra := by
  intro letter
  constructor
  · exact List.mem_append_left _
  · intro member
    rcases List.mem_append.mp member with member | member
    · exact member
    · exact included letter member

private theorem derives_of_lists {left right actualLeft actualRight : Word Nat}
    (leftShape : left.toList = actualLeft.toList)
    (rightShape : right.toList = actualRight.toList)
    (derivation : Derives basis actualLeft actualRight) :
    Derives basis left right := by
  rw [Word.toList_injective leftShape, Word.toList_injective rightShape]
  exact derivation

theorem derivesPenultimateRetarget (rules : Rules basis) (front : List Nat) (old new last : Nat)
    (oldInside : old ∈ front) (newInside : new ∈ front) :
    Derives basis (framedWord front old last) (framedWord front new last) := by
  cases front with
  | nil => simp at oldInside
  | cons head tail =>
      have content := content_append (head :: tail) [old, new, old] (by
        intro letter member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact oldInside
        · exact newInside
        · exact oldInside)
      have first := rules.derivesSamePrefixListContent (head :: tail)
        ((head :: tail) ++ [old, new, old]) old last content
      have finish := rules.derivesSamePrefixListContent
        ((head :: tail) ++ [old, new, old]) (head :: tail) new last (fun letter => (content letter).symm)
      have primitive := Derives.prepend (Word.mk head tail)
        ((rules.terminalSwitch (Word.singleton old) (Word.singleton new)).appendRight (Word.singleton last))
      have middle : Derives basis
          (framedWord ((head :: tail) ++ [old, new, old]) old last)
          (framedWord ((head :: tail) ++ [old, new, old]) new last) := by
        refine derives_of_lists ?_ ?_ primitive <;>
          simp only [framedWord_toList, Word.toList_append, Word.toList_singleton, List.append_assoc] <;> rfl
      exact first.trans (middle.trans finish)

theorem derivesBoundFinalRetarget (rules : Rules basis) (front : List Nat) (penultimate old new : Nat)
    (penultimateInside : penultimate ∈ front) (oldInside : old ∈ front) (newInside : new ∈ front) :
    Derives basis (framedWord front penultimate old) (framedWord front penultimate new) := by
  cases front with
  | nil => simp at oldInside
  | cons head tail =>
      have penultimateFirst := rules.derivesPenultimateRetarget (head :: tail)
        penultimate old old penultimateInside oldInside
      have penultimateLast := rules.derivesPenultimateRetarget (head :: tail)
        old penultimate new oldInside penultimateInside
      have content := content_append (head :: tail) [old, new] (by
        intro letter member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact oldInside
        · exact newInside)
      have first := rules.derivesSamePrefixListContent (head :: tail)
        ((head :: tail) ++ [old, new]) old old content
      have finish := rules.derivesSamePrefixListContent
        ((head :: tail) ++ [old, new]) (head :: tail) old new (fun letter => (content letter).symm)
      have primitive := Derives.prepend (Word.mk head tail)
        (rules.terminalSwitch (Word.singleton old) (Word.singleton new))
      have middle : Derives basis
          (framedWord ((head :: tail) ++ [old, new]) old old)
          (framedWord ((head :: tail) ++ [old, new]) old new) := by
        refine derives_of_lists ?_ ?_ primitive <;>
          simp only [framedWord_toList, Word.toList_append, Word.toList_singleton, List.append_assoc] <;> rfl
      exact penultimateFirst.trans (first.trans (middle.trans (finish.trans penultimateLast)))

/-- A free penultimate letter forces an exact final pair, not just a free-last key. -/
theorem derivesFramesOfPrefixEndpoint (rules : Rules basis)
    (front otherPrefix : List Nat) (penultimate last otherPenultimate otherLast : Nat)
    (content : ∀ letter, letter ∈ front ↔ letter ∈ otherPrefix)
    (penultimateKey : penultimate = otherPenultimate ∨
      (penultimate ∈ front ∧ otherPenultimate ∈ otherPrefix))
    (lastKey : last = otherLast ∨ (penultimate ∈ front ∧ otherPenultimate ∈ otherPrefix ∧
      last ∈ front ∧ otherLast ∈ otherPrefix)) :
    Derives basis (framedWord front penultimate last)
      (framedWord otherPrefix otherPenultimate otherLast) := by
  have first := rules.derivesSamePrefixListContent front otherPrefix penultimate last content
  have penultimateStep : Derives basis (framedWord otherPrefix penultimate last)
      (framedWord otherPrefix otherPenultimate last) := by
    rcases penultimateKey with rfl | ⟨oldInside, newInside⟩
    · exact Derives.refl _
    · exact rules.derivesPenultimateRetarget otherPrefix penultimate otherPenultimate last
        ((content penultimate).1 oldInside) newInside
  have lastStep : Derives basis (framedWord otherPrefix otherPenultimate last)
      (framedWord otherPrefix otherPenultimate otherLast) := by
    rcases lastKey with rfl | ⟨_, penultimateInside, oldInside, newInside⟩
    · exact Derives.refl _
    · exact rules.derivesBoundFinalRetarget otherPrefix otherPenultimate last otherLast
        penultimateInside ((content last).1 oldInside) newInside
  exact first.trans (penultimateStep.trans lastStep)

end Rules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixTwoEndpoint

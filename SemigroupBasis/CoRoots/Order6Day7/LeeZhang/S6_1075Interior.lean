import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075Presentation
import SemigroupBasis.Examples.SemilatticeTwo

/-!
# Unrestricted interior-content calculus for S6_1075

Condition 16 is DERIVED from the unchanged raw10 presentation. In particular,
it is not supplied by the historical packet's completeness label. Both outer
contexts are nonempty semigroup words throughout. Inside them, the existing
semilattice derivation calculus can be replayed with arbitrary nonempty-word
substitutions. This removes the bounded-alphabet and bounded-length limits.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

open SemigroupBasis
open SemigroupBasis.Examples

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesSquareFinal (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ x) ++ y) ++ y) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law01, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesSquareTransfer (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law02, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesSquareInitial (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((y ++ x) ++ y) ++ x) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law03, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesReturnDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ y) ++ x) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law07, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

/-- The raw `xyyz = xyz` allows contraction of any interior word block. -/
theorem derivesInteriorIdempotence (before middle after : Word Nat) :
    Derives basis (((before ++ middle) ++ middle) ++ after)
      ((before ++ middle) ++ after) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law08, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree before middle after)

/-- `xxyy -> xxyx -> xyxx -> xyyxx -> xyyxy -> xyxy -> yyxy -> yyxx`.
The middle two steps retain the extra outer letter; no cancellation occurs. -/
theorem derivesSquareCommutation (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y)) ((y ++ y) ++ (x ++ x)) := by
  have first := (derivesSquareFinal x y).symm
  have second := derivesSquareTransfer x y
  have third := (derivesReturnDuplication x y).appendRight x
  have fourth := Derives.prepend x (derivesSquareFinal y x).symm
  have fifth := (derivesReturnDuplication x y).symm.appendRight y
  have sixth := (derivesSquareInitial y x).symm
  have seventh := derivesSquareFinal y x
  have result := first.trans (second.trans (third.trans (by
    simpa only [Word.append_assoc] using fourth.trans (by
      simpa only [Word.append_assoc] using fifth.trans (sixth.trans seventh)))))
  simpa only [Word.append_assoc] using result

/-- Literal Condition 16, obtained by duplicating the two middle blocks,
commuting their squares, and contracting the two duplicates. -/
theorem derivesInteriorCommutation (before left right after : Word Nat) :
    Derives basis (((before ++ left) ++ right) ++ after)
      (((before ++ right) ++ left) ++ after) := by
  have first := (derivesInteriorIdempotence before left (right ++ after)).symm
  have second := (derivesInteriorIdempotence ((before ++ left) ++ left) right after).symm
  have third := (Derives.prepend before (derivesSquareCommutation left right)).appendRight after
  have fourth := derivesInteriorIdempotence ((before ++ right) ++ right) left after
  have fifth := derivesInteriorIdempotence before right (left ++ after)
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

/-- Replay the full existing semilattice proof calculus inside arbitrary
nonempty outer contexts, including every substitution and context rule. -/
theorem liftSemilatticeInterior {left right : Word Nat}
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
          derivesInteriorIdempotence before (substitution 0) after
      · simpa [semilatticeCommutativityLaw, semilatticeXY, semilatticeYX,
          Word.bind, Word.singleton, Word.append_assoc] using
          derivesInteriorCommutation before (substitution 0) (substitution 1) after
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

/-- Equal interior contents suffice under fixed nonempty outer contexts.
No length or variable-count restriction remains in this theorem. -/
theorem derivesSameInteriorContent (before after left right : Word Nat)
    (content : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    Derives basis ((before ++ left) ++ after) ((before ++ right) ++ after) := by
  have expandLeft := semilatticeDerivesContentExpansion left right
    (fun letter present => (content letter).2 present)
  have expandRight := semilatticeDerivesContentExpansion right left
    (fun letter present => (content letter).1 present)
  have middle := expandLeft.trans
    ((semilatticeDerivesCommutativity left right).trans expandRight.symm)
  simpa only [bind_singleton] using
    liftSemilatticeInterior middle before after Word.singleton

/-- An interior list can be empty, but no empty semigroup substitution is used. -/
def framedWord (first : Nat) (interior : List Nat) (last : Nat) : Word Nat :=
  ⟨first, interior ++ [last]⟩

theorem framedWord_of_word (first last : Nat) (interior : Word Nat) :
    framedWord first interior.toList last =
      ((Word.singleton first ++ interior) ++ Word.singleton last) := rfl

/-- List form, retaining the literal two-letter case when both interiors
are empty. This is the normalization interface for the endpoint analysis. -/
theorem derivesSameInteriorListContent (first last : Nat) (left right : List Nat)
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
          exact derivesSameInteriorContent (Word.singleton first) (Word.singleton last)
            (Word.mk head tail) (Word.mk other rest) content

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

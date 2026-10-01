import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Rank006 Sigma+: unrestricted period and return-block macros

Every displayed step is a literal member of the reviewed thirteen-law
basis, checked with `decide`, instantiated with nonempty words, and chained
through explicitly typed intermediates. No lower S4_69 law is retargeted.

In particular, the single new bridge supplies all three period insertions
in a return x y x. It also turns a return into a product of powered blocks.
Squaring and fourth powers distribute over arbitrary words. These are
unbounded normalization ingredients, not a completeness assertion.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.S5_107

def square (word : Word Nat) : Word Nat := word ++ word
def cube (word : Word Nat) : Word Nat := (word ++ word) ++ word
def fourth (word : Word Nat) : Word Nat := ((word ++ word) ++ word) ++ word
def fifth (word : Word Nat) : Word Nat := (((word ++ word) ++ word) ++ word) ++ word

private def instantiate (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesSquarePeriod (word : Word Nat) :
    Derives sigmaPlus (square word) (fifth word) := by
  have primitive : Derives sigmaPlus (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0, 0]⟩) (by decide)
  have substituted := primitive.subst (fun _ => word)
  simpa [square, fifth, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesCubeTransfer (first second : Word Nat) :
    Derives sigmaPlus ((cube first ++ second) ++ first)
      ((second ++ first) ++ cube second) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1]) :=
    Derives.fromBasis
      (e := ⟨Word.mk 0 [0, 0, 1, 0], Word.mk 1 [0, 1, 1, 1]⟩) (by decide)
  have substituted := primitive.subst (instantiate first second second)
  simpa [cube, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesSquareSlide (first second : Word Nat) :
    Derives sigmaPlus ((square first ++ second) ++ first)
      ((first ++ second) ++ square first) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0, 0]⟩) (by decide)
  have substituted := primitive.subst (instantiate first second second)
  simpa [square, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesSquareAppend (first second : Word Nat) :
    Derives sigmaPlus (square (first ++ second)) (square first ++ square second) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [1, 0, 1]) (Word.mk 0 [0, 1, 1]) :=
    (Derives.fromBasis
      (e := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 1]⟩) (by decide)).symm
  have substituted := primitive.subst (instantiate first second second)
  simpa [square, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesSquaresEnclose (first second : Word Nat) :
    Derives sigmaPlus (square first ++ square second)
      ((first ++ square second) ++ first) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩) (by decide)
  have substituted := primitive.subst (instantiate first second second)
  simpa [square, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesSquaresRotate (first second : Word Nat) :
    Derives sigmaPlus (square first ++ square second)
      ((second ++ square first) ++ second) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) :=
    Derives.fromBasis (e := ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩) (by decide)
  have substituted := primitive.subst (instantiate first second second)
  simpa [square, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesInteriorSwap (outer first second : Word Nat) :
    Derives sigmaPlus (((outer ++ first) ++ second) ++ outer)
      (((outer ++ second) ++ first) ++ outer) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [2, 1, 0]⟩) (by decide)
  have substituted := primitive.subst (instantiate outer first second)
  simpa [instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

theorem derivesReturnLeftPeriod (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer)
      ((fourth outer ++ middle) ++ outer) := by
  have primitive :
      Derives sigmaPlus (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]) :=
    Derives.fromBasis (e := Rank006Raw12Obstruction.missingLaw) bridge_member
  have substituted := primitive.subst (instantiate outer middle middle)
  simpa [fourth, instantiate, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

/-- The right-hand bridge is derived, not added to the basis. -/
theorem derivesReturnRightPeriod (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer)
      ((outer ++ middle) ++ fourth outer) := by
  have first : Derives sigmaPlus
      ((fourth outer ++ middle) ++ outer)
      ((cube outer ++ middle) ++ square outer) := by
    simpa only [fourth, cube, square, Word.append_assoc] using
      Derives.prepend (square outer) (derivesSquareSlide outer middle)
  have second : Derives sigmaPlus
      ((cube outer ++ middle) ++ square outer)
      ((square outer ++ middle) ++ cube outer) := by
    simpa only [cube, square, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend outer (derivesSquareSlide outer middle)) outer
  have third : Derives sigmaPlus
      ((square outer ++ middle) ++ cube outer)
      ((outer ++ middle) ++ fourth outer) := by
    simpa only [fourth, cube, square, Word.append_assoc] using
      Derives.appendRight (derivesSquareSlide outer middle) (square outer)
  exact (derivesReturnLeftPeriod outer middle).trans
    (first.trans (second.trans third))

/-- A return is a product of powered blocks with exactly the same residues. -/
theorem derivesReturnToPoweredSquares (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer)
      (square outer ++ fourth middle) := by
  have transfer : Derives sigmaPlus
      ((fourth outer ++ middle) ++ outer)
      (((outer ++ middle) ++ outer) ++ cube middle) := by
    simpa only [fourth, cube, Word.append_assoc] using
      Derives.prepend outer (derivesCubeTransfer outer middle)
  have collect : Derives sigmaPlus
      (((outer ++ middle) ++ outer) ++ cube middle)
      (square outer ++ fourth middle) := by
    simpa only [fourth, cube, square, Word.append_assoc] using
      Derives.appendRight (derivesSquareAppend outer middle) (square middle)
  exact (derivesReturnLeftPeriod outer middle).trans (transfer.trans collect)

/-- Interior period absorption follows by an explicit four-step chain. -/
theorem derivesReturnMiddlePeriod (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer)
      ((outer ++ fourth middle) ++ outer) := by
  have enclose : Derives sigmaPlus
      (square outer ++ fourth middle)
      ((outer ++ fourth middle) ++ outer) := by
    simpa only [fourth, square, Word.append_assoc] using
      derivesSquaresEnclose outer (square middle)
  exact (derivesReturnToPoweredSquares outer middle).trans enclose

theorem derivesSquaresCommute (first second : Word Nat) :
    Derives sigmaPlus (square first ++ square second)
      (square second ++ square first) :=
  (derivesSquaresRotate first second).trans (derivesSquaresEnclose second first).symm

/-- Historical bridge aaaabb = bab is a consequence of Sigma+, not law 14. -/
theorem derivesFourthSquareToReturn (first second : Word Nat) :
    Derives sigmaPlus (fourth first ++ square second) ((second ++ first) ++ second) := by
  have rotate : Derives sigmaPlus
      (fourth first ++ square second) ((second ++ fourth first) ++ second) := by
    simpa only [fourth, square, Word.append_assoc] using
      derivesSquaresRotate (square first) second
  exact rotate.trans (derivesReturnMiddlePeriod second first).symm

theorem derivesSquareCongr {first second : Word Nat}
    (derivation : Derives sigmaPlus first second) :
    Derives sigmaPlus (square first) (square second) :=
  (Derives.appendRight derivation first).trans (Derives.prepend second derivation)

theorem derivesFourthAppend (first second : Word Nat) :
    Derives sigmaPlus (fourth (first ++ second)) (fourth first ++ fourth second) := by
  have distribute : Derives sigmaPlus
      (square (square (first ++ second))) (square (square first ++ square second)) :=
    derivesSquareCongr (derivesSquareAppend first second)
  have collect : Derives sigmaPlus
      (square (square first ++ square second))
      (square (square first) ++ square (square second)) :=
    derivesSquareAppend (square first) (square second)
  simpa only [fourth, square, Word.append_assoc] using distribute.trans collect

private theorem bind_append (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution = first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- A fourth power expands into letter fourth-powers for ANY nonempty word. -/
theorem derivesFourthLetterwise (word : Word Nat) :
    Derives sigmaPlus (fourth word)
      (word.bind (fun letter => fourth (Word.singleton letter))) := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil => exact Derives.refl _
      | cons next rest induction =>
          change Derives sigmaPlus (fourth (Word.singleton head ++ Word.mk next rest))
            ((Word.singleton head ++ Word.mk next rest).bind
              (fun letter => fourth (Word.singleton letter)))
          rw [bind_append]
          have first := derivesFourthAppend (Word.singleton head) (Word.mk next rest)
          have second := Derives.prepend (fourth (Word.singleton head)) (induction next)
          exact first.trans second

/-- Return-block flattening carries actual unbounded word derivations. -/
theorem derivesReturnLetterwise (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer)
      (square outer ++ middle.bind (fun letter => fourth (Word.singleton letter))) :=
  (derivesReturnToPoweredSquares outer middle).trans
    (Derives.prepend (square outer) (derivesFourthLetterwise middle))

/-- A repeated initial letter admits its three extra copies before any
remaining suffix; the gap and suffix may be empty. -/
theorem derivesRepeatedInitialPeriod (head : Nat) (tail : List Nat)
    (repeated : head ∈ tail) :
    Derives sigmaPlus (Word.mk head tail)
      (Word.mk head (head :: head :: head :: tail)) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp repeated
  subst tail
  have core : ListDerives sigmaPlus
      ((head :: before) ++ [head]) ((head :: head :: head :: head :: before) ++ [head]) := by
    cases before with
    | nil =>
        simpa [square, fifth, Word.singleton, Word.append] using
          ListDerives.ofWord (derivesSquarePeriod (Word.singleton head))
    | cons first rest =>
        simpa [fourth, Word.singleton, Word.append, List.append_assoc] using
          ListDerives.ofWord
            (derivesReturnLeftPeriod (Word.singleton head) (Word.mk first rest))
  have contextual : ListDerives sigmaPlus
      (head :: (before ++ head :: after))
      (head :: head :: head :: head :: (before ++ head :: after)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using core.append after
  exact contextual.toWord

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros

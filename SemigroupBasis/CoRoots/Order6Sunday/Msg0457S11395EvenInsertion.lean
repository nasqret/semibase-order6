import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Signature
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Actual B12 normalization steps. An even block may move inside two
occurrences of its letter. The sentinels remain present; this is not a
license to permute first introductions or arbitrary repeated gaps. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395EvenInsertion

open SemigroupBasis
open Msg0457S11395Semantics

abbrev LD := S5_107.ListDerives basis

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesSquare : Derives basis law00.lhs law00.rhs :=
  Derives.fromBasis (by decide)

theorem derivesLeftPair : Derives basis law01.lhs law01.rhs :=
  Derives.fromBasis (by decide)

theorem derivesRightPair : Derives basis law02.lhs law02.rhs :=
  Derives.fromBasis (by decide)

theorem derivesInteriorPair : Derives basis law09.lhs law09.rhs :=
  Derives.fromBasis (by decide)

/-- Both interior gaps may be empty. Substitutions themselves remain nonempty. -/
theorem insertPairBetween (letter : Nat) (before after : List Nat) :
    LD ([letter] ++ before ++ after ++ [letter])
      ([letter] ++ before ++ [letter,letter] ++ after ++ [letter]) := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesSquare.subst
            (threeWords (Word.singleton letter) (Word.singleton letter) (Word.singleton letter)))
          simp only [Word.toList_bind] at proof
          simpa [law00, threeWords, Word.toList, Word.singleton] using proof
      | cons head tail =>
          have proof := S5_107.ListDerives.ofWord (derivesLeftPair.subst
            (threeWords (Word.singleton letter) (S5_107.listWordOfCons head tail)
              (Word.singleton letter)))
          simp only [Word.toList_bind] at proof
          simpa [law01, threeWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
  | cons head tail =>
      cases after with
      | nil =>
          have proof := S5_107.ListDerives.ofWord (derivesRightPair.subst
            (threeWords (Word.singleton letter) (S5_107.listWordOfCons head tail)
              (Word.singleton letter)))
          simp only [Word.toList_bind] at proof
          simpa [law02, threeWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof
      | cons next rest =>
          have proof := S5_107.ListDerives.ofWord (derivesInteriorPair.subst
            (threeWords (Word.singleton letter) (S5_107.listWordOfCons head tail)
              (S5_107.listWordOfCons next rest)))
          simp only [Word.toList_bind] at proof
          simpa [law09, threeWords, Word.toList, Word.singleton,
            S5_107.listWordOfCons, List.append_assoc] using proof

theorem contextualInsertPair (prefixWords before after suffix : List Nat) (letter : Nat) :
    LD (prefixWords ++ [letter] ++ before ++ after ++ [letter] ++ suffix)
      (prefixWords ++ [letter] ++ before ++ [letter,letter] ++ after ++ [letter] ++ suffix) := by
  simpa [List.append_assoc] using (insertPairBetween letter before after).context prefixWords suffix

/-- A pair crosses an arbitrary word, but never crosses either sentinel. -/
theorem movePairBetween (letter : Nat) (before middle after : List Nat) :
    LD ([letter] ++ before ++ [letter,letter] ++ middle ++ after ++ [letter])
      ([letter] ++ before ++ middle ++ [letter,letter] ++ after ++ [letter]) := by
  have erase := (insertPairBetween letter before (middle ++ after)).symm
  have insert := insertPairBetween letter (before ++ middle) after
  have erased : LD ([letter] ++ before ++ [letter,letter] ++ middle ++ after ++ [letter])
      ([letter] ++ before ++ middle ++ after ++ [letter]) := by
    simpa [List.append_assoc] using erase
  exact erased.trans (by simpa [List.append_assoc] using insert)

theorem replicateAdd (first second letter : Nat) :
    List.replicate (first + second) letter =
      List.replicate first letter ++ List.replicate second letter := by
  induction first with
  | zero => simp
  | succ first ih => simpa [Nat.succ_add, List.replicate_succ] using congrArg (List.cons letter) ih

theorem insertEvenBetween (letter : Nat) (before after : List Nat) (pairs : Nat) :
    LD ([letter] ++ before ++ after ++ [letter])
      ([letter] ++ before ++ List.replicate (2 * pairs) letter ++ after ++ [letter]) := by
  induction pairs with
  | zero => simpa using S5_107.ListDerives.refl (basis := basis) ([letter] ++ before ++ after ++ [letter])
  | succ pairs ih =>
      have step := insertPairBetween letter (before ++ List.replicate (2 * pairs) letter) after
      apply ih.trans
      simpa [Nat.mul_add, replicateAdd, List.append_assoc] using step

/-- Every anchored run reduces to zero or one copy, preserving its parity. -/
theorem normalizeAnchoredRun (letter : Nat) (before after : List Nat) (copies : Nat) :
    LD ([letter] ++ before ++ List.replicate copies letter ++ after ++ [letter])
      ([letter] ++ before ++ List.replicate (copies % 2) letter ++ after ++ [letter]) := by
  have split : copies % 2 + 2 * (copies / 2) = copies := Nat.mod_add_div copies 2
  have inserted := insertEvenBetween letter (before ++ List.replicate (copies % 2) letter) after (copies / 2)
  have joined : List.replicate (copies % 2) letter ++ List.replicate (2 * (copies / 2)) letter =
      List.replicate copies letter := by
    rw [← replicateAdd, split]
  rw [← joined]
  simpa only [List.append_assoc] using inserted.symm

theorem contextualNormalizeRun (prefixWords before after suffix : List Nat) (letter copies : Nat) :
    LD (prefixWords ++ [letter] ++ before ++ List.replicate copies letter ++ after ++ [letter] ++ suffix)
      (prefixWords ++ [letter] ++ before ++ List.replicate (copies % 2) letter ++ after ++ [letter] ++ suffix) := by
  simpa [List.append_assoc] using (normalizeAnchoredRun letter before after copies).context prefixWords suffix

/-- The bounded precheck is not a premise of this actual B12 derivation. -/
theorem normalizeRunWord (letter : Nat) (before after : List Nat) (copies : Nat) :
    Derives basis
      ⟨letter, before ++ List.replicate copies letter ++ after ++ [letter]⟩
      ⟨letter, before ++ List.replicate (copies % 2) letter ++ after ++ [letter]⟩ := by
  exact (show LD
    (letter :: (before ++ List.replicate copies letter ++ after ++ [letter]))
    (letter :: (before ++ List.replicate (copies % 2) letter ++ after ++ [letter])) from
      by simpa [List.append_assoc] using normalizeAnchoredRun letter before after copies).toWord

theorem normalizeRunPreservesSignature (letter : Nat) (before after : List Nat) (copies : Nat) :
    Msg0457S11395Observations.SameSignature
      ⟨letter, before ++ List.replicate copies letter ++ after ++ [letter]⟩
      ⟨letter, before ++ List.replicate (copies % 2) letter ++ after ++ [letter]⟩ :=
  Msg0457S11395Signature.derives_preserve_signature (normalizeRunWord letter before after copies)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395EvenInsertion

import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank013
import SemigroupBasis.Generated.S4_95

/-!
# Exact two-block initial-guard lift for S3_4 × S4_95 rank 013

The complete parity-initial lower calculus has `x = x³`, so the protected
bare-square strategy used for S4_69/S4_71 is false here.  Instead its two
axioms lift after any two fixed nonempty initial blocks.  Every word of
length at least three accepts two copies of its existing initial letter by
the frozen `xxxyz = xyz` law.  Equal initial letters therefore splice the
guarded complete lower derivation between two exact expansion/contraction
witnesses, without altering either unrestricted endpoint.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_95

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank013.basis

private abbrev lowerBasis : List (Identity Nat) := parityInitialBasis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Frozen `xyz = xyzzz` lifts `z = z³` after two nonempty blocks. -/
theorem derivesParityPowerUnderTwoPrefixes
    (first second block : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ block)
      ((((first ++ second) ++ block) ++ block) ++ block) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 2]) (Word.mk 0 [1, 2, 2, 2]) :=
    Derives.fromBasis (e := Rank013.law09)
      (show Rank013.law09 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxy = xyx` to obtain the exact parity gather law. -/
theorem derivesParityGather (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      ((first ++ first) ++ second) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank013.law06)
      (show Rank013.law06 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxxyz = xyz` to insert two initial block copies. -/
theorem derivesDoubleInitialExpansion
    (first second third : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ third)
      ((((first ++ first) ++ first) ++ second) ++ third) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank013.law04)
      (show Rank013.law04 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete two-law parity derivation after any two blocks. -/
theorem liftParityUnderTwoPrefixes
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (first second : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ left.bind substitution)
      ((first ++ second) ++ right.bind substitution) := by
  induction derivation generalizing first second substitution with
  | fromBasis member =>
      simp only [parityInitialBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityInitialPowerLaw, parityInitialX,
          parityInitialXXX, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          derivesParityPowerUnderTwoPrefixes
            first second (substitution 0)
      · simpa [parityInitialGatherLaw, parityInitialXYX,
          parityInitialXXY, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          Derives.prepend (first ++ second)
            (derivesParityGather (substitution 0) (substitution 1))
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact (induction first second substitution).symm
  | trans _ _ leftInduction rightInduction =>
      exact
        (leftInduction first second substitution).trans
          (rightInduction first second substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction first
          (second ++ stem.bind substitution) substitution
  | appendRight _ ending induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction first second substitution)
          (ending.bind substitution)
  | subst _ next induction =>
      simpa only [bind_bind] using
        induction first second
          (fun letter => (next letter).bind substitution)

/-- Every long word accepts exactly two copies of its own initial letter. -/
theorem derivesDoubleInitialExpansionOfLong
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives targetBasis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third remainder =>
              let initial := Word.singleton first
              let middle := Word.singleton second
              let ending := Word.mk third remainder
              simpa [initial, middle, ending, Word.singleton, Word.append,
                Word.append_assoc] using
                derivesDoubleInitialExpansion initial middle ending

/-- Common initial letters remove both guard insertions after parity lifting. -/
theorem derivesLongOfLowerAndSameInitial
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (sameInitial : left.head = right.head) :
    Derives targetBasis left right := by
  have expandedLeft := derivesDoubleInitialExpansionOfLong left leftLong
  have expandedRight :
      Derives targetBasis right
        ((Word.singleton left.head ++ Word.singleton left.head) ++ right) := by
    simpa [sameInitial] using
      derivesDoubleInitialExpansionOfLong right rightLong
  have lifted :=
    liftParityUnderTwoPrefixes derivation
      (Word.singleton left.head) (Word.singleton left.head)
      Word.singleton
  have aligned :
      Derives targetBasis
        ((Word.singleton left.head ++ Word.singleton left.head) ++ left)
        ((Word.singleton left.head ++ Word.singleton left.head) ++ right) := by
    simpa only [bind_singleton] using lifted
  exact expandedLeft.trans (aligned.trans expandedRight.symm)

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_95

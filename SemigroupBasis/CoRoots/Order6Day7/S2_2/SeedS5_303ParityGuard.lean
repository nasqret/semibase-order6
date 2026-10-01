import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038
import SemigroupBasis.CoRoots.S5_303Completeness
import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.Examples.CommutativeParityThree

/-!
# Parity-preserving protected-terminal calculus for `S2_2 × S5_303`

The complete `S5_303` normalizer duplicates a prefix once; that operation
changes cyclic-two occurrence parity and cannot be imported into the frozen
four-law intersection.  Instead, the actual staged `xxxy = xy` expands the
protected marker by TWO copies.  The independently reviewed rotation and
interior transposition then derive full prefix commutation while preserving
both terminal positions.  Consequently the kernel-green commutative-parity
calculus lifts before two explicit nonempty terminal guards.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

private abbrev terminalPair :=
  SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | index + 3 => Word.singleton (index + 3)

/-- The displayed four-law target contracts three leading copies to one,
preserving every occurrence parity. -/
theorem derivesTriplePrefixContraction (first guard : Word Nat) :
    Derives basis
      (((first ++ first) ++ first) ++ guard)
      (first ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1]) (Word.mk 0 [1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first guard guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen `xyx = yxx` rotates an independently repeated marker. -/
theorem derivesRotate (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      ((second ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen `xyzx = xzyx` exchanges blocks strictly inside a repeated guard. -/
theorem derivesInteriorSwap (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Prefix commutation retains BOTH actual terminal guards.  Unlike the
ordinary `S5_303` proof, the temporary guard expands by TWO copies, so every
edge is valid in the independently required cyclic-two factor. -/
theorem derivesPrefixSwap
    (first second penultimate final : Word Nat) :
    Derives basis
      (((first ++ second) ++ penultimate) ++ final)
      (((second ++ first) ++ penultimate) ++ final) := by
  have duplicate :=
    Derives.prepend (first ++ second)
      (derivesTriplePrefixContraction penultimate final).symm
  have moveLeft :=
    Derives.appendRight
      (derivesRotate penultimate (first ++ second)).symm
      (penultimate ++ final)
  have swapMiddle :=
    Derives.appendRight
      (derivesInteriorSwap penultimate first second)
      (penultimate ++ final)
  have moveRight :=
    Derives.appendRight
      (derivesRotate penultimate (second ++ first))
      (penultimate ++ final)
  have contract :=
    Derives.prepend (second ++ first)
      (derivesTriplePrefixContraction penultimate final)
  apply Derives.trans
  · simpa [Word.append_assoc] using duplicate
  · apply Derives.trans
    · simpa [Word.append_assoc] using moveLeft
    · apply Derives.trans
      · simpa [Word.append_assoc] using swapMiddle
      · apply Derives.trans
        · simpa [Word.append_assoc] using moveRight
        · simpa [Word.append_assoc] using contract

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

/-- The complete commutative positive-parity calculus lifts BEFORE two actual
terminal guards.  Arbitrary substitutions and every derivation constructor
retain both nonempty protected blocks. -/
theorem liftParityBeforeFinalPair
    {left right : Word Nat}
    (derivation : Derives commutativeParityBasis left right)
    (penultimate final : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basis
      ((left.bind substitution ++ penultimate) ++ final)
      ((right.bind substitution ++ penultimate) ++ final) := by
  induction derivation generalizing penultimate final substitution with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          (derivesTriplePrefixContraction
            (substitution 0) (penultimate ++ final)).symm
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesPrefixSwap
            (substitution 0) (substitution 1) penultimate final
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction penultimate final substitution).symm
  | trans _ _ first second =>
      exact
        (first penultimate final substitution).trans
          (second penultimate final substitution)
  | prepend front _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend
          (front.bind substitution)
          (induction penultimate final substitution)
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        induction
          (suffix.bind substitution ++ penultimate)
          final substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction penultimate final
          (fun letter => (next letter).bind substitution)

/-- Every actual permutation of the prefix is parity-preserving and derivable
while the literal final pair remains unchanged. -/
theorem derivesPrefixPermutation
    {leftPrefix rightPrefix : List Nat}
    (permutation : leftPrefix.Perm rightPrefix)
    (penultimate final : Nat) :
    Derives basis
      (terminalPair leftPrefix penultimate final)
      (terminalPair rightPrefix penultimate final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      simpa [terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton letter) induction
  | swap first second rest =>
      have swapped :=
        derivesPrefixSwap
          (Word.singleton second) (Word.singleton first)
          (wordOfPrefixFinal rest penultimate)
          (Word.singleton final)
      have leftRendered :
          (((Word.singleton second ++ Word.singleton first) ++
              wordOfPrefixFinal rest penultimate) ++ Word.singleton final) =
            terminalPair (second :: first :: rest) penultimate final := by
        apply Word.toList_injective
        simp [terminalPair,
          SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
          Word.toList_append, toList_wordOfPrefixFinal,
          List.append_assoc]
      have rightRendered :
          (((Word.singleton first ++ Word.singleton second) ++
              wordOfPrefixFinal rest penultimate) ++ Word.singleton final) =
            terminalPair (first :: second :: rest) penultimate final := by
        apply Word.toList_injective
        simp [terminalPair,
          SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
          Word.toList_append, toList_wordOfPrefixFinal,
          List.append_assoc]
      rw [leftRendered, rightRendered] at swapped
      exact swapped
  | trans _ _ first second =>
      exact first.trans second

private theorem parityDerivesOfSupportParity
    (left right : Word Nat)
    (sameSupport : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (sameParity :
      ∀ letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2) :
    Derives commutativeParityBasis left right := by
  have reducedPermutation :=
    positiveParityReduce_perm sameSupport sameParity
  have leftNormal := positiveParityDerivesNormal left
  have rightNormal := positiveParityDerivesNormal right
  cases leftReduced : positiveParityReduce left.toList with
  | nil =>
      have present : left.head ∈ positiveParityReduce left.toList :=
        (mem_positiveParityReduce_iff _ _).mpr
          (by simp [Word.toList])
      simp [leftReduced] at present
  | cons leftHead leftTail =>
      cases rightReduced : positiveParityReduce right.toList with
      | nil =>
          rw [leftReduced, rightReduced] at reducedPermutation
          exact False.elim (List.not_perm_cons_nil reducedPermutation)
      | cons rightHead rightTail =>
          rw [leftReduced] at leftNormal
          rw [rightReduced] at rightNormal
          rw [leftReduced, rightReduced] at reducedPermutation
          exact leftNormal.trans <|
            (parityDerivesPermutation
              (Word.mk leftHead leftTail)
              (Word.mk rightHead rightTail)
              reducedPermutation).trans rightNormal.symm

/-- Add two copies of the actual penultimate guard, preserving parity and both
final positions even when the original prefix is empty. -/
theorem derivesAddGuardPair :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (terminalPair stem penultimate final)
        (terminalPair (stem ++ [penultimate, penultimate])
          penultimate final)
  | [], penultimate, final => by
      simpa [terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, Word.append_assoc] using
        (derivesTriplePrefixContraction
          (Word.singleton penultimate)
          (Word.singleton final)).symm
  | letter :: stem, penultimate, final => by
      simpa [terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton letter)
          (derivesAddGuardPair stem penultimate final)

/-- Equal parity plus support modulo the retained penultimate marker suffices
to identify complete words with the SAME genuine terminal pair. -/
theorem derivesSameGuardedPair
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (sameSupport :
      ∀ letter,
        (letter ∈ leftPrefix ∨ letter = penultimate) ↔
          (letter ∈ rightPrefix ∨ letter = penultimate))
    (sameParity :
      ∀ letter,
        leftPrefix.count letter % 2 =
          rightPrefix.count letter % 2) :
    Derives basis
      (terminalPair leftPrefix penultimate final)
      (terminalPair rightPrefix penultimate final) := by
  let leftWord :=
    wordOfPrefixFinal (leftPrefix ++ [penultimate]) penultimate
  let rightWord :=
    wordOfPrefixFinal (rightPrefix ++ [penultimate]) penultimate
  have wordSupport :
      ∀ letter, letter ∈ leftWord.toList ↔ letter ∈ rightWord.toList := by
    intro letter
    simpa [leftWord, rightWord, toList_wordOfPrefixFinal,
      List.mem_append, or_assoc] using sameSupport letter
  have wordParity :
      ∀ letter,
        leftWord.toList.count letter % 2 =
          rightWord.toList.count letter % 2 := by
    intro letter
    have prefixParity := sameParity letter
    simp only [leftWord, rightWord, toList_wordOfPrefixFinal,
      List.count_append]
    omega
  have lower :=
    parityDerivesOfSupportParity leftWord rightWord wordSupport wordParity
  have guarded :=
    liftParityBeforeFinalPair lower
      (Word.singleton penultimate) (Word.singleton final)
      Word.singleton
  rw [bind_singleton, bind_singleton] at guarded
  have middle :
      Derives basis
        (terminalPair (leftPrefix ++ [penultimate, penultimate])
          penultimate final)
        (terminalPair (rightPrefix ++ [penultimate, penultimate])
          penultimate final) := by
    have leftRendered :
        ((leftWord ++ Word.singleton penultimate) ++ Word.singleton final) =
          terminalPair (leftPrefix ++ [penultimate, penultimate])
            penultimate final := by
      apply Word.toList_injective
      simp [leftWord, terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        Word.toList_append, toList_wordOfPrefixFinal, List.append_assoc]
    have rightRendered :
        ((rightWord ++ Word.singleton penultimate) ++ Word.singleton final) =
          terminalPair (rightPrefix ++ [penultimate, penultimate])
            penultimate final := by
      apply Word.toList_injective
      simp [rightWord, terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        Word.toList_append, toList_wordOfPrefixFinal, List.append_assoc]
    rw [leftRendered, rightRendered] at guarded
    exact guarded
  exact
    (derivesAddGuardPair leftPrefix penultimate final).trans <|
      middle.trans
        (derivesAddGuardPair rightPrefix penultimate final).symm

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.Seed

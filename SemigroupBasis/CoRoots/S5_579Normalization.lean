import SemigroupBasis.CoRoots.S5_579Parity

namespace SemigroupBasis.CoRoots.S5_579

open SemigroupBasis
open SemigroupBasis.Examples

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Simulate `xyx = xxy` while retaining a fixed nonempty suffix. The
repeated-final law first gives `xyxq = x^2y^3q`; the power-tail law then
contracts `y^3q` to `yq`. -/
theorem derivesContextualParityGather
    (repeated middle rightContext : Word Nat) :
    Derives basis
      (((repeated ++ middle) ++ repeated) ++ rightContext)
      (((repeated ++ repeated) ++ middle) ++ rightContext) := by
  have expanded :=
    Derives.appendRight
      (derivesRepeatedFinalBridge repeated middle) rightContext
  have contracted :=
    Derives.prepend (repeated ++ repeated)
      (derivesTriplePrefixReduction middle rightContext)
  exact Derives.trans
    (by simpa [Word.append_assoc] using expanded)
    (by simpa [Word.append_assoc] using contracted)

/-- Replay every derivation for the `S4_95` parity basis under a fixed
nonempty right context. This is a derivation simulation, not a transfer of the
factor's completeness endpoint. -/
theorem liftParityInitial
    {left right : Word Nat}
    (derivation : Derives parityInitialBasis left right)
    (rightContext : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ rightContext)
      (right.bind substitution ++ rightContext) := by
  induction derivation generalizing rightContext substitution with
  | fromBasis member =>
      simp only [parityInitialBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityInitialPowerLaw, parityInitialX,
          parityInitialXXX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.symm
            (derivesTriplePrefixReduction
              (substitution 0) rightContext)
      · simpa [parityInitialGatherLaw, parityInitialXYX,
          parityInitialXXY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualParityGather
            (substitution 0) (substitution 1) rightContext
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih rightContext substitution)
  | trans _ _ ihLeft ihRight =>
      exact Derives.trans
        (ihLeft rightContext substitution)
        (ihRight rightContext substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (ih rightContext substitution)
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (suffix.bind substitution ++ rightContext) substitution
  | subst _ first ih =>
      simpa [bind_bind] using
        ih rightContext
          (fun letter => (first letter).bind substitution)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem wordOfCons_append_final
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfCons head tail ++ Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

/-- Normalize the entire prefix before the original final letter to the exact
`S4_95` first-occurrence/parity profile. The final letter is retained as the
nonempty context, so this theorem applies to every semigroup word, including
the no-simple-final branch. -/
def prefixParityNormalWord (word : Word Nat) : Word Nat :=
  let split := splitPrefixFinal word
  match split.1 with
  | [] => Word.singleton split.2
  | head :: tail =>
      match parityInitialNormalList (head :: tail) with
      | [] => Word.singleton split.2
      | normalHead :: normalTail =>
          wordOfCons normalHead normalTail ++ Word.singleton split.2

/-- Unrestricted source normalizer to `prefixParityNormalWord`. It deliberately
stops before recursively moving a repeated final marker to a canonical final
block. -/
theorem derivesPrefixParityNormal (word : Word Nat) :
    Derives basis word (prefixParityNormalWord word) := by
  let split := splitPrefixFinal word
  have reconstruct : wordOfPrefixFinal split.1 split.2 = word :=
    wordOfPrefixFinal_split word
  cases prefixEq : split.1 with
  | nil =>
      have sourceEq : word = Word.singleton split.2 := by
        rw [← reconstruct, prefixEq]
        rfl
      rw [sourceEq]
      simp [prefixParityNormalWord, split, prefixEq]
      exact Derives.refl _
  | cons head tail =>
      let prefixWord := wordOfCons head tail
      have prefixNormal := parityInitialDerivesNormal prefixWord
      cases normalEq : parityInitialNormalList (head :: tail) with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil head tail normalEq
      | cons normalHead normalTail =>
          change
            match parityInitialNormalList prefixWord.toList with
            | [] => False
            | first :: rest =>
                Derives parityInitialBasis prefixWord
                  (parityInitialWordOfCons first rest) at prefixNormal
          have normalForPrefix :
              parityInitialNormalList prefixWord.toList =
                normalHead :: normalTail := by
            simpa [prefixWord, wordOfCons, Word.toList] using normalEq
          rw [normalForPrefix] at prefixNormal
          have lifted :=
            liftParityInitial prefixNormal
              (Word.singleton split.2) Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          have sourceEq :
              prefixWord ++ Word.singleton split.2 = word := by
            rw [wordOfCons_append_final]
            rw [← reconstruct, prefixEq]
          have targetEq :
              prefixParityNormalWord word =
                wordOfCons normalHead normalTail ++
                  Word.singleton split.2 := by
            simp [prefixParityNormalWord, split, prefixEq, normalEq]
          rw [targetEq]
          simpa [sourceEq, parityInitialWordOfCons, wordOfCons] using lifted

/-- The repeated-final branch with one current copy of the repeated block.
It toggles that block to even multiplicity and makes the intervening block a
terminal triple. -/
theorem derivesRepeatedFinalEvenBridge
    (repeated middle : Word Nat) :
    Derives basis ((repeated ++ middle) ++ repeated)
      ((repeated ++ repeated) ++ ((middle ++ middle) ++ middle)) := by
  simpa [Word.append_assoc] using
    derivesRepeatedFinalBridge repeated middle

/-- The repeated-final branch with two current copies of the repeated block.
The new terminal block occurs three times, which is the required odd
terminal-triple branch. -/
theorem derivesRepeatedFinalOddTerminalTriple
    (repeated middle : Word Nat) :
    Derives basis (((repeated ++ repeated) ++ middle) ++ repeated)
      (repeated ++ ((middle ++ middle) ++ middle)) := by
  have expanded :=
    Derives.prepend repeated
      (derivesRepeatedFinalBridge repeated middle)
  have contracted :=
    derivesTriplePrefixReduction repeated
      ((middle ++ middle) ++ middle)
  exact Derives.trans
    (by simpa [Word.append_assoc] using expanded)
    (by simpa [Word.append_assoc] using contracted)

/- `derivesPrefixParityNormal` and the two repeated-final bridges are valid for
all nonempty substituted blocks. `S5_579Canonical` performs their structural
iteration when the repeated final variable is not the last variable in
first-occurrence order. -/

end SemigroupBasis.CoRoots.S5_579

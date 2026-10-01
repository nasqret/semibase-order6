import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_254

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private def instantiateTwoWords
    (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

/-- The square of any nonempty word commutes with every nonempty word.
This is the direct nonempty-substitution instance of `xxy = yxx`. -/
theorem derivesSquareBlockAcross (block payload : Word Nat) :
    Derives basis
      ((block ++ block) ++ payload)
      (payload ++ (block ++ block)) := by
  have substituted :=
    derivesPrefixRotationSubstitution
      (instantiateTwoWords block payload)
  change
    Derives basis
      ((block ++ block) ++ payload)
      ((payload ++ block) ++ block) at substituted
  simpa [Word.append_assoc] using substituted

/-- Four copies of a nonempty block contract to two copies. -/
theorem derivesFourBlockToTwo (block : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ block)
      (block ++ block) := by
  have substituted :=
    derivesPowerSubstitution (instantiateTwoWords block block)
  change
    Derives basis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) at substituted
  exact substituted.symm

/-- A square block crosses an arbitrary list. Empty blocks and empty
payloads are discharged by reflexivity; all nonempty cases use
`derivesSquareBlockAcross`, so no empty substitution image is introduced. -/
theorem listDerivesBlockSquareAcross
    (block payload : List Nat) :
    ListDerives
      (block ++ block ++ payload)
      (payload ++ block ++ block) := by
  cases block with
  | nil =>
      simpa using
        S5_107.ListDerives.refl (basis := basis) payload
  | cons blockHead blockTail =>
      cases payload with
      | nil =>
          simpa using
            S5_107.ListDerives.refl (basis := basis)
              ((blockHead :: blockTail) ++
                (blockHead :: blockTail))
      | cons payloadHead payloadTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSquareBlockAcross
                  (S5_107.listWordOfCons blockHead blockTail)
                  (S5_107.listWordOfCons payloadHead payloadTail)

/-- A single-letter pair crosses an arbitrary list, including the empty
list. -/
theorem listDerivesPairAcross (letter : Nat) (payload : List Nat) :
    ListDerives
      ([letter, letter] ++ payload)
      (payload ++ [letter, letter]) := by
  simpa [List.append_assoc] using
    listDerivesBlockSquareAcross [letter] payload

/-- Relocate an adjacent pair through arbitrary left and right contexts. -/
theorem listDerivesPairAcrossContext
    (prefixWords : List Nat) (letter : Nat)
    (payload suffix : List Nat) :
    ListDerives
      (prefixWords ++ [letter, letter] ++ payload ++ suffix)
      (prefixWords ++ payload ++ [letter, letter] ++ suffix) := by
  simpa [List.append_assoc] using
    S5_107.ListDerives.context
      (basis := basis) prefixWords suffix
      (listDerivesPairAcross letter payload)

/-- Contract two adjacent copies of the same letter-pair. -/
theorem listDerivesDuplicatePairContraction
    (letter : Nat) :
    ListDerives [letter, letter, letter, letter] [letter, letter] := by
  exact S5_107.ListDerives.words <| by
    simpa [S5_107.listWordOfCons, Word.append,
      Word.singleton, Word.append_assoc] using
        derivesFourBlockToTwo (Word.singleton letter)

/-- Contract a duplicated pair under arbitrary list contexts. -/
theorem listDerivesDuplicatePairContractionContext
    (prefixWords : List Nat) (letter : Nat) (suffix : List Nat) :
    ListDerives
      (prefixWords ++ [letter, letter, letter, letter] ++ suffix)
      (prefixWords ++ [letter, letter] ++ suffix) := by
  simpa [List.append_assoc] using
    S5_107.ListDerives.context
      (basis := basis) prefixWords suffix
      (listDerivesDuplicatePairContraction letter)

/-- Render each label as one adjacent square. This is the movable pair bank
that remains after a future extraction pass separates parity residues from
even pairs. -/
def renderSquareBank (labels : List Nat) : List Nat :=
  labels.flatMap fun letter => [letter, letter]

/-- Extracted square banks commute with arbitrary separator skeletons. -/
theorem listDerivesSquareBankAcross :
    ∀ (labels payload : List Nat),
      ListDerives
        (renderSquareBank labels ++ payload)
        (payload ++ renderSquareBank labels)
  | [], payload => by
      simpa [renderSquareBank] using
        S5_107.ListDerives.refl (basis := basis) payload
  | letter :: labels, payload => by
      have restFirst :=
        S5_107.ListDerives.prepend
          (basis := basis) [letter, letter]
          (listDerivesSquareBankAcross labels payload)
      have headSecond :=
        listDerivesPairAcrossContext [] letter payload
          (renderSquareBank labels)
      exact S5_107.ListDerives.trans
        (by simpa [renderSquareBank, List.append_assoc] using restFirst)
        (by simpa [renderSquareBank, List.append_assoc] using headSecond)

/-- Relocate an extracted square bank through arbitrary left and right
contexts. The payload may contain any globally simple separators. -/
theorem listDerivesSquareBankAcrossContext
    (prefixWords labels payload suffix : List Nat) :
    ListDerives
      (prefixWords ++ renderSquareBank labels ++ payload ++ suffix)
      (prefixWords ++ payload ++ renderSquareBank labels ++ suffix) := by
  simpa [List.append_assoc] using
    S5_107.ListDerives.context
      (basis := basis) prefixWords suffix
      (listDerivesSquareBankAcross labels payload)

/-- Every permutation of square-bank labels is derivable. -/
theorem listDerivesSquareBankPermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives
      (renderSquareBank source)
      (renderSquareBank target) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.empty
  | cons letter _ induction =>
      simpa [renderSquareBank] using
        S5_107.ListDerives.prepend
          (basis := basis) [letter, letter] induction
  | swap left right rest =>
      have swapped :=
        listDerivesPairAcross left [right, right]
      simpa [renderSquareBank, List.append_assoc] using
        (S5_107.ListDerives.append
          (basis := basis) swapped
          (renderSquareBank rest)).symm
  | trans _ _ first second =>
      exact S5_107.ListDerives.trans first second

/-- Remove a duplicated square-bank label. The proof exposes the later pair
by a bank permutation, contracts four adjacent copies, and restores the
original order of the remaining bank. -/
theorem listDerivesDropDuplicateSquareHead
    (letter : Nat) (labels : List Nat)
    (present : letter ∈ labels) :
    ListDerives
      (renderSquareBank (letter :: labels))
      (renderSquareBank labels) := by
  have expose : labels.Perm (letter :: labels.erase letter) :=
    List.perm_cons_erase present
  have exposeDerivation :=
    listDerivesSquareBankPermutation expose
  have prefixedExpose :=
    S5_107.ListDerives.prepend
      (basis := basis) [letter, letter] exposeDerivation
  have contraction :=
    S5_107.ListDerives.append
      (basis := basis)
      (listDerivesDuplicatePairContraction letter)
      (renderSquareBank (labels.erase letter))
  exact S5_107.ListDerives.trans
    (by simpa [renderSquareBank, List.append_assoc] using prefixedExpose) <|
      S5_107.ListDerives.trans
        (by simpa [renderSquareBank, List.append_assoc] using contraction)
        exposeDerivation.symm

/-- Keep the last occurrence of every square-bank label. -/
def deduplicateSquareBank : List Nat → List Nat
  | [] => []
  | letter :: labels =>
      if letter ∈ labels then
        deduplicateSquareBank labels
      else
        letter :: deduplicateSquareBank labels

/-- Every square bank derives to its duplicate-free representative. -/
theorem listDerivesDeduplicateSquareBank :
    ∀ labels : List Nat,
      ListDerives
        (renderSquareBank labels)
        (renderSquareBank (deduplicateSquareBank labels))
  | [] => by
      exact S5_107.ListDerives.empty
  | letter :: labels => by
      by_cases present : letter ∈ labels
      · have drop :=
          listDerivesDropDuplicateSquareHead letter labels present
        have normalizeTail :=
          listDerivesDeduplicateSquareBank labels
        simpa [deduplicateSquareBank, present] using
          S5_107.ListDerives.trans drop normalizeTail
      · have normalizeTail :=
          S5_107.ListDerives.prepend
            (basis := basis) [letter, letter]
            (listDerivesDeduplicateSquareBank labels)
        simpa [renderSquareBank, deduplicateSquareBank, present,
          List.append_assoc] using normalizeTail

/-- Deterministic canonical order for an extracted square bank. -/
def canonicalSquareBank (labels : List Nat) : List Nat :=
  (deduplicateSquareBank labels).mergeSort
    (fun left right => decide (left ≤ right))

private theorem natMergeSort_pairwise (letters : List Nat) :
    (letters.mergeSort
      (fun left right => decide (left ≤ right))).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted := List.pairwise_mergeSort transitive total letters
  exact sorted.imp fun relation => of_decide_eq_true relation

@[simp] private theorem mergeSort_three_two_one :
    ([3, 2, 1].mergeSort
      (fun left right : Nat => decide (left ≤ right))) = [1, 2, 3] := by
  have inputPermutation :
      ([3, 2, 1] : List Nat).Perm [1, 2, 3] :=
    (List.Perm.swap 2 3 [1]).trans <|
      (List.Perm.cons 2 (List.Perm.swap 1 3 [])).trans <|
        List.Perm.swap 1 2 [3]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (natMergeSort_pairwise [3, 2, 1])
    (by decide)
    ((List.mergeSort_perm _ _).trans inputPermutation)

/-- Every extracted square bank derives to its deduplicated, sorted canonical
representative. -/
theorem listDerivesCanonicalSquareBank (labels : List Nat) :
    ListDerives
      (renderSquareBank labels)
      (renderSquareBank (canonicalSquareBank labels)) := by
  exact S5_107.ListDerives.trans
    (listDerivesDeduplicateSquareBank labels) <|
      listDerivesSquareBankPermutation
        (List.mergeSort_perm _ _).symm

/-- Restricted completeness for extracted square banks: equal canonical
banks are derivably equal. This does not extract pairs from an arbitrary
interleaved M18 word. -/
theorem listDerivesSquareBanksOfEqualCanonical
    (source target : List Nat)
    (same : canonicalSquareBank source = canonicalSquareBank target) :
    ListDerives
      (renderSquareBank source)
      (renderSquareBank target) := by
  have sourceNormal := listDerivesCanonicalSquareBank source
  have targetNormal := listDerivesCanonicalSquareBank target
  rw [same] at sourceNormal
  exact S5_107.ListDerives.trans sourceNormal targetNormal.symm

/-- Canonicalize a square bank while moving it across an arbitrary residue
or separator skeleton. The theorem assumes the even pairs have already been
extracted into `labels`. Pair extraction is the next source layer and now
discharges that historical obstruction. -/
theorem listDerivesNormalizeExtractedSquareBank
    (labels residue : List Nat) :
    ListDerives
      (renderSquareBank labels ++ residue)
      (residue ++ renderSquareBank (canonicalSquareBank labels)) := by
  exact S5_107.ListDerives.trans
    (listDerivesSquareBankAcross labels residue) <|
      S5_107.ListDerives.prepend
        (basis := basis) residue
        (listDerivesCanonicalSquareBank labels)

end SemigroupBasis.CoRoots.S5_254

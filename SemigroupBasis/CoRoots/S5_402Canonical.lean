import SemigroupBasis.CoRoots.S5_402TailNormalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

/-! ## Canonical square-factor inventory -/

/-- Every factor retained by the marker-only filter has an empty block. -/
theorem markerOnlyFactors_blocks_empty
    (factors : List (List Nat × Nat)) :
    ∀ factor ∈ markerOnlyFactors factors, factor.1 = [] := by
  intro factor member
  simp only [markerOnlyFactors, List.mem_filter,
    decide_eq_true_eq] at member
  exact member.2

/-- A factor list whose blocks are all empty is recovered exactly from its
marker projection. -/
theorem markerOnlyFactorList_terminatedFactorMarkers
    (factors : List (List Nat × Nat))
    (blocksEmpty : ∀ factor ∈ factors, factor.1 = []) :
    markerOnlyFactorList (terminatedFactorMarkers factors) = factors := by
  induction factors with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockEmpty : block = [] :=
        blocksEmpty (block, marker) (by simp)
      have restEmpty :
          ∀ candidate ∈ rest, candidate.1 = [] := by
        intro candidate member
        exact blocksEmpty candidate (by simp [member])
      change
        ([], marker) ::
            markerOnlyFactorList (terminatedFactorMarkers rest) =
          (block, marker) :: rest
      rw [blockEmpty, ih restEmpty]

/-- Recover the filtered marker-only factor list from its marker labels. -/
theorem markerOnlyFactorList_markerOnlyFactors
    (factors : List (List Nat × Nat)) :
    markerOnlyFactorList
        (terminatedFactorMarkers (markerOnlyFactors factors)) =
      markerOnlyFactors factors :=
  markerOnlyFactorList_terminatedFactorMarkers
    (markerOnlyFactors factors)
    (markerOnlyFactors_blocks_empty factors)

/-- Deterministic factor inventory used by the unrestricted canonical form.
The first sorted factor remains fixed, every later block-bearing factor is
retained, and the remaining repeated labels form one deduplicated, filtered,
sorted marker-only square bank. -/
def canonicalSquaredFactorInventory (letters : List Nat) :
    List (List Nat × Nat) :=
  match sortedTerminatedBlocks letters with
  | [] => []
  | first :: rest =>
      let retainedTail := blockBearingFactors rest
      let labels :=
        terminatedFactorMarkers (markerOnlyFactors rest)
      first :: retainedTail ++
        markerOnlyFactorList
          (canonicalMarkerBank
            (terminatedFactorMarkers (first :: retainedTail))
            labels)

/-- Normalize the sorted square-ended scanner factors to the deterministic
factor inventory. This closes the arbitrary marker-bank contraction problem
without first extracting the bank into scattered singleton copies. -/
theorem listDerivesCanonicalizeSortedFactorInventory
    (letters : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (sortedTerminatedBlocks letters) ++
        terminatedFinalBlock letters)
      (renderSquaredTerminatedBlocks
          (canonicalSquaredFactorInventory letters) ++
        terminatedFinalBlock letters) := by
  cases shape : sortedTerminatedBlocks letters with
  | nil =>
      simpa [canonicalSquaredFactorInventory, shape] using
        (S5_107.ListDerives.refl
          (basis := basis) (terminatedFinalBlock letters))
  | cons first rest =>
      let retainedTail := blockBearingFactors rest
      let labels :=
        terminatedFactorMarkers (markerOnlyFactors rest)
      have partition :=
        listDerivesSquaredTailPermutation
          (blockBearingFactors_append_markerOnlyFactors_perm rest).symm
          first (terminatedFinalBlock letters)
      have markerShape :
          markerOnlyFactorList labels = markerOnlyFactors rest := by
        simpa [labels] using
          markerOnlyFactorList_markerOnlyFactors rest
      have partitionStep :
          ListDerives
            (renderSquaredTerminatedBlocks (first :: rest) ++
              terminatedFinalBlock letters)
            (renderSquaredTerminatedBlocks
                (first :: retainedTail ++
                  markerOnlyFactorList labels) ++
              terminatedFinalBlock letters) := by
        simpa [retainedTail, markerShape, List.append_assoc] using
          partition
      have bankStep :=
        listDerivesCanonicalMarkerBank
          first retainedTail labels
          (terminatedFinalBlock letters)
      refine S5_107.ListDerives.trans
        (middle :=
          renderSquaredTerminatedBlocks
              (first :: retainedTail ++ markerOnlyFactorList labels) ++
            terminatedFinalBlock letters) ?_ ?_
      · simpa [shape] using partitionStep
      · simpa [canonicalSquaredFactorInventory, shape,
          retainedTail, labels, List.append_assoc] using bankStep

/-- Canonical list obtained by rendering the deterministic square-factor
inventory and the unchanged final simple block. -/
def squareInventoryCanonicalList (letters : List Nat) : List Nat :=
  renderSquaredTerminatedBlocks
      (canonicalSquaredFactorInventory letters) ++
    terminatedFinalBlock letters

/-- Every finite word list derives to the square-inventory canonical list,
with no bound on its length, number of variables, or occurrence pattern. -/
theorem listDerivesSquareInventoryCanonical
    (letters : List Nat) :
    ListDerives letters (squareInventoryCanonicalList letters) :=
  (listDerivesSquareAndSortTerminatedFactors letters).trans <| by
    simpa [squareInventoryCanonicalList] using
      listDerivesCanonicalizeSortedFactorInventory letters

private def squareInventoryWordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- Word-level form of the square-inventory canonical list. -/
def squareInventoryCanonicalWord (word : Word Nat) : Word Nat :=
  squareInventoryWordOfListOr word.head
    (squareInventoryCanonicalList word.toList)

theorem squareInventoryCanonicalList_ne_nil (word : Word Nat) :
    squareInventoryCanonicalList word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      apply S5_107.ListDerives.target_ne_nil
      simpa [Word.toList] using
        listDerivesSquareInventoryCanonical (head :: tail)

@[simp]
theorem toList_squareInventoryCanonicalWord (word : Word Nat) :
    (squareInventoryCanonicalWord word).toList =
      squareInventoryCanonicalList word.toList := by
  unfold squareInventoryCanonicalWord
  cases shape : squareInventoryCanonicalList word.toList with
  | nil =>
      exact False.elim <|
        squareInventoryCanonicalList_ne_nil word shape
  | cons head tail =>
      rfl

/-- Unrestricted word-level normalization to the canonical square-factor
inventory. -/
theorem derivesSquareInventoryCanonical (word : Word Nat) :
    Derives basis word (squareInventoryCanonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :
          ListDerives (head :: tail)
            (squareInventoryCanonicalList
              (Word.mk head tail).toList) := by
        simpa [Word.toList] using
          listDerivesSquareInventoryCanonical (head :: tail)
      obtain
        ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
          S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            squareInventoryCanonicalWord
              (Word.mk head tail) := by
        apply Word.toList_injective
        rw [toList_squareInventoryCanonicalWord]
        simpa [S5_107.listWordOfCons] using targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

end SemigroupBasis.CoRoots.S5_402

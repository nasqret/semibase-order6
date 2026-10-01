import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitialSignature
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

/-!
# Endpoint capping for the d024 B10 root

The deterministic endpoint cap retains the first and last occurrence of
each letter.  Its middle-occurrence deletion is derivable from literal B10
laws 1, 2, 3, and 6, with the law orientation chosen separately for the
four empty/nonempty gap cases.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

open SemigroupBasis
open SemigroupBasis.Examples

/-- Delete the middle of three occurrences of one letter.  Laws 1, 2, 3,
and 6 cover the four possible empty/nonempty intervening-gap cases. -/
private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    B10ListDerives
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesPowerExpansion (Word.singleton x)).symm
      | cons y ys =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesLeftContraction
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)
  | cons y ys =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesRightExpansion
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesCrossingContraction
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)
                (S5_107.listWordOfCons z zs)

/-- Delete a current occurrence that has both a processed and a future
occurrence. -/
private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    B10ListDerives (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore x left right).context before after

/-- The endpoint-cap scanner is derivable whenever each seen letter is
already represented in the fixed processed part. -/
private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      B10ListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using
        S5_107.ListDerives.refl (basis := B10) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre :=
          seenInPre x middle.1
        have deleteCurrent :
            B10ListDerives
              (pre ++ x :: xs) (pre ++ xs) :=
          listDerivesDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact xInPre
          · exact seenInPre z hz
        have recurse :=
          listDerivesEndpointCapAux
            pre (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre ++ [x] := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [x] (seenInPre z hz)
        have recurse :=
          listDerivesEndpointCapAux
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every list derives to the deterministic cap retaining exactly the first
and last occurrence of each letter. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    B10ListDerives letters (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

/-- Endpoint capping preserves the complete first-occurrence sequence. -/
theorem firstOccurrenceSequence_endpointCap
    (letters : List Nat) :
    firstOccurrenceSequence (uniqueSeparatorEndpointCap letters) =
      firstOccurrenceSequence letters := by
  cases letters with
  | nil =>
      rfl
  | cons head tail =>
      have derivation :=
        listDerivesEndpointCap (head :: tail)
      obtain
        ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
          derivation.from_cons
      rw [targetShape]
      simpa [S5_107.listWordOfCons, Word.toList] using
        (derives_sameCutInitialSignature wordDerivation).initials.symm

/-- Endpoint capping preserves the full ordered connected-cut signature,
including component finals and unary repetition flags. -/
theorem connectedCutSignatures_endpointCap
    (letters : List Nat) :
    S5_804.connectedCutSignaturesList
        (uniqueSeparatorEndpointCap letters) =
      S5_804.connectedCutSignaturesList letters := by
  cases letters with
  | nil =>
      rfl
  | cons head tail =>
      have derivation :=
        listDerivesEndpointCap (head :: tail)
      obtain
        ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
          derivation.from_cons
      rw [targetShape]
      simpa [S5_107.listWordOfCons, Word.toList,
        S5_804.SameConnectedCutSignature,
        S5_804.connectedCutSignaturesWord] using
          (derives_sameCutInitialSignature wordDerivation).cuts.symm

/-- A support-connected nonempty list is scanned as one component. -/
private theorem connectedComponentDecomposeList_eq_singleton
    {letters : List Nat}
    (nonempty : letters ≠ [])
    (connected : ConnectedComponentSupportConnected letters) :
    connectedComponentDecomposeList letters = [letters] := by
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty nonempty
  obtain ⟨first, rest, decompositionShape⟩ :=
    List.exists_cons_of_ne_nil decompositionNonempty
  cases rest with
  | nil =>
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by
        simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty :
          (second :: remaining).flatten ≠ [] := by
        have secondNonempty : second ≠ [] :=
          connectedComponentDecomposeList_nonempty_components letters
            second (by rw [decompositionShape]; simp)
        intro flattenedEmpty
        have appendedEmpty :
            second ++ remaining.flatten = [] := by
          simpa using flattenedEmpty
        exact secondNonempty
          (List.append_eq_nil_iff.mp appendedEmpty).1
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint letters
      rw [decompositionShape] at pairwise
      have firstToSuffix :=
        (List.pairwise_cons.mp pairwise).1
      have disjoint :
          ConnectedComponentSupportsDisjoint
            first (second :: remaining).flatten := by
        intro letter firstMember suffixMember
        rw [List.mem_flatten] at suffixMember
        rcases suffixMember with
          ⟨candidate, candidateMember, letterMember⟩
        exact
          (firstToSuffix candidate candidateMember
            letter firstMember) letterMember
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim <|
        disjoint letter firstMember suffixMember

/-- Equality of full cut signatures transfers support-connectedness from a
nonempty source list. -/
private theorem supportConnected_of_same_cut_signatures
    {source target : List Nat}
    (sourceNonempty : source ≠ [])
    (sourceConnected : ConnectedComponentSupportConnected source)
    (same :
      S5_804.connectedCutSignaturesList source =
        S5_804.connectedCutSignaturesList target) :
    ConnectedComponentSupportConnected target := by
  have sourceDecomposition :=
    connectedComponentDecomposeList_eq_singleton
      sourceNonempty sourceConnected
  have equalLengths :
      (connectedComponentDecomposeList source).length =
        (connectedComponentDecomposeList target).length := by
    simpa [S5_804.connectedCutSignaturesList] using
      congrArg List.length same
  have targetDecompositionLength :
      (connectedComponentDecomposeList target).length = 1 := by
    calc
      (connectedComponentDecomposeList target).length =
          (connectedComponentDecomposeList source).length :=
        equalLengths.symm
      _ = 1 := by rw [sourceDecomposition]; rfl
  obtain ⟨only, targetDecomposition⟩ :=
    List.length_eq_one_iff.mp targetDecompositionLength
  have onlyConnected :=
    connectedComponentDecomposeList_supportConnected target
      only (by rw [targetDecomposition]; simp)
  have flattened :=
    connectedComponentDecomposeList_flatten target
  rw [targetDecomposition] at flattened
  have onlyEq : only = target := by
    simpa using flattened
  simpa [onlyEq] using onlyConnected

/-- Endpoint capping preserves support-connectedness. -/
theorem endpointCap_supportConnected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail)) :
    ConnectedComponentSupportConnected
      (uniqueSeparatorEndpointCap (head :: tail)) := by
  exact supportConnected_of_same_cut_signatures
    (by simp) connected
      (connectedCutSignatures_endpointCap (head :: tail)).symm

/-- A support-connected list of length at least two retains at least two
letters after endpoint capping. -/
theorem endpointCap_lengthAtLeastTwo
    {head next : Nat} {rest : List Nat}
    (connected :
      ConnectedComponentSupportConnected
        (head :: next :: rest)) :
    2 ≤
      (uniqueSeparatorEndpointCap
        (head :: next :: rest)).length := by
  have headInTail : head ∈ next :: rest :=
    connectedComponentSupportConnected_cons_tail
      connected (by simp)
  have sourceCount :
      2 ≤ (head :: next :: rest).count head := by
    have positive :
        1 ≤ (next :: rest).count head :=
      List.one_le_count_iff.mpr headInTail
    simp only [List.count_cons_self]
    omega
  have capCount :
      (uniqueSeparatorEndpointCap
        (head :: next :: rest)).count head = 2 :=
    (uniqueSeparatorEndpointCap_count_eq_two_iff
      head (head :: next :: rest)).2 sourceCount
  have countBound :=
    List.count_le_length
      (a := head)
      (l := uniqueSeparatorEndpointCap (head :: next :: rest))
  omega

/-! ## Basis-independent cap contracts -/

/-- The endpoint cap is a sublist of its source. -/
theorem endpointCap_sublist (letters : List Nat) :
    List.Sublist (uniqueSeparatorEndpointCap letters) letters :=
  uniqueSeparatorEndpointCap_sublist letters

/-- Endpoint capping preserves support exactly. -/
theorem endpointCap_mem_iff (letter : Nat) (letters : List Nat) :
    letter ∈ uniqueSeparatorEndpointCap letters ↔ letter ∈ letters :=
  uniqueSeparatorEndpointCap_mem_iff letter letters

/-- Endpoint capping truncates every multiplicity at two. -/
theorem endpointCap_count (letter : Nat) (letters : List Nat) :
    (uniqueSeparatorEndpointCap letters).count letter =
      Nat.min 2 (letters.count letter) :=
  uniqueSeparatorEndpointCap_count letter letters

/-- Endpoint capping never increases list length. -/
theorem endpointCap_length_le (letters : List Nat) :
    (uniqueSeparatorEndpointCap letters).length ≤ letters.length :=
  (endpointCap_sublist letters).length_le

/-- Every capped list contains each letter at most twice. -/
theorem endpointCap_twoLimited (letters : List Nat) :
    UniqueSeparatorTwoLimited
      (uniqueSeparatorEndpointCap letters) :=
  uniqueSeparatorEndpointCap_twoLimited letters

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

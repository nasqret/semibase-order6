import SemigroupBasis.CoRoots.S5_791Invariant
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.CoRoots.S5_791

open SemigroupBasis
open SemigroupBasis.Examples

/-- Delete the middle of three occurrences of one letter. The regular-band
law covers two nonempty gaps; the three duplication laws cover all endpoint
cases. -/
private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    S5_107.ListDerives basis
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
              (derivesLeftDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesRightDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesRegularContraction
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)
                (S5_107.listWordOfCons z zs)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    S5_107.ListDerives basis
      (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore x left right).context before after

private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      S5_107.ListDerives basis
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using S5_107.ListDerives.refl (basis := basis) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre := seenInPre x middle.1
        have deleteCurrent :
            S5_107.ListDerives basis
              (pre ++ x :: xs) (pre ++ xs) :=
          listDerivesDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact xInPre
          · exact seenInPre z hz
        have recurse :=
          listDerivesEndpointCapAux pre (x :: seen) nextSeenInPre xs
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

/-- Every list derives to the deterministic cap retaining its first and last
occurrences of each letter. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    S5_107.ListDerives basis letters
      (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

/-- Endpoint capping preserves the full first-occurrence sequence. -/
theorem firstOccurrenceSequence_endpointCap
    (letters : List Nat) :
    firstOccurrenceSequence
        (uniqueSeparatorEndpointCap letters) =
      firstOccurrenceSequence letters := by
  cases letters with
  | nil =>
      rfl
  | cons head tail =>
      have derivation := listDerivesEndpointCap (head :: tail)
      obtain
        ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
          derivation.from_cons
      rw [targetShape]
      simpa [S5_107.listWordOfCons, Word.toList] using
        (derives_sameSignature wordDerivation).initials.symm

end SemigroupBasis.CoRoots.S5_791

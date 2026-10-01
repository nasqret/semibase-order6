import SemigroupBasis.Examples.UniqueSeparatorFourListDerives
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Delete the middle of three occurrences of `x`, including the cases where
one or both intervening gaps are empty. -/
private theorem uniqueSeparatorDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    UniqueSeparatorListDerives
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [uniqueSeparatorWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (uniqueSeparatorDerivesPowerExpansion
                (Word.singleton x)).symm
      | cons y ys =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [uniqueSeparatorWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (uniqueSeparatorDerivesLeftDuplication
                (Word.singleton x)
                (uniqueSeparatorWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [uniqueSeparatorWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (uniqueSeparatorDerivesRightDuplication
                (Word.singleton x)
                (uniqueSeparatorWordOfCons y ys)).symm
      | cons z zs =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [uniqueSeparatorWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              uniqueSeparatorDerivesThirdOccurrenceDeletion
                (Word.singleton x)
                (uniqueSeparatorWordOfCons y ys)
                (uniqueSeparatorWordOfCons z zs)

/-- If `x` occurs in both a processed prefix and the remaining suffix, then
the current occurrence between them may be deleted. -/
private theorem uniqueSeparatorDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    UniqueSeparatorListDerives
      (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (uniqueSeparatorDeleteMiddleCore x left right).context before after

/-- The scanner cap is derivable whenever every letter recorded in `seen`
already occurs in the fixed processed prefix. -/
private theorem uniqueSeparatorEndpointCapAux_derives
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      UniqueSeparatorListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using UniqueSeparatorListDerives.refl pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre :=
          seenInPre x middle.1
        have deleteCurrent :
            UniqueSeparatorListDerives
              (pre ++ x :: xs) (pre ++ xs) :=
          uniqueSeparatorDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact xInPre
          · exact seenInPre z hz
        have recurse :=
          uniqueSeparatorEndpointCapAux_derives
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
          uniqueSeparatorEndpointCapAux_derives
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every word derives its deterministic endpoint cap: all occurrences except
the first and last occurrence of each letter can be deleted from the seven-law
basis. -/
theorem uniqueSeparatorEndpointCap_derives (xs : List Nat) :
    UniqueSeparatorListDerives xs (uniqueSeparatorEndpointCap xs) := by
  simpa [uniqueSeparatorEndpointCap] using
    uniqueSeparatorEndpointCapAux_derives
      [] [] (by simp) xs

end SemigroupBasis.Examples

import SemigroupBasis.CoRoots.S5_379ListDerives
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_379

open SemigroupBasis
open SemigroupBasis.Examples

/-- Append a letter exactly while fewer than two copies have been retained.
This prefix-only helper is retained for API compatibility; the sound endpoint
cap below uses future-occurrence lookahead. -/
def capStep (kept : List Nat) (letter : Nat) : List Nat :=
  if kept.count letter < 2 then kept ++ [letter] else kept

/-- Retain the first and last occurrences of every letter. -/
abbrev capScan := uniqueSeparatorEndpointCap

/-- The scan realizes pointwise capping at two. -/
theorem capScan_count (tested : Nat) (letters : List Nat) :
    (capScan letters).count tested = min (letters.count tested) 2 := by
  simpa [Nat.min_comm] using
    uniqueSeparatorEndpointCap_count tested letters

theorem capScan_count_le_two (tested : Nat) (letters : List Nat) :
    (capScan letters).count tested ≤ 2 := by
  rw [capScan_count]
  exact Nat.min_le_right _ _

theorem mem_capScan_iff (tested : Nat) (letters : List Nat) :
    tested ∈ capScan letters ↔ tested ∈ letters := by
  exact uniqueSeparatorEndpointCap_mem_iff tested letters

theorem capScan_ne_nil {letters : List Nat}
    (nonempty : letters ≠ []) : capScan letters ≠ [] := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      exact List.ne_nil_of_mem <|
        (mem_capScan_iff head (head :: tail)).mpr (by simp)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (letter : Nat)
    (past : letter ∈ pre) (future : letter ∈ suffix) :
    ListDerives (pre ++ letter :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, firstGap, preShape⟩
  rcases List.append_of_mem future with
    ⟨secondGap, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    listDerivesDeleteThirdOccurrence
      letter before firstGap secondGap after

private theorem listDerivesCapScanAux
    (pre seen : List Nat)
    (seenInPre : ∀ tested ∈ seen, tested ∈ pre) :
    ∀ suffix : List Nat,
      ListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using S5_107.ListDerives.refl (basis := basis) pre
  | letter :: rest => by
      by_cases middle : letter ∈ seen ∧ letter ∈ rest
      · have letterInPre : letter ∈ pre :=
          seenInPre letter middle.1
        have deleteCurrent :
            ListDerives
              (pre ++ letter :: rest) (pre ++ rest) :=
          listDerivesDeleteCurrent
            pre rest letter letterInPre middle.2
        have nextSeenInPre :
            ∀ tested ∈ letter :: seen, tested ∈ pre := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact letterInPre
          · exact seenInPre tested member
        have recurse :=
          listDerivesCapScanAux pre (letter :: seen)
            nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ tested ∈ letter :: seen,
              tested ∈ pre ++ [letter] := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [letter]
              (seenInPre tested member)
        have recurse :=
          listDerivesCapScanAux
            (pre ++ [letter]) (letter :: seen)
            nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every list derives directly to its first/last-occurrence cap. -/
theorem listDerivesCapScan (letters : List Nat) :
    ListDerives letters (capScan letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesCapScanAux [] [] (by simp) letters

end SemigroupBasis.CoRoots.S5_379

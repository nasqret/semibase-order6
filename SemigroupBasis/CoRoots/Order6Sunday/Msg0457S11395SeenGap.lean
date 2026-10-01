import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenSwaps
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PositiveRuns

/-! Canonical normalization of an arbitrary gap all of whose letters are
already present in its prefix. Support and parity determine the result;
no first occurrence is crossed and no last occurrence is discarded. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenGap

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion
open Msg0457S11395SeenSwaps Msg0457S11395PositiveRuns

def renderCounts (counts : Nat → Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest => List.replicate (counts letter) letter ++ renderCounts counts rest

theorem countReplicate (copies letter tested : Nat) :
    (List.replicate copies letter).count tested = if tested = letter then copies else 0 := by
  induction copies with
  | zero => simp
  | succ copies ih =>
      by_cases equal : tested = letter <;> simp [List.replicate_succ, equal, Ne.symm, ih]

theorem renderCounts_count (counts : Nat → Nat) (labels : List Nat)
    (nodup : labels.Nodup) (tested : Nat) :
    (renderCounts counts labels).count tested = if tested ∈ labels then counts tested else 0 := by
  induction labels with
  | nil => simp [renderCounts]
  | cons letter rest ih =>
      have absent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [renderCounts, List.count_append, countReplicate, ih tailNodup]
      by_cases equal : tested = letter
      · subst tested
        simp [absent]
      · simp [equal]

theorem renderCounts_congr (left right : Nat → Nat) (labels : List Nat)
    (equal : ∀ tested, left tested = right tested) : renderCounts left labels = renderCounts right labels := by
  induction labels with
  | nil => rfl
  | cons letter rest ih => simp only [renderCounts, equal, ih]

def canonicalLabels (gap : List Nat) : List Nat := sortedGap (S5_107.distinctLetters gap)

theorem canonicalLabels_nodup (gap : List Nat) : (canonicalLabels gap).Nodup :=
  (sortedGap_perm (S5_107.distinctLetters gap)).nodup_iff.mpr (S5_107.distinctLetters_nodup gap)

theorem canonicalLabels_mem (gap : List Nat) (tested : Nat) : tested ∈ canonicalLabels gap ↔ tested ∈ gap :=
  (sortedGap_perm (S5_107.distinctLetters gap)).mem_iff.trans (S5_107.distinctLetters_mem_iff tested gap)

theorem canonicalLabels_eq_of_support (left right : List Nat)
    (support : ∀ tested, tested ∈ left ↔ tested ∈ right) : canonicalLabels left = canonicalLabels right := by
  apply sortedGap_eq_of_counts
  intro tested
  rw [(S5_107.distinctLetters_nodup left).count, (S5_107.distinctLetters_nodup right).count]
  simp only [S5_107.distinctLetters_mem_iff, support tested]

theorem renderOriginalCounts (gap : List Nat) (tested : Nat) :
    (renderCounts (fun x => gap.count x) (canonicalLabels gap)).count tested = gap.count tested := by
  rw [renderCounts_count _ _ (canonicalLabels_nodup gap)]
  simp only [canonicalLabels_mem]
  by_cases member : tested ∈ gap
  · simp [member]
  · simp [member, List.count_eq_zero.mpr member]

theorem normalizeCountBlocks (prefixWords suffix labels : List Nat) (counts : Nat → Nat)
    (seen : AllSeen prefixWords labels) :
    LD (prefixWords ++ renderCounts counts labels ++ suffix)
      (prefixWords ++ renderCounts (fun x => positiveCopies (counts x)) labels ++ suffix) := by
  induction labels generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter rest ih =>
      have step := normalizeSeenRun prefixWords (renderCounts counts rest ++ suffix)
        letter (counts letter) (seen letter (by simp))
      have remaining := ih (prefixWords ++ List.replicate (positiveCopies (counts letter)) letter) (by
        intro tested member
        exact List.mem_append_left _ (seen tested (List.mem_cons_of_mem letter member)))
      have first : LD (prefixWords ++ renderCounts counts (letter :: rest) ++ suffix)
          ((prefixWords ++ List.replicate (positiveCopies (counts letter)) letter) ++
            renderCounts counts rest ++ suffix) := by
        simpa [renderCounts, List.append_assoc] using step
      simpa [renderCounts, List.append_assoc] using first.trans remaining

def canonicalSeenGap (gap : List Nat) : List Nat :=
  renderCounts (fun x => positiveCopies (gap.count x)) (canonicalLabels gap)

theorem canonicalSeenGap_count (gap : List Nat) (tested : Nat) :
    (canonicalSeenGap gap).count tested = positiveCopies (gap.count tested) := by
  rw [canonicalSeenGap, renderCounts_count _ _ (canonicalLabels_nodup gap)]
  simp only [canonicalLabels_mem]
  by_cases member : tested ∈ gap
  · simp [member]
  · simp [member, List.count_eq_zero.mpr member, positiveCopies_zero]

theorem canonicalSeenGap_support (gap : List Nat) (tested : Nat) :
    tested ∈ canonicalSeenGap gap ↔ tested ∈ gap := by
  rw [← List.count_pos_iff, canonicalSeenGap_count, positiveCopies_positive_iff, List.count_pos_iff]

theorem canonicalSeenGap_parity (gap : List Nat) (tested : Nat) :
    (canonicalSeenGap gap).count tested % 2 = gap.count tested % 2 := by
  rw [canonicalSeenGap_count, positiveCopies_parity]

theorem canonicalSeenGap_reduced (gap : List Nat) (tested : Nat) :
    (canonicalSeenGap gap).count tested ≤ 2 := by
  rw [canonicalSeenGap_count]
  exact positiveCopies_le_two _

/-- Actual B12 reach, with arbitrary external contexts and arbitrary gap length. -/
theorem normalizeSeenGap (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    LD (prefixWords ++ gap ++ suffix) (prefixWords ++ canonicalSeenGap gap ++ suffix) := by
  have grouped := compareSeenGaps prefixWords gap
    (renderCounts (fun x => gap.count x) (canonicalLabels gap)) suffix
    (fun tested => (renderOriginalCounts gap tested).symm) seen
  have reduced := normalizeCountBlocks prefixWords suffix (canonicalLabels gap) (fun x => gap.count x)
    (fun tested member => seen tested ((canonicalLabels_mem gap tested).mp member))
  exact grouped.trans reduced

theorem canonicalSeenGap_eq (left right : List Nat)
    (support : ∀ tested, tested ∈ left ↔ tested ∈ right)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    canonicalSeenGap left = canonicalSeenGap right := by
  have counts : ∀ tested, positiveCopies (left.count tested) = positiveCopies (right.count tested) := by
    intro tested
    apply (positiveCopies_eq_iff _ _).2
    refine ⟨?_, parity tested⟩
    by_cases member : tested ∈ left
    · have leftPositive := List.count_pos_iff.mpr member
      have rightPositive := List.count_pos_iff.mpr ((support tested).mp member)
      omega
    · have rightAbsent : tested ∉ right := fun present => member ((support tested).mpr present)
      rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr rightAbsent]
  unfold canonicalSeenGap
  rw [canonicalLabels_eq_of_support left right support]
  exact renderCounts_congr _ _ _ counts

theorem compareSeenSupportParity (prefixWords left right suffix : List Nat)
    (seen : AllSeen prefixWords left)
    (support : ∀ tested, tested ∈ left ↔ tested ∈ right)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) := by
  have rightSeen : AllSeen prefixWords right :=
    fun tested member => seen tested ((support tested).mpr member)
  have first := normalizeSeenGap prefixWords left suffix seen
  have second := normalizeSeenGap prefixWords right suffix rightSeen
  rw [canonicalSeenGap_eq left right support parity] at first
  exact first.trans second.symm

theorem canonicalSeenGap_idempotent (gap : List Nat) :
    canonicalSeenGap (canonicalSeenGap gap) = canonicalSeenGap gap :=
  canonicalSeenGap_eq _ _ (canonicalSeenGap_support gap) (canonicalSeenGap_parity gap)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenGap

import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureRuns

/-! Suffix-aware canonical allocation in an already-seen gap. Equal gap
support is not required: support is observed after adjoining the retained
suffix. This is a local reduction/comparison layer, not global SignatureReach. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureGap

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395SeenGap Msg0457S11395FutureRuns

theorem renderOnPrefix_count (prefixWords gap : List Nat) (seen : AllSeen prefixWords gap) (tested : Nat) :
    (renderCounts (fun x => gap.count x) (canonicalLabels prefixWords)).count tested = gap.count tested := by
  rw [renderCounts_count _ _ (canonicalLabels_nodup prefixWords)]
  simp only [canonicalLabels_mem]
  by_cases member : tested ∈ prefixWords
  · simp [member]
  · have absent : tested ∉ gap := fun present => member (seen tested present)
    simp [member, List.count_eq_zero.mpr absent]

theorem normalizeFutureCountBlocks (prefixWords suffix labels : List Nat) (counts : Nat → Nat)
    (seen : AllSeen prefixWords labels) :
    LD (prefixWords ++ renderCounts counts labels ++ suffix)
      (prefixWords ++ renderCounts (fun x => futureCopies suffix x (counts x)) labels ++ suffix) := by
  induction labels generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter rest ih =>
      have step := normalizeFutureRun prefixWords (renderCounts counts rest) suffix letter (counts letter)
        (seen letter (by simp))
      have remaining := ih (prefixWords ++ List.replicate (futureCopies suffix letter (counts letter)) letter) (by
        intro tested member
        exact List.mem_append_left _ (seen tested (List.mem_cons_of_mem letter member)))
      have first : LD (prefixWords ++ renderCounts counts (letter :: rest) ++ suffix)
          ((prefixWords ++ List.replicate (futureCopies suffix letter (counts letter)) letter) ++
            renderCounts counts rest ++ suffix) := by
        simpa [renderCounts, List.append_assoc] using step
      simpa [renderCounts, List.append_assoc] using first.trans remaining

def futureGap (prefixWords gap suffix : List Nat) : List Nat :=
  renderCounts (fun x => futureCopies suffix x (gap.count x)) (canonicalLabels prefixWords)

theorem futureGap_count (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) (tested : Nat) :
    (futureGap prefixWords gap suffix).count tested = futureCopies suffix tested (gap.count tested) := by
  rw [futureGap, renderCounts_count _ _ (canonicalLabels_nodup prefixWords)]
  simp only [canonicalLabels_mem]
  by_cases member : tested ∈ prefixWords
  · simp [member]
  · have absent : tested ∉ gap := fun present => member (seen tested present)
    simp [member, List.count_eq_zero.mpr absent, futureCopies_zero]

theorem futureGap_seen (prefixWords gap suffix : List Nat) :
    AllSeen prefixWords (futureGap prefixWords gap suffix) := by
  intro tested member
  have positive := List.count_pos_iff.mpr member
  rw [futureGap, renderCounts_count _ _ (canonicalLabels_nodup prefixWords)] at positive
  by_cases present : tested ∈ prefixWords
  · exact present
  · simp [canonicalLabels_mem, present] at positive

theorem futureGap_parity (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) (tested : Nat) :
    (futureGap prefixWords gap suffix).count tested % 2 = gap.count tested % 2 := by
  rw [futureGap_count _ _ _ seen]
  exact futureCopies_parity suffix tested (gap.count tested)

theorem futureGap_supportWithSuffix (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap)
    (tested : Nat) : tested ∈ futureGap prefixWords gap suffix ++ suffix ↔ tested ∈ gap ++ suffix := by
  simp only [List.mem_append]
  have support := futureCopies_support suffix tested (gap.count tested)
  rw [← futureGap_count prefixWords gap suffix seen tested] at support
  simpa only [List.count_pos_iff] using support

theorem futureGap_count_le (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) (tested : Nat) :
    (futureGap prefixWords gap suffix).count tested ≤ gap.count tested := by
  rw [futureGap_count _ _ _ seen]
  exact futureCopies_le_self suffix tested (gap.count tested)

theorem futureGap_reduced (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) (tested : Nat) :
    (futureGap prefixWords gap suffix).count tested ≤ 2 := by
  rw [futureGap_count _ _ _ seen]
  exact futureCopies_le_two suffix tested (gap.count tested)

/-- Actual B12 derivability for arbitrary contexts, not a bounded-test premise. -/
theorem normalizeFutureGap (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    LD (prefixWords ++ gap ++ suffix) (prefixWords ++ futureGap prefixWords gap suffix ++ suffix) := by
  have grouped := compareSeenGaps prefixWords gap
    (renderCounts (fun x => gap.count x) (canonicalLabels prefixWords)) suffix
    (fun tested => (renderOnPrefix_count prefixWords gap seen tested).symm) seen
  have reduced := normalizeFutureCountBlocks prefixWords suffix (canonicalLabels prefixWords) (fun x => gap.count x)
    (fun tested member => (canonicalLabels_mem prefixWords tested).mp member)
  exact grouped.trans reduced

theorem futureGap_eq (prefixWords left right suffix : List Nat)
    (support : ∀ tested, tested ∈ left ++ suffix ↔ tested ∈ right ++ suffix)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    futureGap prefixWords left suffix = futureGap prefixWords right suffix := by
  apply renderCounts_congr
  intro tested
  apply futureCopies_eq_of_observations suffix tested _ _
  · simpa only [List.mem_append, List.count_pos_iff] using support tested
  · exact parity tested

theorem compareFutureGaps (prefixWords left right suffix : List Nat)
    (leftSeen : AllSeen prefixWords left) (rightSeen : AllSeen prefixWords right)
    (support : ∀ tested, tested ∈ left ++ suffix ↔ tested ∈ right ++ suffix)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) := by
  have first := normalizeFutureGap prefixWords left suffix leftSeen
  have second := normalizeFutureGap prefixWords right suffix rightSeen
  rw [futureGap_eq prefixWords left right suffix support parity] at first
  exact first.trans second.symm

theorem futureGap_idempotent (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    futureGap prefixWords (futureGap prefixWords gap suffix) suffix = futureGap prefixWords gap suffix := by
  apply renderCounts_congr
  intro tested
  rw [futureGap_count _ _ _ seen, futureCopies_idempotent]

/-- Natural-valued local surplus; zero is the normal form for this suffix. -/
def surplusBudget (prefixWords gap suffix : List Nat) : Nat :=
  (canonicalLabels prefixWords).foldr
    (fun tested total => gap.count tested - futureCopies suffix tested (gap.count tested) + total) 0

theorem surplusBudget_normal (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    surplusBudget prefixWords (futureGap prefixWords gap suffix) suffix = 0 := by
  have zero : ∀ tested, (futureGap prefixWords gap suffix).count tested -
      futureCopies suffix tested ((futureGap prefixWords gap suffix).count tested) = 0 := by
    intro tested
    rw [futureGap_count _ _ _ seen, futureCopies_idempotent]
    omega
  have allLabels : ∀ labels : List Nat, labels.foldr
      (fun tested total => (futureGap prefixWords gap suffix).count tested -
        futureCopies suffix tested ((futureGap prefixWords gap suffix).count tested) + total) 0 = 0 := by
    intro labels
    induction labels with
    | nil => rfl
    | cons letter rest ih => rw [List.foldr_cons, zero letter, Nat.zero_add, ih]
  exact allLabels _

theorem surplusBudget_progress (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap)
    (positive : 0 < surplusBudget prefixWords gap suffix) :
    surplusBudget prefixWords (futureGap prefixWords gap suffix) suffix < surplusBudget prefixWords gap suffix := by
  rw [surplusBudget_normal _ _ _ seen]
  exact positive

theorem normalizeFutureGapWord (head : Nat) (before gap suffix : List Nat)
    (seen : AllSeen (head :: before) gap) :
    Derives basis ⟨head, before ++ gap ++ suffix⟩
      ⟨head, before ++ futureGap (head :: before) gap suffix ++ suffix⟩ := by
  exact (show LD (head :: (before ++ gap ++ suffix))
      (head :: (before ++ futureGap (head :: before) gap suffix ++ suffix)) from
        by simpa using normalizeFutureGap (head :: before) gap suffix seen).toWord

theorem normalizeFutureGapPreservesSignature (head : Nat) (before gap suffix : List Nat)
    (seen : AllSeen (head :: before) gap) :
    Msg0457S11395Observations.SameSignature ⟨head, before ++ gap ++ suffix⟩
      ⟨head, before ++ futureGap (head :: before) gap suffix ++ suffix⟩ :=
  Msg0457S11395Signature.derives_preserve_signature (normalizeFutureGapWord head before gap suffix seen)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureGap

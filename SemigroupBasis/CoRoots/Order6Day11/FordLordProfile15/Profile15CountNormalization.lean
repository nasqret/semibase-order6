import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Anchors

/-! Global count normalization for the exact B16. Each selected letter is
normalized between its first and last anchors. Every other literal count is
preserved. The finite support fold is justified by these equations, not by
confluence of one-letter renderers. All lists and alphabets are unrestricted. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis
open Moves

namespace CountNormalization

theorem cap_idempotent (n : Nat) : cap22 (cap22 n) = cap22 n := by
  by_cases small : n < 2
  · have fixed : cap22 n = n := by simp [cap22, small]
    rw [fixed, fixed]
  · have value : cap22 n = 2 + n % 2 := by simp [cap22, small]
    rw [value, cap22_two_add]
    omega

theorem cap_le (n : Nat) : cap22 n ≤ n := by
  unfold cap22
  split <;> omega

theorem cap_bounded (n : Nat) : cap22 n ≤ 3 := by
  unfold cap22
  split <;> omega

theorem splitFirst (x : Nat) : ∀ word : List Nat, x ∈ word →
    ∃ before after : List Nat, word = before ++ x :: after ∧ x ∉ before
  | [], member => by simp at member
  | head :: rest, member => by
      by_cases equal : head = x
      · subst head
        exact ⟨[], rest, rfl, by simp⟩
      · have later : x ∈ rest := by simpa [Ne.symm equal] using member
        obtain ⟨before, after, shape, absent⟩ := splitFirst x rest later
        refine ⟨head :: before, after, ?_, ?_⟩
        · simp [shape]
        · simp [Ne.symm equal, absent]

theorem splitLast (x : Nat) (word : List Nat) (member : x ∈ word) :
    ∃ before after : List Nat, word = before ++ x :: after ∧ x ∉ after := by
  obtain ⟨before, after, shape, absent⟩ := splitFirst x word.reverse (by simpa using member)
  refine ⟨after.reverse, before.reverse, ?_, ?_⟩
  · have reversed := congrArg List.reverse shape
    simpa [List.append_assoc] using reversed
  · simpa using absent

theorem count_erase_other (letter selected : Nat) (middle : List Nat)
    (different : selected ≠ letter) :
    (Anchors.erase letter middle).count selected = middle.count selected := by
  unfold Anchors.erase
  exact List.count_filter (decide_eq_true different)

theorem count_normal_other (letter selected : Nat) (middle : List Nat)
    (different : selected ≠ letter) :
    (Anchors.normal letter middle).count selected = middle.count selected := by
  simp [Anchors.normal, List.count_replicate, Ne.symm different,
    count_erase_other letter selected middle different]

/-- One globally selected letter reaches its exact capped count. The first
and last occurrences remain anchors; all other counts are literally unchanged. -/
theorem capLetter (letter : Nat) (word : List Nat) :
    ∃ normal : List Nat, L word normal ∧
      normal.count letter = cap22 (word.count letter) ∧
      ∀ selected, selected ≠ letter → normal.count selected = word.count selected := by
  by_cases small : word.count letter < 2
  · exact ⟨word, .refl _, by simp [cap22, small], fun _ _ => rfl⟩
  · have present : letter ∈ word := by
      apply Decidable.byContradiction
      intro absent
      have zero := List.count_eq_zero.mpr absent
      omega
    obtain ⟨before, tail, rfl, absentBefore⟩ := splitFirst letter word present
    have beforeZero : before.count letter = 0 := List.count_eq_zero.mpr absentBefore
    have presentTail : letter ∈ tail := by
      apply Decidable.byContradiction
      intro absent
      have zero : tail.count letter = 0 := List.count_eq_zero.mpr absent
      simp [beforeZero, zero] at small
    obtain ⟨middle, after, rfl, absentAfter⟩ := splitLast letter tail presentTail
    have afterZero : after.count letter = 0 := List.count_eq_zero.mpr absentAfter
    refine ⟨before ++ Anchors.normal letter middle ++ after, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using (Anchors.derivesNormal letter middle).context before after
    · simp only [List.count_append, List.count_cons_self, beforeZero, afterZero,
        Anchors.count_normal, Nat.zero_add, Nat.add_zero]
      unfold cap22 tailBudget22
      rw [if_neg (by omega)]
    · intro selected different
      simp [count_normal_other letter selected middle different, Ne.symm different]

/-- Process an arbitrary finite list of selected letters. Repeated entries in
the selection list are harmless by cap idempotence. -/
theorem normalizeSelected : ∀ (letters word : List Nat),
    ∃ normal : List Nat, L word normal ∧
      ∀ selected, normal.count selected =
        if selected ∈ letters then cap22 (word.count selected) else word.count selected
  | [], word => ⟨word, .refl _, fun _ => by simp⟩
  | letter :: letters, word => by
      obtain ⟨middle, first, counts⟩ := normalizeSelected letters word
      obtain ⟨normal, second, capped, others⟩ := capLetter letter middle
      refine ⟨normal, first.trans second, ?_⟩
      intro selected
      by_cases equal : selected = letter
      · subst selected
        rw [capped, counts letter]
        by_cases member : letter ∈ letters <;> simp [member, cap_idempotent]
      · rw [others selected equal, counts selected]
        simp [equal]

/-- Every arbitrary input reaches a word whose literal counts are precisely
its period-two capped counts. No claim of global renderer uniqueness is used. -/
theorem normalizeCounts (word : List Nat) :
    ∃ normal : List Nat, L word normal ∧
      ∀ selected, normal.count selected = cap22 (word.count selected) := by
  obtain ⟨normal, reached, counts⟩ := normalizeSelected word word
  refine ⟨normal, reached, ?_⟩
  intro selected
  by_cases member : selected ∈ word
  · simpa [member] using counts selected
  · have zero : word.count selected = 0 := List.count_eq_zero.mpr member
    simpa [member, zero, cap22] using counts selected

theorem normalizeCounts_withKey (word : List Nat) :
    ∃ normal : List Nat, L word normal ∧ KeyTheory.SameKey word normal ∧
      ∀ selected, normal.count selected = cap22 (word.count selected) := by
  obtain ⟨normal, reached, counts⟩ := normalizeCounts word
  exact ⟨normal, reached, KeyTheory.listDerives_sameKey reached, counts⟩

/-- Equal keys reduce to an equal-literal-count alignment problem. The two
arbitrary words remain connected to their reductions by actual B16 derivations. -/
theorem reduceSameKey (left right : List Nat) (same : KeyTheory.SameKey left right) :
    ∃ reducedLeft reducedRight : List Nat,
      L left reducedLeft ∧ L right reducedRight ∧
      KeyTheory.SameKey reducedLeft reducedRight ∧
      (∀ selected, reducedLeft.count selected = reducedRight.count selected) ∧
      (∀ selected, reducedLeft.count selected ≤ 3) := by
  obtain ⟨reducedLeft, leftReached, leftKey, leftCounts⟩ := normalizeCounts_withKey left
  obtain ⟨reducedRight, rightReached, rightKey, rightCounts⟩ := normalizeCounts_withKey right
  refine ⟨reducedLeft, reducedRight, leftReached, rightReached,
    leftKey.symm.trans (same.trans rightKey), ?_, ?_⟩
  · intro selected
    rw [leftCounts, rightCounts]
    exact same.counts selected
  · intro selected
    rw [leftCounts]
    exact cap_bounded _

end CountNormalization
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

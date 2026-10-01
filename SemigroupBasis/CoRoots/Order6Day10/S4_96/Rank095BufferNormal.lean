import SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros

/-! Affine normalization with an explicit conserved square buffer. Every pair
removed from an affine parity block is retained in the displayed B5 word. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferNormal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros

theorem normalSegments_eq_nil_iff (letters : List Nat) :
    affineParityNormalSegments letters = [] ↔ letters = [] := by
  cases letters with
  | nil => simp [affineParityNormalSegments]
  | cons x xs =>
      constructor
      · intro impossible
        exact False.elim (affineParityNormalSegments_cons_ne_nil x xs impossible)
      · simp

/-- The finite affine renderer is retained verbatim. Only a prefix buffer is
added, and every buffer letter is guarded by an actual final marker. -/
theorem bufferedNormal : ∀ letters : List Nat,
    ∃ buffer : List Nat,
      D letters (doubleLetters buffer ++
        affineParityRender (affineParityNormalSegments letters)) ∧
      (∀ x, x ∈ buffer → x ∈ affineParityMarkers (affineParityNormalSegments letters))
  | [] => by
      refine ⟨[], ?_, ?_⟩
      · exact ListDerives.refl _
      · intro x member
        simp at member
  | x :: xs => by
      obtain ⟨buffer, derived, bufferGuard⟩ := bufferedNormal xs
      have segmentsNormal := affineParityNormalSegments_normal xs
      cases segmentsEq : affineParityNormalSegments xs with
      | nil =>
          have xsNil : xs = [] := (normalSegments_eq_nil_iff xs).mp segmentsEq
          subst xs
          refine ⟨[], ?_, ?_⟩
          · exact ListDerives.refl _
          · intro z member
            simp at member
      | cons segment rest =>
          cases segment with
          | mk parity marker =>
              rw [segmentsEq] at derived bufferGuard segmentsNormal
              cases segmentsNormal with
              | cons parityNodup markerFresh parityGuard restNormal =>
                  have wholeNormal : AffineParitySegmentsNormal (⟨parity, marker⟩ :: rest) :=
                    .cons parityNodup markerFresh parityGuard restNormal
                  have renderBufferGuard : ∀ z, z ∈ buffer →
                      z ∈ affineParityRender (⟨parity, marker⟩ :: rest) := by
                    intro z member
                    exact (wholeNormal.mem_render_iff_marker z).mpr (bufferGuard z member)
                  have base : D (x :: xs)
                      (doubleLetters buffer ++ x :: affineParityRender (⟨parity, marker⟩ :: rest)) := by
                    have first : D (x :: xs)
                        ([x] ++ doubleLetters buffer ++ affineParityRender (⟨parity, marker⟩ :: rest)) := by
                      simpa [List.append_assoc] using derived.prepend [x]
                    have second := bufferSlide buffer [x]
                      (affineParityRender (⟨parity, marker⟩ :: rest)) renderBufferGuard
                    simpa [List.append_assoc] using first.trans second
                  by_cases xSeen : x ∈ affineParityMarkers (⟨parity, marker⟩ :: rest)
                  · have normalEq : affineParityNormalSegments (x :: xs) =
                        ⟨affineParityToggle x parity, marker⟩ :: rest := by
                      rw [affineParityNormalSegments, segmentsEq]
                      exact if_pos xSeen
                    let suffix := marker :: affineParityRender rest
                    have blockGuard : ∀ z, z ∈ parity → z ∈ suffix := by
                      intro z member
                      rcases parityGuard z member with equal | later
                      · subst z
                        exact List.Mem.head _
                      · exact List.Mem.tail _ (affineParityMarker_mem_render later)
                    by_cases xInBlock : x ∈ parity
                    · have exposed : D (x :: (parity ++ suffix))
                          ([x, x] ++ parity.erase x ++ suffix) := by
                        have permutation := guardedPermutation suffix
                          (List.perm_cons_erase xInBlock) blockGuard
                        simpa [List.append_assoc] using permutation.prepend [x]
                      refine ⟨buffer ++ [x], ?_, ?_⟩
                      · have next : D
                            (doubleLetters buffer ++ x :: affineParityRender (⟨parity, marker⟩ :: rest))
                            (doubleLetters (buffer ++ [x]) ++
                              affineParityRender (affineParityNormalSegments (x :: xs))) := by
                          simpa [normalEq, affineParityToggle, xInBlock, affineParityRender,
                            suffix, doubleLetters, List.append_assoc] using exposed.prepend (doubleLetters buffer)
                        exact base.trans next
                      · intro z member
                        rcases List.mem_append.mp member with old | added
                        · simpa [normalEq, affineParityMarkers] using bufferGuard z old
                        · have equal : z = x := by simpa using added
                          subst z
                          simpa [normalEq, affineParityMarkers] using xSeen
                    · refine ⟨buffer, ?_, ?_⟩
                      · simpa [normalEq, affineParityToggle, xInBlock, affineParityRender,
                          List.append_assoc] using base
                      · intro z member
                        simpa [normalEq, affineParityMarkers] using bufferGuard z member
                  · have normalEq : affineParityNormalSegments (x :: xs) =
                        ⟨[], x⟩ :: ⟨parity, marker⟩ :: rest := by
                      rw [affineParityNormalSegments, segmentsEq]
                      exact if_neg xSeen
                    refine ⟨buffer, ?_, ?_⟩
                    · simpa [normalEq, affineParityRender, List.append_assoc] using base
                    · intro z member
                      change z ∈ affineParityMarkers (affineParityNormalSegments (x :: xs))
                      rw [normalEq]
                      exact List.Mem.tail _ (bufferGuard z member)

theorem bufferedNormal_word (word : Word Nat) :
    ∃ buffer : List Nat,
      D word.toList (doubleLetters buffer ++ affineParityRender (affineParityNormalSegments word.toList)) ∧
      (∀ x, x ∈ buffer → x ∈ affineParityRender (affineParityNormalSegments word.toList)) := by
  obtain ⟨buffer, derived, guard⟩ := bufferedNormal word.toList
  refine ⟨buffer, derived, ?_⟩
  intro x member
  exact affineParityMarker_mem_render (guard x member)

end SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferNormal

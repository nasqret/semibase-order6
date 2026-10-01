import SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferNormal

/-! The remaining square buffer has parity, not arbitrary affine history.
All reductions are guarded in an unchanged nonempty renderer suffix. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferParity

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros

theorem mem_doubleLetters {x : Nat} {buffer : List Nat} :
    x ∈ doubleLetters buffer ↔ x ∈ buffer := by
  simp [doubleLetters]

theorem count_doubleLetters (x : Nat) (buffer : List Nat) :
    (doubleLetters buffer).count x = 2 * buffer.count x := by
  induction buffer with
  | nil => simp
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        simp only [doubleLetters_cons, List.count_cons_self, ih]
        omega
      · simp only [doubleLetters_cons, List.count_cons_of_ne equal, ih]

theorem mem_parityReduce_source {x : Nat} : ∀ buffer : List Nat,
    x ∈ parityReduce buffer → x ∈ buffer
  | [] => by simp [parityReduce]
  | y :: ys => by
      intro member
      by_cases present : y ∈ parityReduce ys
      · rw [parityReduce, if_pos present] at member
        exact List.Mem.tail _ (mem_parityReduce_source ys (List.mem_of_mem_erase member))
      · rw [parityReduce, if_neg present] at member
        rcases List.mem_cons.mp member with equal | later
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.Mem.tail _ (mem_parityReduce_source ys later)

theorem bufferPermutation (suffix : List Nat) {left right : List Nat}
    (permutation : left.Perm right) (guard : ∀ x, x ∈ left → x ∈ suffix) :
    D (doubleLetters left ++ suffix) (doubleLetters right ++ suffix) := by
  apply guardedPermutation suffix (permutation.flatMap_right (fun x => [x, x]))
  intro x member
  exact guard x (mem_doubleLetters.mp member)

theorem reduceBuffer (buffer suffix : List Nat)
    (guard : ∀ x, x ∈ buffer → x ∈ suffix) :
    D (doubleLetters buffer ++ suffix) (doubleLetters (parityReduce buffer) ++ suffix) := by
  revert guard
  induction buffer with
  | nil =>
      intro _
      exact ListDerives.refl _
  | cons x xs ih =>
      intro guard
      have tailGuard : ∀ z, z ∈ xs → z ∈ suffix :=
        fun z hz => guard z (List.Mem.tail x hz)
      have reducedGuard : ∀ z, z ∈ parityReduce xs → z ∈ suffix :=
        fun z hz => tailGuard z (mem_parityReduce_source xs hz)
      have first : D (doubleLetters (x :: xs) ++ suffix)
          ([x, x] ++ doubleLetters (parityReduce xs) ++ suffix) := by
        simpa [List.append_assoc] using (ih tailGuard).prepend [x, x]
      by_cases present : x ∈ parityReduce xs
      · have second : D ([x, x] ++ doubleLetters (parityReduce xs) ++ suffix)
            ([x, x, x, x] ++ doubleLetters ((parityReduce xs).erase x) ++ suffix) := by
          have permuted := bufferPermutation suffix (List.perm_cons_erase present) reducedGuard
          simpa [List.append_assoc] using permuted.prepend [x, x]
        have xGuard : x ∈ doubleLetters ((parityReduce xs).erase x) ++ suffix := by
          simp [guard x (by simp)]
        have third : D ([x, x, x, x] ++ doubleLetters ((parityReduce xs).erase x) ++ suffix)
            (doubleLetters (parityReduce (x :: xs)) ++ suffix) := by
          simpa [parityReduce, present, List.append_assoc] using
            deleteFour x (doubleLetters ((parityReduce xs).erase x) ++ suffix) xGuard
        exact first.trans (second.trans third)
      · simpa [parityReduce, present, List.append_assoc] using first

theorem buffersOfSameParity (left right suffix : List Nat)
    (leftGuard : ∀ x, x ∈ left → x ∈ suffix)
    (rightGuard : ∀ x, x ∈ right → x ∈ suffix)
    (sameParity : ∀ x, left.count x % 2 = right.count x % 2) :
    D (doubleLetters left ++ suffix) (doubleLetters right ++ suffix) := by
  have leftReduction := reduceBuffer left suffix leftGuard
  have rightReduction := reduceBuffer right suffix rightGuard
  have middle := bufferPermutation suffix (parityReduce_perm_of_parity_eq sameParity)
    (fun x hx => leftGuard x (mem_parityReduce_source left hx))
  exact leftReduction.trans (middle.trans rightReduction.symm)

/-- Only arithmetic, not cancellation in the semigroup: a common renderer
and doubled buffer counts leave exactly the buffer's residue modulo two. -/
theorem bufferParity_of_modFour (left right suffix : List Nat)
    (same : ∀ x,
      (doubleLetters left ++ suffix).count x % 4 =
        (doubleLetters right ++ suffix).count x % 4) :
    ∀ x, left.count x % 2 = right.count x % 2 := by
  intro x
  have counts := same x
  rw [List.count_append, List.count_append, count_doubleLetters, count_doubleLetters] at counts
  omega

theorem derives_count_mod_four {left right : List Nat} (derived : D left right) :
    ∀ x, left.count x % 4 = right.count x % 4 := by
  cases derived with
  | empty => intro x; rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have valid : (Identity.mk (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail)).SatisfiedBy rightTable.semigroup :=
        fun valuation => wordDerivation.sound modelsRight valuation
      simpa [listWordOfCons, Word.toList] using
        CoRoots.S5_505Family.S5_506.valid_count_mod_four _ valid

theorem listDerives_to_word {left right : Word Nat}
    (derived : D left.toList right.toList) : Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact ListDerives.toWord derived

theorem segmentPermutation_markers : ∀ {left right : List AffineParitySegment},
    AffineParitySegmentsPerm left right → affineParityMarkers left = affineParityMarkers right
  | [], [], .nil => rfl
  | ⟨leftBlock, marker⟩ :: leftRest, ⟨rightBlock, .(marker)⟩ :: rightRest,
      .cons _ restPerm => congrArg (List.cons marker) (segmentPermutation_markers restPerm)

theorem segmentPermutationDerives : ∀ {left right : List AffineParitySegment},
    AffineParitySegmentsPerm left right →
    AffineParitySegmentsNormal left → AffineParitySegmentsNormal right →
    D (affineParityRender left) (affineParityRender right)
  | [], [], .nil, .nil, .nil => ListDerives.refl _
  | ⟨leftBlock, marker⟩ :: leftRest, ⟨rightBlock, .(marker)⟩ :: rightRest,
      .cons blockPerm restPerm,
      .cons leftNodup leftFresh leftGuard leftNormal,
      .cons rightNodup rightFresh rightGuard rightNormal => by
      have guard : ∀ x, x ∈ leftBlock → x ∈ marker :: affineParityRender leftRest := by
        intro x member
        rcases leftGuard x member with equal | later
        · subst x
          exact List.Mem.head _
        · exact List.Mem.tail _ (affineParityMarker_mem_render later)
      have first := guardedPermutation (marker :: affineParityRender leftRest) blockPerm guard
      have tail := segmentPermutationDerives restPerm leftNormal rightNormal
      have second := (tail.prepend [marker]).prepend rightBlock
      simpa [affineParityRender, List.append_assoc] using first.trans second

end SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095BufferParity

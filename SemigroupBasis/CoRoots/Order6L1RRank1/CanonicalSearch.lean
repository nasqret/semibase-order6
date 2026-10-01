import SemigroupBasis.Equational

/-!
# Signature-driven shortlex representatives for the L1R rank-1 root

This module contains only the common, reducible search shell used by the
twelve Layer-A structural canonicalizers.  A leaf supplies an independently
authored structural signature and the support projection of that signature.
The search then chooses the first word, in length-then-lexicographic order,
with the same structural signature.

The search ceiling depends only on the signature support, never on the source
word.  Consequently equal signatures compute to definitionally identical
canonical representatives.  The generous `4 * |support| + 1` ceiling covers
the exported factor normal forms used by this root; existence and derivation
to the selected representative belong to later proof layers, not Layer A.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1

open SemigroupBasis

@[reducible] private def insertNat (letter : Nat) : List Nat → List Nat
  | [] => [letter]
  | head :: tail =>
      if letter ≤ head then
        letter :: head :: tail
      else
        head :: insertNat letter tail

/-- Kernel-reducible ascending sort, avoiding the native merge-sort boundary
in generated ordinary `decide` examples. -/
@[reducible] def sortNat : List Nat → List Nat
  | [] => []
  | head :: tail => insertNat head (sortNat tail)

@[reducible] def sortedSupport (letters : List Nat) : List Nat :=
  sortNat letters.eraseDups

/-! ## Structural facts for the shared insertion sort -/

private theorem mem_insertNat_iff (tested letter : Nat) :
    ∀ letters : List Nat,
      tested ∈ insertNat letter letters ↔
        tested = letter ∨ tested ∈ letters
  | [] => by simp [insertNat]
  | head :: tail => by
      simp only [insertNat]
      split <;>
        simp [mem_insertNat_iff tested letter tail,
          or_left_comm, or_assoc]

/-- Insertion sorting preserves exactly the underlying support. -/
theorem mem_sortNat_iff (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ sortNat letters ↔ tested ∈ letters
  | [] => by simp [sortNat]
  | head :: tail => by
      simp [sortNat, mem_insertNat_iff,
        mem_sortNat_iff tested tail, or_left_comm]

private theorem insertNat_perm (letter : Nat) :
    ∀ letters : List Nat,
      (insertNat letter letters).Perm (letter :: letters)
  | [] => by simp [insertNat]
  | head :: tail => by
      simp only [insertNat]
      split
      · exact List.Perm.refl _
      · exact
          (List.Perm.cons head (insertNat_perm letter tail)).trans
            (List.Perm.swap head letter tail).symm

/-- Insertion sorting is a permutation of its input list. -/
theorem sortNat_perm :
    ∀ letters : List Nat,
      (sortNat letters).Perm letters
  | [] => List.Perm.refl []
  | head :: tail =>
      (insertNat_perm head (sortNat tail)).trans
        (List.Perm.cons head (sortNat_perm tail))

private theorem insertNat_nodup (letter : Nat) :
    ∀ {letters : List Nat},
      letters.Nodup → letter ∉ letters →
        (insertNat letter letters).Nodup
  | [], _, _ => by simp [insertNat]
  | head :: tail, nodup, absent => by
      have parts := List.nodup_cons.mp nodup
      have headNeLetter : head ≠ letter := by
        intro equal
        subst head
        exact absent (List.Mem.head tail)
      have letterAbsentTail : letter ∉ tail := by
        intro member
        exact absent (List.Mem.tail head member)
      simp only [insertNat]
      split
      · exact List.nodup_cons.mpr ⟨absent, nodup⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, insertNat_nodup letter parts.2 letterAbsentTail⟩
        rw [mem_insertNat_iff]
        simp [headNeLetter, parts.1]

/-- Sorting a duplicate-free list remains duplicate-free. -/
theorem sortNat_nodup :
    ∀ {letters : List Nat},
      letters.Nodup → (sortNat letters).Nodup
  | [], _ => by simp [sortNat]
  | head :: tail, nodup => by
      have parts := List.nodup_cons.mp nodup
      simp only [sortNat]
      apply insertNat_nodup head (sortNat_nodup parts.2)
      intro member
      exact parts.1 ((mem_sortNat_iff head tail).mp member)

private theorem insertNat_pairwise_le (letter : Nat) :
    ∀ {letters : List Nat},
      letters.Pairwise (· ≤ ·) →
        (insertNat letter letters).Pairwise (· ≤ ·)
  | [], _ => by simp [insertNat]
  | head :: tail, ordered => by
      have parts := List.pairwise_cons.mp ordered
      simp only [insertNat]
      split <;> rename_i comparison
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ordered⟩
        intro tested member
        rcases List.mem_cons.mp member with rfl | member
        · exact comparison
        · exact Nat.le_trans comparison (parts.1 tested member)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, insertNat_pairwise_le letter parts.2⟩
        intro tested member
        rw [mem_insertNat_iff] at member
        rcases member with rfl | member
        · omega
        · exact parts.1 tested member

/-- The shared insertion sort produces an ascending list. -/
theorem sortNat_pairwise_le :
    ∀ letters : List Nat,
      (sortNat letters).Pairwise (· ≤ ·)
  | [] => by simp [sortNat]
  | head :: tail => by
      simp only [sortNat]
      exact insertNat_pairwise_le head (sortNat_pairwise_le tail)

private theorem mem_eraseDups_iff [BEq α] [LawfulBEq α] :
    ∀ (entry : α) (entries : List α),
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | entry, [] => by simp
  | entry, head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  _ entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem nodup_eraseDups [BEq α] [LawfulBEq α] :
    ∀ entries : List α, entries.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        have filteredMember :=
          (mem_eraseDups_iff head
            (tail.filter fun candidate => !candidate == head)).mp member
        simpa using filteredMember
      · exact nodup_eraseDups
          (tail.filter fun candidate => !candidate == head)
termination_by
  entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

/-- Membership in the sorted support is literal source membership. -/
theorem mem_sortedSupport_iff (tested : Nat) (letters : List Nat) :
    tested ∈ sortedSupport letters ↔ tested ∈ letters := by
  unfold sortedSupport
  rw [mem_sortNat_iff, mem_eraseDups_iff]

/-- The sorted support contains no repeated letter. -/
theorem sortedSupport_nodup (letters : List Nat) :
    (sortedSupport letters).Nodup := by
  unfold sortedSupport
  exact sortNat_nodup (nodup_eraseDups letters)

/-- The sorted support is ascending. -/
theorem sortedSupport_pairwise_le (letters : List Nat) :
    (sortedSupport letters).Pairwise (· ≤ ·) := by
  unfold sortedSupport
  exact sortNat_pairwise_le letters.eraseDups

/-- Two ascending duplicate-free natural-number lists with the same support
are literally equal. -/
theorem natList_eq_of_pairwise_le_nodup_mem_iff
    {left right : List Nat}
    (leftOrdered : left.Pairwise (· ≤ ·))
    (rightOrdered : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have present := (sameSupport head).2 (by simp)
          contradiction
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil =>
          have present := (sameSupport leftHead).1 (by simp)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameSupport leftHead).1 (by simp)
          have rightHeadInLeft :=
            (sameSupport rightHead).2 (by simp)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightOrdered tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftOrdered tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply inductionHypothesis
            leftOrdered.tail rightOrdered.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameSupport letter

/-- The support sorter depends only on set membership. -/
theorem sortedSupport_eq_of_mem_iff
    {left right : List Nat}
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    sortedSupport left = sortedSupport right := by
  apply natList_eq_of_pairwise_le_nodup_mem_iff
    (sortedSupport_pairwise_le left)
    (sortedSupport_pairwise_le right)
    (sortedSupport_nodup left)
    (sortedSupport_nodup right)
  intro letter
  rw [mem_sortedSupport_iff, mem_sortedSupport_iff]
  exact sameSupport letter

/-- Transparent first-occurrence order for the generated ordinary `decide`
boundary. -/
@[reducible] def reducibleFirstOccurrences : List Nat → List Nat
  | [] => []
  | letter :: remaining =>
      letter :: (reducibleFirstOccurrences remaining).filter
        (fun other => decide (other ≠ letter))

/-- Transparent copy of the unrestricted Edmunds square-block normalizer. -/
@[reducible] def reducibleEdmundsNormalList : List Nat → List Nat
  | [] => []
  | letter :: remaining =>
      let rest := reducibleEdmundsNormalList remaining
      if letter ∈ rest then
        letter :: letter :: rest.filter (fun other => decide (other ≠ letter))
      else
        letter :: rest

/-- Split a nonempty word into the list before its final letter and its final
letter.  The empty-tail branch is the singleton convention. -/
@[reducible] def reducibleSplitPrefixFinalData :
    Nat → List Nat → List Nat × Nat
  | head, [] => ([], head)
  | head, next :: remaining =>
      match remaining with
      | [] => ([head], next)
      | _ :: _ =>
          let split := reducibleSplitPrefixFinalData next remaining
          (head :: split.1, split.2)

/-- Transparent `S4_73` exported normal list: normalize to Edmunds blocks,
then duplicate a nonempty suffix. -/
@[reducible] def reducibleS4_73NormalList (word : Word Nat) : List Nat :=
  match reducibleEdmundsNormalList word.toList with
  | [] => word.toList
  | [letter] => [letter]
  | initial :: next :: remaining =>
      initial :: (next :: remaining) ++ (next :: remaining)

/-- Transparent open-or-closed `S4_64` normal list. -/
@[reducible] def reducibleS4_64NormalList (word : Word Nat) : List Nat :=
  match word.tail with
  | [] => word.toList
  | _ :: _ =>
      let split := reducibleSplitPrefixFinalData word.head word.tail
      match reducibleFirstOccurrences split.1 with
      | [] => word.toList
      | initial :: remaining =>
          if split.2 ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [split.2])

/-- All lists of exactly `length` over an already sorted alphabet, in
lexicographic order. -/
@[reducible] def listsOfLength (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      alphabet.flatMap fun letter =>
        (listsOfLength alphabet length).map fun suffix =>
          letter :: suffix

/-- All nonempty lists through an inclusive maximum length, in shortlex
order. -/
@[reducible] def nonemptyListsThrough
    (alphabet : List Nat) (maximumLength : Nat) : List (List Nat) :=
  (List.range maximumLength).flatMap fun offset =>
    listsOfLength alphabet (offset + 1)

/-- Total conversion used during bounded kernel reduction. -/
@[reducible] def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => Word.mk head tail

@[reducible] private def firstWithSignature
    {σ : Type} [DecidableEq σ]
    (signature : Word Nat → σ) (target : σ) :
    List (List Nat) → Option (List Nat)
  | [] => none
  | candidate :: remaining =>
      if signature (wordOfList candidate) = target then
        some candidate
      else
        firstWithSignature signature target remaining

/-- Choose the shortlex-first word with the requested structural signature.

The fallback is support-determined, so this function still respects literal
signature equality before the later existence proof is installed. -/
@[reducible] def canonicalizeBySignature
    {σ : Type} [DecidableEq σ]
    (signature : Word Nat → σ)
    (supportOf : σ → List Nat)
    (word : Word Nat) : Word Nat :=
  let target := signature word
  let support := supportOf target
  let maximumLength := 4 * support.length + 1
  match firstWithSignature signature target
      (nonemptyListsThrough support maximumLength) with
  | some candidate => wordOfList candidate
  | none => wordOfList support

theorem canonicalizeBySignature_eq_of_signature_eq
    {σ : Type} [DecidableEq σ]
    (signature : Word Nat → σ)
    (supportOf : σ → List Nat)
    {left right : Word Nat}
    (same : signature left = signature right) :
    canonicalizeBySignature signature supportOf left =
      canonicalizeBySignature signature supportOf right := by
  simp only [canonicalizeBySignature, same]

end SemigroupBasis.CoRoots.Order6L1RRank1

import SemigroupBasis.Examples.SymmetricThreeCompletenessSchreier

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

/-- Sorting the duplicate-free parity representative preserves its
duplicate-free property. -/
theorem canonicalParity_nodup (letters : List Nat) :
    (canonicalParity letters).Nodup := by
  exact (parityReduce_perm_canonicalParity letters).nodup_iff.mp
    (parityReduce_nodup letters)

@[simp]
theorem canonicalParity_nil : canonicalParity [] = [] := by
  simp [canonicalParity, parityReduce]

/-- The canonical parity representative is sorted increasingly. -/
theorem canonicalParity_pairwise (letters : List Nat) :
    (canonicalParity letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true first) (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted := List.pairwise_mergeSort transitive total
    (parityReduce letters)
  exact sorted.imp fun relation => of_decide_eq_true relation

theorem mem_canonicalParity_iff (tested : Nat) (letters : List Nat) :
    tested ∈ canonicalParity letters ↔ letters.count tested % 2 = 1 := by
  have permutation := parityReduce_perm_canonicalParity letters
  constructor
  · intro member
    exact (mem_parityReduce_iff tested letters).mp
      (permutation.mem_iff.mpr member)
  · intro odd
    exact permutation.mem_iff.mp
      ((mem_parityReduce_iff tested letters).mpr odd)

/-- Canonical parity preserves every occurrence count modulo two. -/
theorem canonicalParity_count_mod_two (tested : Nat) (letters : List Nat) :
    (canonicalParity letters).count tested % 2 =
      letters.count tested % 2 := by
  rw [(canonicalParity_nodup letters).count]
  by_cases odd : letters.count tested % 2 = 1
  · simp [mem_canonicalParity_iff, odd]
  · have bound := Nat.mod_lt (letters.count tested) (by decide : 0 < 2)
    have even : letters.count tested % 2 = 0 := by omega
    simp [mem_canonicalParity_iff, even]

/-- Pointwise parity counts determine the sorted representative exactly. -/
theorem canonicalParity_eq_of_modCounts
    (left right : List Nat)
    (counts : ∀ tested,
      left.count tested % 2 = right.count tested % 2) :
    canonicalParity left = canonicalParity right := by
  have permutation :
      (canonicalParity left).Perm (canonicalParity right) :=
    (parityReduce_perm_canonicalParity left).symm.trans <|
      (parityReduce_perm_of_parity_eq counts).trans <|
        parityReduce_perm_canonicalParity right
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (canonicalParity_pairwise left)
    (canonicalParity_pairwise right)
    permutation

@[simp]
theorem canonicalParity_idempotent (letters : List Nat) :
    canonicalParity (canonicalParity letters) = canonicalParity letters := by
  apply canonicalParity_eq_of_modCounts
  intro tested
  exact canonicalParity_count_mod_two tested letters

/-- Canonicalizing an accumulated parity state before scanning a suffix does
not alter the final state. -/
theorem canonicalParity_append_stable (left right : List Nat) :
    canonicalParity (canonicalParity left ++ right) =
      canonicalParity (left ++ right) := by
  apply canonicalParity_eq_of_modCounts
  intro tested
  simp only [List.count_append]
  have parity := canonicalParity_count_mod_two tested left
  omega

@[simp]
theorem toggleState_canonical (state : List Nat) (letter : Nat) :
    canonicalParity (toggleState state letter) =
      toggleState state letter := by
  unfold toggleState
  exact canonicalParity_idempotent _

theorem mem_canonicalParity_source
    {tested : Nat} {letters : List Nat}
    (member : tested ∈ canonicalParity letters) :
    tested ∈ letters := by
  have odd := (mem_canonicalParity_iff tested letters).mp member
  apply List.count_pos_iff.mp
  omega

/-- A scan begun at a canonicalized state ends at the canonical parity of the
initial state followed by all scanned letters. -/
theorem finalStateFrom_canonical :
    ∀ (state letters : List Nat),
      finalStateFrom (canonicalParity state) letters =
        canonicalParity (state ++ letters)
  | state, [] => by
      simp only [finalStateFrom, List.append_nil]
  | state, letter :: rest => by
      have toggled :
          toggleState (canonicalParity state) letter =
            canonicalParity (state ++ [letter]) := by
        exact canonicalParity_append_stable state [letter]
      simp only [finalStateFrom]
      rw [toggled, finalStateFrom_canonical (state ++ [letter]) rest]
      congr 1
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem finalStateFrom_nil (letters : List Nat) :
    finalStateFrom [] letters = canonicalParity letters := by
  have result := finalStateFrom_canonical [] letters
  rw [canonicalParity_nil, List.nil_append] at result
  exact result

/-- Every state recorded by a scan that starts canonically is itself a
canonical parity state. -/
theorem transitionKeysFrom_tail_canonical :
    ∀ (state letters : List Nat) (key : Word Nat),
      canonicalParity state = state →
      key ∈ transitionKeysFrom state letters →
      canonicalParity key.tail = key.tail
  | _, [], _, _, member => by
      simp only [transitionKeysFrom, List.not_mem_nil] at member
  | state, letter :: rest, key, stateCanonical, member => by
      simp only [transitionKeysFrom, List.mem_cons] at member
      rcases member with equality | member
      · subst key
        simpa only [transitionKey_tail] using stateCanonical
      · exact transitionKeysFrom_tail_canonical
          (toggleState state letter) rest key
          (toggleState_canonical state letter) member

theorem transitionKeysFrom_nil_tail_canonical
    {letters : List Nat} {key : Word Nat}
    (member : key ∈ transitionKeysFrom [] letters) :
    canonicalParity key.tail = key.tail := by
  exact transitionKeysFrom_tail_canonical [] letters key
    canonicalParity_nil member

end SemigroupBasis.Examples.SymmetricThreeCompleteness

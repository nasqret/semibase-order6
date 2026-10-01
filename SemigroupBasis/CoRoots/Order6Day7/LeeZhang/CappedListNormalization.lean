import SemigroupBasis.Normalization.StagedNormalization

/-! A terminating capped/sorted list normalizer and its exact contextual rewrite
obligations. The relation may be a word window with protected endpoints. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CappedList

open SemigroupBasis

def reduce (limit : Nat → Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := reduce limit rest
      if reduced.count letter < limit letter then letter :: reduced else reduced

theorem count_reduce (limit : Nat → Nat) (tested : Nat) (word : List Nat) :
    (reduce limit word).count tested = min (word.count tested) (limit tested) := by
  induction word with
  | nil => simp [reduce]
  | cons letter rest ih =>
      simp only [reduce]
      split <;> rename_i bound
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at bound
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal), List.count_cons_of_ne (Ne.symm equal), ih]
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, ih]
          rw [ih] at bound
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal), ih]

theorem reduce_length_le (limit : Nat → Nat) (word : List Nat) :
    (reduce limit word).length ≤ word.length := by
  induction word with
  | nil => simp [reduce]
  | cons letter rest ih =>
      simp only [reduce]
      split <;> simp only [List.length_cons] <;> omega

def normal (limit : Nat → Nat) (word : List Nat) : List Nat :=
  (reduce limit word).mergeSort (fun left right : Nat => decide (left ≤ right))

theorem normal_perm (limit : Nat → Nat) (word : List Nat) :
    (normal limit word).Perm (reduce limit word) := List.mergeSort_perm _ _

theorem count_normal (limit : Nat → Nat) (tested : Nat) (word : List Nat) :
    (normal limit word).count tested = min (word.count tested) (limit tested) := by
  rw [(List.perm_iff_count.mp (normal_perm limit word)) tested, count_reduce]

theorem normal_sorted (limit : Nat → Nat) (word : List Nat) :
    (normal limit word).Pairwise (fun left right => left ≤ right) := by
  have transitive : ∀ left middle right : Nat,
      decide (left ≤ middle) = true → decide (middle ≤ right) = true → decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true first) (of_decide_eq_true second))
  have total : ∀ left right : Nat, (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  exact (List.pairwise_mergeSort transitive total (reduce limit word)).imp
    (fun relation => of_decide_eq_true relation)

theorem normal_eq_of_counts (leftLimit rightLimit : Nat → Nat) (left right : List Nat)
    (counts : ∀ letter, min (left.count letter) (leftLimit letter) =
      min (right.count letter) (rightLimit letter)) :
    normal leftLimit left = normal rightLimit right := by
  have permutation : (normal leftLimit left).Perm (normal rightLimit right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [count_normal, count_normal, counts letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (normal_sorted leftLimit left) (normal_sorted rightLimit right) permutation

theorem normal_idempotent (limit : Nat → Nat) (word : List Nat) :
    normal limit (normal limit word) = normal limit word := by
  apply normal_eq_of_counts
  intro letter
  rw [count_normal]
  simp [Nat.min_assoc]

theorem normal_length_le (limit : Nat → Nat) (word : List Nat) :
    (normal limit word).length ≤ word.length := by
  rw [(normal_perm limit word).length_eq]
  exact reduce_length_le limit word

theorem count_filter_ne (word : List Nat) (removed tested : Nat) :
    (word.filter (fun letter => decide (letter ≠ removed))).count tested =
      if tested = removed then 0 else word.count tested := by
  by_cases equal : tested = removed
  · subst tested
    rw [if_pos rfl]
    exact List.count_eq_zero.mpr (by simp)
  · rw [if_neg equal]
    exact List.count_filter (by simpa using equal)

structure Rules (D : Normalization.System (List Nat)) (limit : Nat → Nat) : Prop where
  swap : ∀ (front : List Nat) (left right : Nat) (rest : List Nat),
    D.rel (front ++ left :: right :: rest) (front ++ right :: left :: rest)
  contract : ∀ (front : List Nat) (letter : Nat) (rest : List Nat),
    D.rel (front ++ List.replicate (limit letter + 1) letter ++ rest)
      (front ++ List.replicate (limit letter) letter ++ rest)

namespace Rules

variable {D : Normalization.System (List Nat)} {limit : Nat → Nat}

theorem permute (rules : Rules D limit) {left right : List Nat} (permutation : left.Perm right) :
    ∀ front rest, D.rel (front ++ left ++ rest) (front ++ right ++ rest) := by
  induction permutation with
  | nil => intro front rest; exact D.refl _
  | @cons letter left right permutation ih =>
      intro front rest
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using ih (front ++ [letter]) rest
  | swap left right tail =>
      intro front rest
      simpa only [List.append_assoc, List.cons_append] using rules.swap front right left (tail ++ rest)
  | @trans left middle right first second firstIH secondIH =>
      intro front rest
      exact D.trans (firstIH front rest) (secondIH front rest)

theorem delete_excess (rules : Rules D limit) (front : List Nat) (letter : Nat) (rest : List Nat)
    (count : rest.count letter = limit letter) :
    D.rel (front ++ letter :: rest) (front ++ rest) := by
  let remainder := rest.filter (fun tested => decide (tested ≠ letter))
  have targetPermutation : rest.Perm (List.replicate (limit letter) letter ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    rw [List.count_append]
    simp only [remainder, count_filter_ne, List.count_replicate]
    by_cases equal : tested = letter
    · subst tested
      simp [count]
    · simp [equal, Ne.symm equal]
  have sourcePermutation : (letter :: rest).Perm (List.replicate (limit letter + 1) letter ++ remainder) := by
    simpa only [List.replicate_succ, List.cons_append] using List.Perm.cons letter targetPermutation
  have expose := rules.permute sourcePermutation front []
  have contract := rules.contract front letter remainder
  have restore := rules.permute targetPermutation.symm front []
  simp only [List.append_nil] at expose restore
  simp only [List.append_assoc] at contract
  exact D.trans expose (D.trans contract restore)

/-- Structural recursion on the input list; no bounded rewrite search is a premise. -/
theorem reduce_sound (rules : Rules D limit) : ∀ front word,
    D.rel (front ++ word) (front ++ reduce limit word)
  | front, [] => D.refl _
  | front, letter :: rest => by
      let reduced := reduce limit rest
      have first : D.rel (front ++ letter :: rest) (front ++ letter :: reduced) := by
        simpa only [reduced, List.append_assoc, List.cons_append, List.nil_append] using
          rules.reduce_sound (front ++ [letter]) rest
      by_cases bound : reduced.count letter < limit letter
      · simpa only [reduce, reduced, if_pos bound] using first
      · have maximum : reduced.count letter ≤ limit letter := by
          rw [show reduced = reduce limit rest by rfl, count_reduce]
          exact Nat.min_le_right _ _
        have count : reduced.count letter = limit letter := by omega
        have reducedShape : reduce limit (letter :: rest) = reduced := by
          simp only [reduce, ← show reduced = reduce limit rest by rfl, if_neg bound]
        rw [reducedShape]
        exact D.trans first (rules.delete_excess front letter reduced count)
termination_by _ word => word.length

theorem normal_sound (rules : Rules D limit) (word : List Nat) :
    D.rel word (normal limit word) := by
  have reduced := rules.reduce_sound [] word
  have sorted := rules.permute (normal_perm limit word).symm [] []
  simp only [List.nil_append, List.append_nil] at reduced sorted
  exact D.trans reduced sorted

/-- Every branch reaches the same sorted capped list; this is unrestricted. -/
theorem rel_of_counts (rules : Rules D limit) (left right : List Nat)
    (counts : ∀ letter, min (left.count letter) (limit letter) = min (right.count letter) (limit letter)) :
    D.rel left right := by
  have equal := normal_eq_of_counts limit limit left right counts
  exact D.trans (rules.normal_sound left) (D.trans (D.rel_of_eq equal) (D.symm (rules.normal_sound right)))

end Rules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CappedList

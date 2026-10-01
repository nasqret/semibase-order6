import SemigroupBasis.CoRoots.Order6SporadicSection18CrossingMerge

/-! Finite support growth for the unrestricted C7 canonical-form construction.
The alphabet and number of blocks are arbitrary parameters, not fixed bounds. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def normalizeBlock (alphabet block : List Nat) : List Nat :=
  alphabet.filter (fun x => decide (x ∈ block))

def joinBlock (alphabet left right : List Nat) : List Nat :=
  alphabet.filter (fun x => decide (x ∈ left) || decide (x ∈ right))

def GoodBlock (alphabet block : List Nat) : Prop :=
  block ≠ [] ∧ normalizeBlock alphabet block = block

theorem normalizeBlock_mem (alphabet block : List Nat) (x : Nat) :
    x ∈ normalizeBlock alphabet block ↔ x ∈ alphabet ∧ x ∈ block := by
  simp [normalizeBlock]

theorem normalize_filter (alphabet : List Nat) (predicate : Nat → Bool) :
    normalizeBlock alphabet (alphabet.filter predicate) = alphabet.filter predicate := by
  apply List.filter_congr
  intro x member
  cases value : predicate x <;> simp [List.mem_filter, member, value]

theorem joinBlock_mem (alphabet left right : List Nat) (x : Nat) :
    x ∈ joinBlock alphabet left right ↔ x ∈ alphabet ∧ (x ∈ left ∨ x ∈ right) := by
  simp [joinBlock]

theorem GoodBlock.bounded {alphabet block : List Nat} (good : GoodBlock alphabet block)
    (x : Nat) (member : x ∈ block) : x ∈ alphabet := by
  have normalized : x ∈ normalizeBlock alphabet block := by
    rw [good.2]
    exact member
  exact ((normalizeBlock_mem alphabet block x).mp normalized).1

theorem GoodBlock.length_le {alphabet block : List Nat} (good : GoodBlock alphabet block) :
    block.length ≤ alphabet.length := by
  calc
    block.length = (normalizeBlock alphabet block).length := congrArg List.length good.2.symm
    _ ≤ alphabet.length := List.length_filter_le _ _

theorem joinBlock_good (alphabet left right : List Nat)
    (leftGood : GoodBlock alphabet left) (rightGood : GoodBlock alphabet right) :
    GoodBlock alphabet (joinBlock alphabet left right) := by
  have witness : ∃ x, x ∈ left := by
    cases left with
    | nil => exact False.elim (leftGood.1 rfl)
    | cons x xs => exact ⟨x, by simp⟩
  obtain ⟨x, member⟩ := witness
  have memberJoin : x ∈ joinBlock alphabet left right :=
    (joinBlock_mem alphabet left right x).mpr ⟨leftGood.bounded x member, Or.inl member⟩
  refine ⟨?_, normalize_filter alphabet _⟩
  intro empty
  rw [empty] at memberJoin
  exact List.not_mem_nil memberJoin

theorem joinBlock_content (alphabet left right : List Nat)
    (leftGood : GoodBlock alphabet left) (rightGood : GoodBlock alphabet right) (x : Nat) :
    x ∈ left ++ right ↔ x ∈ joinBlock alphabet left right := by
  rw [List.mem_append, joinBlock_mem]
  constructor
  · intro member
    refine ⟨?_, member⟩
    rcases member with leftMember | rightMember
    · exact leftGood.bounded x leftMember
    · exact rightGood.bounded x rightMember
  · exact And.right

private theorem filter_pair_bound (alphabet : List Nat) (p q : Nat → Bool) :
    (alphabet.filter p).length + (alphabet.filter q).length ≤
        (alphabet.filter (fun x => p x || q x)).length + (alphabet.filter (fun x => p x || q x)).length ∧
    ((alphabet.filter p).length + (alphabet.filter q).length =
        (alphabet.filter (fun x => p x || q x)).length + (alphabet.filter (fun x => p x || q x)).length →
      alphabet.filter p = alphabet.filter q) := by
  induction alphabet with
  | nil => simp
  | cons x xs ih =>
      have bound := ih.1
      cases hp : p x <;> cases hq : q x
      · simpa [List.filter_cons, hp, hq] using ih
      · constructor
        · simp [List.filter_cons, hp, hq] <;> omega
        · intro equal
          simp [List.filter_cons, hp, hq] at equal
          omega
      · constructor
        · simp [List.filter_cons, hp, hq] <;> omega
        · intro equal
          simp [List.filter_cons, hp, hq] at equal
          omega
      · constructor
        · simp [List.filter_cons, hp, hq] <;> omega
        · intro equal
          have tailCounts : (xs.filter p).length + (xs.filter q).length =
              (xs.filter (fun z => p z || q z)).length + (xs.filter (fun z => p z || q z)).length := by
            simp [List.filter_cons, hp, hq] at equal
            omega
          have tailEqual := ih.2 tailCounts
          simpa [List.filter_cons, hp, hq] using congrArg (List.cons x) tailEqual

theorem joinBlock_growth (alphabet left right : List Nat)
    (leftGood : GoodBlock alphabet left) (rightGood : GoodBlock alphabet right) (different : left ≠ right) :
    left.length + right.length <
      (joinBlock alphabet left right).length + (joinBlock alphabet left right).length := by
  have facts := filter_pair_bound alphabet (fun x => decide (x ∈ left)) (fun x => decide (x ∈ right))
  change (normalizeBlock alphabet left).length + (normalizeBlock alphabet right).length ≤
      (joinBlock alphabet left right).length + (joinBlock alphabet left right).length ∧
    ((normalizeBlock alphabet left).length + (normalizeBlock alphabet right).length =
      (joinBlock alphabet left right).length + (joinBlock alphabet left right).length →
      normalizeBlock alphabet left = normalizeBlock alphabet right) at facts
  rw [leftGood.2, rightGood.2] at facts
  have bound := facts.1
  have unequal : left.length + right.length ≠
      (joinBlock alphabet left right).length + (joinBlock alphabet left right).length :=
    fun equal => different (facts.2 equal)
  omega

structure Slot where
  gap : List Nat
  block : List Nat
  deriving DecidableEq

def render : List Slot → List Nat
  | [] => []
  | slot :: rest => slot.gap ++ squareList slot.block ++ render rest

def score : List Slot → Nat
  | [] => 0
  | slot :: rest => slot.block.length + score rest

def Valid (alphabet : List Nat) (chain : List Slot) : Prop :=
  ∀ slot ∈ chain, GoodBlock alphabet slot.block

theorem render_append (before after : List Slot) : render (before ++ after) = render before ++ render after := by
  induction before with
  | nil => rfl
  | cons slot rest ih => simp only [List.cons_append, render, ih, List.append_assoc]

theorem score_append (before after : List Slot) : score (before ++ after) = score before + score after := by
  induction before with
  | nil => exact (Nat.zero_add (score after)).symm
  | cons slot rest ih => simp only [List.cons_append, score, ih, Nat.add_assoc]

theorem valid_cons_iff (alphabet : List Nat) (slot : Slot) (rest : List Slot) :
    Valid alphabet (slot :: rest) ↔ GoodBlock alphabet slot.block ∧ Valid alphabet rest := by
  constructor
  · intro valid
    exact ⟨valid slot (by simp), fun s member => valid s (List.mem_cons_of_mem slot member)⟩
  · rintro ⟨head, tail⟩ s member
    rcases List.mem_cons.mp member with equal | member
    · subst s
      exact head
    · exact tail s member

theorem valid_append_iff (alphabet : List Nat) (left right : List Slot) :
    Valid alphabet (left ++ right) ↔ Valid alphabet left ∧ Valid alphabet right := by
  constructor
  · intro valid
    exact ⟨fun s member => valid s (List.mem_append.mpr (Or.inl member)),
      fun s member => valid s (List.mem_append.mpr (Or.inr member))⟩
  · rintro ⟨leftValid, rightValid⟩ s member
    rcases List.mem_append.mp member with member | member
    · exact leftValid s member
    · exact rightValid s member

theorem score_bound (alphabet : List Nat) (chain : List Slot) :
    Valid alphabet chain → score chain ≤ chain.length * alphabet.length := by
  induction chain with
  | nil => intro _; simp [score]
  | cons slot rest ih =>
      intro valid
      have parts := (valid_cons_iff alphabet slot rest).mp valid
      have headBound := parts.1.length_le
      have tailBound := ih parts.2
      simp [score, Nat.add_mul] <;> omega

/-- A maximum is obtained from a bound proved for the entire reachable set,
not from a supplied normalizer or an enumerated collection of test words. -/
theorem bounded_maximum (property : Nat → Prop) (inhabited : ∃ n, property n) :
    ∀ bound, (∀ n, property n → n ≤ bound) →
      ∃ n, property n ∧ ∀ m, property m → m ≤ n := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro bounded
      obtain ⟨n, member⟩ := inhabited
      refine ⟨n, member, ?_⟩
      intro m memberM
      have lower := bounded m memberM
      omega
  | succ bound ih =>
      intro bounded
      by_cases top : property (bound + 1)
      · exact ⟨bound + 1, top, bounded⟩
      · apply ih
        intro n member
        have upper := bounded n member
        have different : n ≠ bound + 1 := by
          intro equal
          exact top (equal ▸ member)
        omega

theorem append_derivations {a b c d : List Nat} (first : ListDerives a b) (second : ListDerives c d) :
    ListDerives (a ++ c) (b ++ d) := (first.append c).trans (second.prepend b)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.normalize_filter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.joinBlock_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.joinBlock_content
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.joinBlock_growth
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.score_bound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.bounded_maximum

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

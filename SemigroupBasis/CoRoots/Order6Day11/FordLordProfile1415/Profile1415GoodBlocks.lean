import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415Factors

/-! Good words have no simple letter hidden inside a connected component. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.GoodWords

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

/-- Every simple letter is an exact separator with disjoint side supports. -/
def Good (letters : List Nat) : Prop :=
  ∀ marker, letters.count marker = 1 →
    ∃ before after, UniqueSeparatorFourExactCut letters before marker after

/-- There are no simple supported letters. -/
def Repeated (letters : List Nat) : Prop :=
  ∀ letter, letter ∈ letters → 2 ≤ letters.count letter

theorem good_nil : Good [] := by
  intro marker simple
  simp only [List.count_nil] at simple
  omega

theorem good_singleton (letter : Nat) : Good [letter] := by
  intro marker simple
  have member : marker ∈ [letter] := List.count_pos_iff.mp (by omega)
  have equal : marker = letter := by simpa only [List.mem_singleton] using member
  subst marker
  refine ⟨[], [], rfl, ?_, ?_⟩
  · simp
  · intro selected member
    simp at member

theorem good_of_repeated {letters : List Nat} (repeated : Repeated letters) :
    Good letters := by
  intro marker simple
  have member : marker ∈ letters := List.count_pos_iff.mp (by omega)
  have atLeastTwo := repeated marker member
  omega

theorem good_append {left right : List Nat}
    (leftGood : Good left) (rightGood : Good right)
    (disjoint : UniqueSeparatorFourSupportsDisjoint left right) :
    Good (left ++ right) := by
  intro marker simple
  have counts : left.count marker + right.count marker = 1 := by
    simpa only [List.count_append] using simple
  by_cases leftSimple : left.count marker = 1
  · obtain ⟨before, after, shape, _, sideDisjoint⟩ := leftGood marker leftSimple
    refine ⟨before, after ++ right, ?_, simple, ?_⟩
    · simp only [shape, List.append_assoc, List.cons_append]
    · intro selected inBefore inAfter
      rcases List.mem_append.mp inAfter with inOldAfter | inRight
      · exact sideDisjoint selected inBefore inOldAfter
      · apply disjoint selected ?_ inRight
        rw [shape]
        exact List.mem_append.mpr (Or.inl inBefore)
  · have rightSimple : right.count marker = 1 := by omega
    obtain ⟨before, after, shape, _, sideDisjoint⟩ := rightGood marker rightSimple
    refine ⟨left ++ before, after, ?_, simple, ?_⟩
    · simp only [shape, List.append_assoc]
    · intro selected inBefore inAfter
      rcases List.mem_append.mp inBefore with inLeft | inOldBefore
      · apply disjoint selected inLeft
        rw [shape]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem marker inAfter))
      · exact sideDisjoint selected inOldBefore inAfter

/-- Support preservation is obtained from the checked separator model. -/
theorem support_of_listDerives {left right : List Nat}
    (derivation : ListDerives basis left right) :
    ∀ letter, letter ∈ left ↔ letter ∈ right := by
  cases derivation with
  | empty => exact fun _ => Iff.rfl
  | words derived =>
      exact CoRoots.S5_441Invariant.sameSupport_of_s4_69_equalEval _ _
        (derived.sound separatorModels)

theorem repeated_sandwich_target (anchor : Nat) (middle : List Nat) :
    Repeated ([anchor, anchor] ++ middle ++ middle ++ middle) := by
  intro selected member
  by_cases equal : selected = anchor
  · subst selected
    simp only [List.count_append, List.count_cons_self, List.count_nil]
    omega
  · have inMiddle : selected ∈ middle := by
      simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, equal, false_or, or_self] using member
    have positive : 0 < middle.count selected := List.count_pos_iff.mpr inMiddle
    have absent : ([anchor, anchor] : List Nat).count selected = 0 := by
      simp [Ne.symm equal]
    simp only [List.count_append, absent]
    omega

/-- The sole new collapse uses the literal B32 sandwich identity. -/
theorem collapse_closed (anchor : Nat) (middle : List Nat) :
    ∃ target, ListDerives basis (anchor :: middle ++ [anchor]) target ∧
      Repeated target := by
  cases middle with
  | nil =>
      refine ⟨[anchor, anchor], ListDerives.refl _, ?_⟩
      simpa only [List.append_nil] using repeated_sandwich_target anchor []
  | cons head tail =>
      refine ⟨[anchor, anchor] ++ (head :: tail) ++ (head :: tail) ++
        (head :: tail), ?_, repeated_sandwich_target anchor (head :: tail)⟩
      have edge := rawLaw03 (Word.singleton anchor) (Word.mk head tail)
      have listEdge := ListDerives.ofWord edge
      simpa [Word.singleton, Word.append, Word.toList, List.append_assoc] using listEdge

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.GoodWords

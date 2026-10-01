import SemigroupBasis.CoRoots.Order6SporadicSection17C10Canonical
import SemigroupBasis.CoRoots.Order6SporadicSection17C10OrderDetectors

/-! Read the simple subword from the C10/D1 probes. The suffix-content relation
orders any two distinct simple letters, while duplicate-free list rigidity
turns that relation into literal equality of the simple subsequences. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics
open SemigroupBasis

def afterFirst (separator : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = separator then xs else afterFirst separator xs

theorem afterFirst_append (separator : Nat) (before after : List Nat) (absent : separator ∉ before) :
    afterFirst separator (before ++ after) = afterFirst separator after := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
      have noHead : x ≠ separator := fun same => absent (by simp [same])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      simpa [afterFirst,noHead] using ih noTail

theorem afterFirst_absent (separator : Nat) (letters : List Nat) (absent : separator ∉ letters) :
    afterFirst separator letters = [] := by
  simpa [afterFirst] using afterFirst_append separator letters [] absent

theorem afterFirst_split (separator : Nat) (before after : List Nat) (absent : separator ∉ before) :
    afterFirst separator (before ++ separator :: after) = after := by
  rw [afterFirst_append separator before _ absent]
  simp [afterFirst]

theorem afterFirst_mem (separator : Nat) (letters : List Nat) (x : Nat)
    (member : x ∈ afterFirst separator letters) : x ∈ letters := by
  induction letters with
  | nil => simp [afterFirst] at member
  | cons h t ih =>
      by_cases same : h = separator
      · exact List.mem_cons_of_mem h (by simpa [afterFirst,same] using member)
      · exact List.mem_cons_of_mem h (ih (by simpa [afterFirst,same] using member))

theorem split_countOne (separator : Nat) (letters : List Nat) (one : letters.count separator = 1) :
    ∃ before after, letters = before ++ separator :: after ∧ separator ∉ before ∧ separator ∉ after := by
  have member : separator ∈ letters := List.count_pos_iff.mp (by rw [one]; decide)
  obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp member
  have total : before.count separator + (after.count separator + 1) = 1 := by
    simpa [shape,List.count_append,List.count_cons_self] using one
  exact ⟨before,after,shape,List.count_eq_zero.mp (by omega),List.count_eq_zero.mp (by omega)⟩

theorem SameEval.afterFirst {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (separator : Nat) (one : left.count separator = 1) :
    ∀ x, x ∈ afterFirst separator left ↔ x ∈ afterFirst separator right := by
  obtain ⟨leftBefore,leftAfter,leftShape,leftBeforeAbsent,leftAfterAbsent⟩ := split_countOne separator left one
  obtain ⟨rightBefore,rightAfter,rightShape,rightBeforeAbsent,rightAfterAbsent⟩ :=
    split_countOne separator right ((same.countOne separator).mp one)
  have splitSame : SameEval which (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter) := by
    simpa [leftShape,rightShape] using same
  rw [leftShape,rightShape,afterFirst_split separator leftBefore leftAfter leftBeforeAbsent,
    afterFirst_split separator rightBefore rightAfter rightBeforeAbsent]
  exact sameEval_afterMem which separator leftBefore leftAfter rightBefore rightAfter splitSame
    leftBeforeAbsent leftAfterAbsent rightBeforeAbsent rightAfterAbsent

theorem afterFirst_filter (simple : Nat → Bool) (separator : Nat) (letters : List Nat)
    (kept : simple separator = true) :
    afterFirst separator (letters.filter simple) = (afterFirst separator letters).filter simple := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      by_cases same : x = separator
      · subst x
        simp [afterFirst,List.filter,kept]
      · cases flag : simple x <;> simp [afterFirst,List.filter,same,flag,ih]

theorem nodup_eq_of_afterFirst (left right : List Nat) (leftGood : left.Nodup) (rightGood : right.Nodup)
    (content : ∀ x, x ∈ left ↔ x ∈ right)
    (ordered : ∀ separator marker, marker ∈ afterFirst separator left ↔ marker ∈ afterFirst separator right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons y ys =>
          have impossible : y ∈ ([] : List Nat) := (content y).mpr (by simp)
          simp at impossible
  | cons x xs ih =>
      cases right with
      | nil =>
          have impossible : x ∈ ([] : List Nat) := (content x).mp (by simp)
          simp at impossible
      | cons y ys =>
          have leftTail := List.nodup_cons.mp leftGood
          have rightTail := List.nodup_cons.mp rightGood
          have heads : x = y := by
            by_cases equal : x = y
            · exact equal
            · have yInLeft : y ∈ x :: xs := (content y).mpr (by simp)
              have yInXs : y ∈ xs := by simpa [Ne.symm equal] using yInLeft
              have yAfterLeft : y ∈ afterFirst x (x :: xs) := by simpa [afterFirst] using yInXs
              have yAfterRight := (ordered x y).mp yAfterLeft
              have yAfterTail : y ∈ afterFirst x ys := by simpa [afterFirst,Ne.symm equal] using yAfterRight
              exact False.elim (rightTail.1 (afterFirst_mem x ys y yAfterTail))
          subst y
          have tailContent : ∀ a, a ∈ xs ↔ a ∈ ys := by
            intro a
            by_cases equal : a = x
            · subst a
              simp [leftTail.1,rightTail.1]
            · simpa [equal] using content a
          have tailOrdered : ∀ separator marker,
              marker ∈ afterFirst separator xs ↔ marker ∈ afterFirst separator ys := by
            intro separator marker
            by_cases equal : separator = x
            · subst separator
              rw [afterFirst_absent x xs leftTail.1,afterFirst_absent x ys rightTail.1]
            · simpa [afterFirst,Ne.symm equal] using ordered separator marker
          exact congrArg (List.cons x) (ih ys leftTail.2 rightTail.2 tailContent tailOrdered)

theorem SameEval.simpleSubsequence {which : Bool} {left right : List Nat} (same : SameEval which left right) :
    left.filter (simpleMask left) = right.filter (simpleMask right) := by
  have masks : simpleMask right = simpleMask left := by
    funext x
    simp [simpleMask,same.countOne x]
  rw [masks]
  apply nodup_eq_of_afterFirst
  · exact simpleSubsequence_nodup left
  · rw [← masks]
    exact simpleSubsequence_nodup right
  · intro x
    simp only [List.mem_filter]
    exact and_congr (same.mem x) (Iff.refl _)
  · intro separator marker
    cases kept : simpleMask left separator with
    | false =>
        have leftAbsent : separator ∉ left.filter (simpleMask left) := by
          intro member
          have flag := (List.mem_filter.mp member).2
          simp [kept] at flag
        have rightAbsent : separator ∉ right.filter (simpleMask left) := by
          intro member
          have flag := (List.mem_filter.mp member).2
          simp [kept] at flag
        rw [afterFirst_absent separator _ leftAbsent,afterFirst_absent separator _ rightAbsent]
    | true =>
        have countOne : left.count separator = 1 := by simpa [simpleMask] using kept
        rw [afterFirst_filter _ _ _ kept,afterFirst_filter _ _ _ kept]
        simp only [List.mem_filter]
        exact and_congr (same.afterFirst separator countOne marker) (Iff.refl _)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.SameEval.afterFirst
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.nodup_eq_of_afterFirst
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.SameEval.simpleSubsequence

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics

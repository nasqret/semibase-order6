import SemigroupBasis.CoRoots.Order6Day15.B16.B16GapObservation
import SemigroupBasis.CoRoots.Order6Day15.B16.B16ObservationOne

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open Literal

theorem optional_support {xs ys : List Nat} (h : SameOptionalKey xs ys) :
    ∀ a, a ∈ xs ↔ a ∈ ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact fun _ => Iff.rfl
      | cons b bs => exact False.elim h
  | cons a as =>
      cases ys with
      | nil => exact False.elim h
      | cons b bs => exact h.1

theorem optional_empty {xs ys : List Nat} (h : SameOptionalKey xs ys) :
    xs = [] ↔ ys = [] := by
  constructor
  · intro eq
    subst xs
    cases ys with
    | nil => rfl
    | cons b bs => exact False.elim h
  · intro eq
    subst ys
    cases xs with
    | nil => rfl
    | cons a as => exact False.elim h

theorem optional_pins {xs ys : List Nat} (h : SameOptionalKey xs ys) :
    ∀ a, GapPin a xs [] ↔ GapPin a ys [] := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact fun _ => Iff.rfl
      | cons b bs => exact False.elim h
  | cons a as =>
      cases ys with
      | nil => exact False.elim h
      | cons b bs =>
          intro z
          have keys := h.2 z
          simpa only [GapPin, List.append_nil] using keys

theorem pin_after_gap_iff_empty (g post : List Nat) (s : Nat) (absent : s ∉ post) :
    GapPin s (g ++ s :: post) [] ↔ g = [] := by
  cases g with
  | nil =>
      constructor
      · intro _; rfl
      · intro _
        change s = s ∧ s ∉ post ++ []
        rw [List.append_nil]
        exact ⟨rfl,absent⟩
  | cons a as =>
      constructor
      · intro pin
        have bad : s ∉ (as ++ s :: post) ++ [] := pin.2
        apply False.elim
        apply bad
        rw [List.append_nil]
        exact List.mem_append.mpr (Or.inr (List.Mem.head _))
      · intro eq; cases eq

theorem gap_pin_whole (g post : List Nat) (nonempty : g ≠ []) (a : Nat) :
    GapPin a g post ↔ GapPin a (g ++ post) [] := by
  cases g with
  | nil => exact False.elim (nonempty rfl)
  | cons b bs =>
      change (b = a ∧ a ∉ bs ++ post) ↔ (b = a ∧ a ∉ (bs ++ post) ++ [])
      rw [List.append_nil]

theorem sameGap_of_optional {xs post ys post' : List Nat}
    (key : SameOptionalKey (xs ++ post) (ys ++ post'))
    (empty : xs = [] ↔ ys = []) (future : ∀ a, a ∈ post ↔ a ∈ post') :
    SameGapObservation xs post ys post' := by
  refine ⟨empty,optional_support key,future,?_⟩
  intro a
  by_cases ex : xs = []
  · have ey := empty.mp ex
    rw [ex,ey]
    exact Iff.rfl
  · have ey : ys ≠ [] := fun h => ex (empty.mpr h)
    exact (gap_pin_whole xs post ex a).trans
      ((optional_pins key a).trans (gap_pin_whole ys post' ey a).symm)

theorem sameGap_final {xs ys : List Nat} (key : SameOptionalKey xs ys) :
    SameGapObservation xs [] ys [] := by
  apply sameGap_of_optional
  · simpa only [List.append_nil] using key
  · exact optional_empty key
  · exact fun _ => Iff.rfl

theorem sameGap_before_separator (s : Nat) (xs post ys post' : List Nat)
    (leftAbsent : s ∉ post) (rightAbsent : s ∉ post')
    (key : SameOptionalKey (xs ++ s :: post) (ys ++ s :: post'))
    (future : ∀ a, a ∈ post ↔ a ∈ post') :
    SameGapObservation xs (s :: post) ys (s :: post') := by
  apply sameGap_of_optional key
  · exact (pin_after_gap_iff_empty xs post s leftAbsent).symm.trans
      ((optional_pins key s).trans (pin_after_gap_iff_empty ys post' s rightAbsent))
  · intro a
    simp only [List.mem_cons, future a]

theorem afterLetter_append_absent (a : Nat) (pre post : List Nat) (absent : a ∉ pre) :
    afterLetter a (pre ++ post) = afterLetter a post := by
  induction pre with
  | nil => rfl
  | cons b bs ih =>
      have head : b ≠ a := fun eq => absent (List.mem_cons.mpr (Or.inl eq.symm))
      have tail : a ∉ bs := fun h => absent (List.Mem.tail _ h)
      change (if b = a then bs ++ post else afterLetter a (bs ++ post)) = afterLetter a post
      rw [if_neg head]
      exact ih tail

theorem afterLetter_subset (a : Nat) (xs : List Nat) : ∀ b ∈ afterLetter a xs, b ∈ xs := by
  induction xs with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons c cs ih =>
      by_cases eq : c = a
      · rw [afterLetter, if_pos eq]
        exact fun b hb => List.Mem.tail _ hb
      · rw [afterLetter, if_neg eq]
        exact fun b hb => List.Mem.tail _ (ih b hb)

theorem sameObservation_nonsimple {u v : Word Nat} (obs : SameObservation u v) :
    nonsimpleSupport u.toList = nonsimpleSupport v.toList := by
  apply strictly_sorted_eq_of_support _ _ (nonsimpleSupport_sorted _) (nonsimpleSupport_sorted _)
  intro a
  rw [mem_nonsimpleSupport,mem_nonsimpleSupport]
  have one : u.toList.count a = 1 ↔ v.toList.count a = 1 := obs.2.1 a
  constructor
  · intro h
    have mem := (obs.1.1 a).mp h.1
    have positive : 0 < v.toList.count a := Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) mem)
    have notOne : v.toList.count a ≠ 1 := by
      intro eq
      have old := one.mpr eq
      have many := h.2
      omega
    exact ⟨mem,by omega⟩
  · intro h
    have mem := (obs.1.1 a).mpr h.1
    have positive : 0 < u.toList.count a := Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) mem)
    have notOne : u.toList.count a ≠ 1 := by
      intro eq
      have old := one.mp eq
      have many := h.2
      omega
    exact ⟨mem,by omega⟩

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468RecursiveSwaps

/-! Unbounded separating evaluations. Only three explicitly finite table
controls remain inputs; their exact signatures were sent to the finite owner
S3. The arbitrary-list inductions and signature separation are proved here. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

open SemigroupBasis Order6Sunday

structure ObservationControls : Prop where
  zeroLeft : ∀ value : Fin 6, RecursivePublishedFinite.S6_9726.mul 0 value = 0
  nilStep : ∀ n : Fin 4,
    RecursivePublishedFinite.S6_9726.mul
      (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 2 else if n.val = 2 then 1 else 0) 2 =
      (if n.val = 0 then (2 : Fin 6) else if n.val = 1 then 1 else 0)
  markerStep : ∀ n : Fin 4,
    RecursivePublishedFinite.S6_9726.mul
      (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 2 else if n.val = 2 then 1 else 0) 4 =
      (if n.val = 0 then (4 : Fin 6) else if n.val = 1 then 3 else 0)

def nilValue (count : Nat) : Fin 6 :=
  if count = 0 then 5 else if count = 1 then 2 else if count = 2 then 1 else 0

def markerValue (count : Nat) : Fin 6 :=
  if count = 0 then 4 else if count = 1 then 3 else 0

theorem nilValue_separates {left right : Nat} (same : nilValue left = nilValue right) :
    min 3 left = min 3 right := by
  have finite : ∀ l r : Fin 6, nilValue l.val = nilValue r.val → min 3 l.val = min 3 r.val := by
    decide
  have capped (count : Nat) : nilValue (min 3 count) = nilValue count := by
    by_cases small : count ≤ 3
    · rw [Nat.min_eq_right small]
    · have bound : 3 ≤ count := by omega
      have zero : count ≠ 0 := by omega
      have one : count ≠ 1 := by omega
      have two : count ≠ 2 := by omega
      simp [Nat.min_eq_left bound, nilValue, zero, one, two]
  let l : Fin 6 := ⟨min 3 left, by omega⟩
  let r : Fin 6 := ⟨min 3 right, by omega⟩
  have equal : nilValue l.val = nilValue r.val := (capped left).trans (same.trans (capped right).symm)
  have values := finite l r equal
  change min 3 (min 3 left) = min 3 (min 3 right) at values
  omega

theorem markerValue_separates {left right : Nat} (same : markerValue left = markerValue right) :
    min 2 left = min 2 right := by
  have finite : ∀ l r : Fin 6, markerValue l.val = markerValue r.val → min 2 l.val = min 2 r.val := by
    decide
  have capped (count : Nat) : markerValue (min 2 count) = markerValue count := by
    by_cases small : count ≤ 2
    · rw [Nat.min_eq_right small]
    · have bound : 2 ≤ count := by omega
      have zero : count ≠ 0 := by omega
      have one : count ≠ 1 := by omega
      simp [Nat.min_eq_left bound, markerValue, zero, one]
  let l : Fin 6 := ⟨min 2 left, by omega⟩
  let r : Fin 6 := ⟨min 2 right, by omega⟩
  have equal : markerValue l.val = markerValue r.val := (capped left).trans (same.trans (capped right).symm)
  have values := finite l r equal
  change min 2 (min 2 left) = min 2 (min 2 right) at values
  omega

theorem nilValue_step (controls : ObservationControls) (count : Nat) :
    RecursivePublishedFinite.S6_9726.mul (nilValue count) 2 = nilValue (count + 1) := by
  by_cases zero : count = 0
  · subst count
    simpa [nilValue] using controls.nilStep 0
  by_cases one : count = 1
  · subst count
    simpa [nilValue] using controls.nilStep 1
  by_cases two : count = 2
  · subst count
    simpa [nilValue] using controls.nilStep 2
  have nextZero : count + 1 ≠ 0 := by omega
  have nextOne : count + 1 ≠ 1 := by omega
  have nextTwo : count + 1 ≠ 2 := by omega
  simpa [nilValue, zero, one, two, nextZero, nextOne, nextTwo] using controls.nilStep 3

theorem nilValue_marker (controls : ObservationControls) (count : Nat) :
    RecursivePublishedFinite.S6_9726.mul (nilValue count) 4 = markerValue count := by
  by_cases zero : count = 0
  · subst count
    simpa [nilValue, markerValue] using controls.markerStep 0
  by_cases one : count = 1
  · subst count
    simpa [nilValue, markerValue] using controls.markerStep 1
  by_cases two : count = 2
  · subst count
    simpa [nilValue, markerValue] using controls.markerStep 2
  simpa [nilValue, markerValue, zero, one, two] using controls.markerStep 3

def run (valuation : Nat → Fin 6) (letters : List Nat) (initial : Fin 6) : Fin 6 :=
  letters.foldl (fun value letter => table.mul value (valuation letter)) initial

private theorem run_cons (valuation : Nat → Fin 6) (head : Nat) (tail : List Nat) (initial : Fin 6) :
    run valuation (head :: tail) initial = run valuation tail (table.mul initial (valuation head)) := rfl

theorem run_append (valuation : Nat → Fin 6) (left right : List Nat) (initial : Fin 6) :
    run valuation (left ++ right) initial = run valuation right (run valuation left initial) := by
  simp only [run, List.foldl_append]

theorem run_congr (left right : Nat → Fin 6) (letters : List Nat) (initial : Fin 6)
    (agree : ∀ letter ∈ letters, left letter = right letter) :
    run left letters initial = run right letters initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons head tail induction =>
      simp only [run, List.foldl_cons]
      rw [agree head (by simp)]
      exact induction _ (fun letter member => agree letter (List.mem_cons_of_mem head member))

theorem run_word (valuation : Nat → Fin 6) (word : Word Nat) :
    run valuation word.toList 5 = table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [run, Word.toList, List.foldl_cons, Semigroup.eval]
      have unit := (RecursivePublishedFinite.S6_9726.identityControl (valuation head)).1
      change tail.foldl _ (RecursivePublishedFinite.S6_9726.mul 5 (valuation head)) = _
      rw [unit]
      rfl

def nilValuation (tested letter : Nat) : Fin 6 := if letter = tested then 2 else 5

theorem run_nil (controls : ObservationControls) (tested : Nat) (letters : List Nat) (initial : Nat) :
    run (nilValuation tested) letters (nilValue initial) = nilValue (initial + letters.count tested) := by
  induction letters generalizing initial with
  | nil => simp [run]
  | cons head tail induction =>
      by_cases equal : head = tested
      · subst head
        rw [run_cons, show nilValuation tested tested = 2 by simp [nilValuation]]
        change run (nilValuation tested) tail (RecursivePublishedFinite.S6_9726.mul (nilValue initial) 2) = _
        rw [nilValue_step controls, induction]
        simp only [List.count_cons_self]
        congr 1
        omega
      · change run (nilValuation tested) tail
            (RecursivePublishedFinite.S6_9726.mul (nilValue initial) (nilValuation tested head)) = _
        rw [show nilValuation tested head = 5 by simp [nilValuation, equal],
          (RecursivePublishedFinite.S6_9726.identityControl (nilValue initial)).2, induction,
          List.count_cons_of_ne equal]

theorem run_nil_zero (controls : ObservationControls) (tested : Nat) (letters : List Nat) :
    run (nilValuation tested) letters 5 = nilValue (letters.count tested) := by
  simpa only [nilValue, if_pos rfl, Nat.zero_add] using run_nil controls tested letters 0

theorem run_marker (controls : ObservationControls) (valuation : Nat → Fin 6)
    (letters : List Nat) (count : Nat) : run valuation letters (markerValue count) = markerValue count := by
  have absorbs : ∀ value : Fin 6, table.mul (markerValue count) value = markerValue count := by
    intro value
    by_cases zero : count = 0
    · simpa [markerValue, zero] using (RecursivePublishedFinite.S6_9726.structuralControl.1 value).2
    by_cases one : count = 1
    · simpa [markerValue, zero, one] using (RecursivePublishedFinite.S6_9726.structuralControl.1 value).1
    simpa [markerValue, zero, one] using controls.zeroLeft value
  induction letters with
  | nil => rfl
  | cons head tail induction =>
      change run valuation tail (table.mul (markerValue count) (valuation head)) = _
      rw [absorbs, induction]

def markerValuation (tested separator letter : Nat) : Fin 6 :=
  if letter = separator then 4 else if letter = tested then 2 else 5

theorem run_prefix_marker (controls : ObservationControls) (tested separator : Nat)
    (prefixWords tail : List Nat) (absent : separator ∉ prefixWords) :
    run (markerValuation tested separator) (prefixWords ++ separator :: tail) 5 =
      markerValue (prefixWords.count tested) := by
  have prefixSame : run (markerValuation tested separator) prefixWords 5 =
      run (nilValuation tested) prefixWords 5 := by
    apply run_congr
    intro letter member
    have different : letter ≠ separator := fun equal => absent (equal ▸ member)
    simp [markerValuation, nilValuation, different]
  rw [run_append, run_cons,
    show markerValuation tested separator separator = 4 by simp [markerValuation],
    prefixSame, run_nil_zero controls]
  change run (markerValuation tested separator) tail
    (RecursivePublishedFinite.S6_9726.mul (nilValue (prefixWords.count tested)) 4) = _
  rw [nilValue_marker controls]
  exact run_marker controls _ _ _

theorem sameCapsThree_of_valid (controls : ObservationControls) (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    PrefixCount.SameCapsThree identity.lhs.toList identity.rhs.toList := by
  intro tested
  have equal : run (nilValuation tested) identity.lhs.toList 5 =
      run (nilValuation tested) identity.rhs.toList 5 :=
    (run_word _ _).trans ((valid _).trans (run_word _ _).symm)
  rw [run_nil_zero controls, run_nil_zero controls] at equal
  exact nilValue_separates equal

theorem sameBeforeTwo_of_valid (controls : ObservationControls) (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    PrefixCount.SameBeforeTwo identity.lhs.toList identity.rhs.toList := by
  have counts := sameCapsThree_of_valid controls identity valid
  intro tested separator
  by_cases member : separator ∈ identity.lhs.toList
  · have otherMember : separator ∈ identity.rhs.toList := by
      apply List.count_pos_iff.mp
      have positive := List.count_pos_iff.mpr member
      have same := counts separator
      omega
    obtain ⟨leftPrefix, leftTail, leftShape, leftAbsent⟩ := PrefixCount.split_first separator member
    obtain ⟨rightPrefix, rightTail, rightShape, rightAbsent⟩ := PrefixCount.split_first separator otherMember
    have equal : run (markerValuation tested separator) identity.lhs.toList 5 =
        run (markerValuation tested separator) identity.rhs.toList 5 :=
      (run_word _ _).trans ((valid _).trans (run_word _ _).symm)
    rw [leftShape, rightShape, run_prefix_marker controls tested separator leftPrefix leftTail leftAbsent,
      run_prefix_marker controls tested separator rightPrefix rightTail rightAbsent] at equal
    rw [leftShape, rightShape, PrefixCount.before_append_of_not_mem separator leftPrefix _ leftAbsent,
      PrefixCount.before_append_of_not_mem separator rightPrefix _ rightAbsent]
    simpa only [PrefixCount.before_self, List.append_nil] using markerValue_separates equal
  · have otherAbsent : separator ∉ identity.rhs.toList := by
      apply List.not_mem_of_count_eq_zero
      have zero := List.count_eq_zero_of_not_mem member
      have same := counts separator
      omega
    rw [PrefixCount.before_eq_self_of_not_mem separator member,
      PrefixCount.before_eq_self_of_not_mem separator otherAbsent]
    have same := counts tested
    omega

/-- No unrestricted premise is left: only the one fixed derivation and
three finite table controls, all assigned to S3 by exact signatures. This
does not assert that those pending controls have been delivered. -/
theorem complete_of_fixed_interface (third : ThirdTransport) (controls : ObservationControls)
    (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature third (sameCapsThree_of_valid controls identity valid)
    (sameBeforeTwo_of_valid controls identity valid)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

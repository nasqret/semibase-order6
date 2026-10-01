import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Generated.CatalogueOrder5Part05

namespace SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics

open SemigroupBasis
open SemigroupBasis.Examples

/-- Multiplication in the opposite of the catalogue representative `S5_614`. -/
def oppositeMul (a b : Fin 5) : Fin 5 :=
  Generated.Catalogue.S5_614.mul b a

/-- Evaluation of a possibly empty list, starting at the identity element `4`. -/
def listEval (valuation : Nat → Fin 5) (xs : List Nat) : Fin 5 :=
  xs.foldl (fun current x => oppositeMul current (valuation x)) 4

private theorem oppositeMul_left_identity (a : Fin 5) :
    oppositeMul 4 a = a := by
  apply Fin.ext
  revert a
  decide

theorem eval_eq_listEval
    (valuation : Nat → Fin 5) (w : Word Nat) :
    Generated.Catalogue.S5_614.table.semigroup.opposite.eval valuation w =
      listEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => oppositeMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x => oppositeMul current (valuation x))
            (oppositeMul 4 (valuation head))
      rw [oppositeMul_left_identity]

def occurrenceState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else if n = 1 then 1 else 0

def occurrenceValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 1 else 4

private theorem occurrenceTransition (n : Nat) :
    oppositeMul (occurrenceState n) 1 = occurrenceState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [oppositeMul, occurrenceState, hn0, hn1,
        Generated.Catalogue.S5_614.mul]

private theorem occurrenceIdentity (n : Nat) :
    oppositeMul (occurrenceState n) 4 = occurrenceState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [oppositeMul, occurrenceState, hn0, hn1,
        Generated.Catalogue.S5_614.mul]

private theorem occurrenceFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            oppositeMul current (occurrenceValuation z x))
          (occurrenceState n) =
        occurrenceState (n + xs.count z)
  | [], n => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show occurrenceValuation z z = (1 : Fin 5) by
          simp [occurrenceValuation]]
        rw [occurrenceTransition, occurrenceFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show occurrenceValuation z x = (4 : Fin 5) by
          simp [occurrenceValuation, hx]]
        rw [occurrenceIdentity, occurrenceFold, List.count_cons_of_ne hx]

theorem listEval_occurrence (z : Nat) (xs : List Nat) :
    listEval (occurrenceValuation z) xs =
      occurrenceState (xs.count z) := by
  simpa [listEval, occurrenceState] using occurrenceFold z xs 0

def parityState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else if n % 2 = 0 then 2 else 3

def parityValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 3 else 4

private theorem parityTransition (n : Nat) :
    oppositeMul (parityState n) 3 = parityState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases heven : n % 2 = 0
    · have hodd : (n + 1) % 2 = 1 := by omega
      simp [oppositeMul, parityState, hn0, heven, hodd,
        Generated.Catalogue.S5_614.mul]
    · have hmod : n % 2 = 1 := by omega
      have heven' : (n + 1) % 2 = 0 := by omega
      simp [oppositeMul, parityState, hn0, hmod, heven',
        Generated.Catalogue.S5_614.mul]

private theorem parityIdentity (n : Nat) :
    oppositeMul (parityState n) 4 = parityState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases heven : n % 2 = 0
    · simp [oppositeMul, parityState, hn0, heven,
        Generated.Catalogue.S5_614.mul]
    · simp [oppositeMul, parityState, hn0, heven,
        Generated.Catalogue.S5_614.mul]

private theorem parityFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            oppositeMul current (parityValuation z x))
          (parityState n) =
        parityState (n + xs.count z)
  | [], n => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show parityValuation z z = (3 : Fin 5) by
          simp [parityValuation]]
        rw [parityTransition, parityFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show parityValuation z x = (4 : Fin 5) by
          simp [parityValuation, hx]]
        rw [parityIdentity, parityFold, List.count_cons_of_ne hx]

theorem listEval_parity (z : Nat) (xs : List Nat) :
    listEval (parityValuation z) xs =
      parityState (xs.count z) := by
  simpa [listEval, parityState] using parityFold z xs 0

theorem exponent_eq_of_state_eq
    {m n : Nat}
    (occurrence : occurrenceState m = occurrenceState n)
    (parity : parityState m = parityState n) :
    periodTwoFromTwoExponent m = periodTwoFromTwoExponent n := by
  by_cases hm0 : m = 0
  · subst m
    by_cases hn0 : n = 0
    · subst n
      rfl
    · by_cases hn1 : n = 1
      · subst n
        simp [occurrenceState] at occurrence
      · simp [occurrenceState, hn0, hn1] at occurrence
  · by_cases hm1 : m = 1
    · subst m
      by_cases hn0 : n = 0
      · subst n
        simp [occurrenceState] at occurrence
      · by_cases hn1 : n = 1
        · subst n
          rfl
        · simp [occurrenceState, hn0, hn1] at occurrence
    · have hm2 : 2 ≤ m := by omega
      have hn0 : n ≠ 0 := by
        intro h
        subst n
        simp [occurrenceState, hm0, hm1] at occurrence
      have hn1 : n ≠ 1 := by
        intro h
        subst n
        simp [occurrenceState, hm0, hm1] at occurrence
      have hn2 : 2 ≤ n := by omega
      by_cases hmEven : m % 2 = 0
      · have hnEven : n % 2 = 0 := by
          by_cases h : n % 2 = 0
          · exact h
          · simp [parityState, hm0, hn0, hmEven, h] at parity
        simp [periodTwoFromTwoExponent, show ¬m < 2 by omega,
          show ¬n < 2 by omega, hmEven, hnEven]
      · have hmOdd : m % 2 = 1 := by omega
        have hnOdd : n % 2 = 1 := by
          by_cases h : n % 2 = 0
          · simp [parityState, hm0, hn0, hmOdd, h] at parity
          · omega
        simp [periodTwoFromTwoExponent, show ¬m < 2 by omega,
          show ¬n < 2 by omega, hmOdd, hnOdd]

theorem periodTwoFromTwoExponent_eq_self_of_le_three
    {n : Nat} (bound : n ≤ 3) :
    periodTwoFromTwoExponent n = n := by
  unfold periodTwoFromTwoExponent
  split <;> omega

theorem count_eq_of_equalEval
    {left right : List Nat}
    (leftBound : ∀ z, left.count z ≤ 3)
    (rightBound : ∀ z, right.count z ≤ 3)
    (equalEval :
      ∀ valuation : Nat → Fin 5,
        listEval valuation left = listEval valuation right) :
    ∀ z, left.count z = right.count z := by
  intro z
  have occurrence := equalEval (occurrenceValuation z)
  have parity := equalEval (parityValuation z)
  rw [listEval_occurrence, listEval_occurrence] at occurrence
  rw [listEval_parity, listEval_parity] at parity
  have exponentEq :=
    exponent_eq_of_state_eq occurrence parity
  rw [periodTwoFromTwoExponent_eq_self_of_le_three (leftBound z),
    periodTwoFromTwoExponent_eq_self_of_le_three (rightBound z)] at exponentEq
  exact exponentEq

theorem valid_exponent_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        Generated.Catalogue.S5_614.table.semigroup.opposite) :
    ∀ z,
      periodTwoFromTwoExponent (e.lhs.toList.count z) =
        periodTwoFromTwoExponent (e.rhs.toList.count z) := by
  intro z
  have occurrence := valid (occurrenceValuation z)
  have parity := valid (parityValuation z)
  rw [eval_eq_listEval, eval_eq_listEval,
    listEval_occurrence, listEval_occurrence] at occurrence
  rw [eval_eq_listEval, eval_eq_listEval,
    listEval_parity, listEval_parity] at parity
  exact exponent_eq_of_state_eq occurrence parity

/-- The maximal prefix before the first occurrence of `marker`. -/
def prefixBefore (marker : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if x = marker then [] else x :: prefixBefore marker xs

theorem prefixBefore_split
    (marker : Nat) :
    ∀ (pre suffix : List Nat),
      marker ∉ pre →
      prefixBefore marker (pre ++ marker :: suffix) = pre
  | [], suffix, _ => by simp [prefixBefore]
  | x :: xs, suffix, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.cons_append, prefixBefore, hx, ↓reduceIte]
      rw [prefixBefore_split marker xs suffix
        (fun h => markerNotMem (List.Mem.tail x h))]

def markerValuation (marker selected : Nat) : Nat → Fin 5 :=
  fun x => if x = marker then 1 else if x = selected then 2 else 4

private theorem fold_values_two_four_preserves
    (marker selected : Nat) :
    ∀ (xs : List Nat) (initial : Fin 5),
      marker ∉ xs →
      (initial = 0 ∨ initial = 1 ∨ initial = 2) →
      xs.foldl
          (fun current x =>
            oppositeMul current (markerValuation marker selected x))
          initial = initial
  | [], _, _, _ => rfl
  | x :: xs, initial, markerNotMem, initialCases => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      have step :
          oppositeMul initial (markerValuation marker selected x) =
            initial := by
        rcases initialCases with rfl | rfl | rfl
        all_goals
          by_cases hsel : x = selected
          · subst x
            simp [oppositeMul, markerValuation, hx,
              Generated.Catalogue.S5_614.mul]
          · simp [oppositeMul, markerValuation, hx, hsel,
              Generated.Catalogue.S5_614.mul]
      rw [step]
      exact fold_values_two_four_preserves marker selected xs initial
        (fun h => markerNotMem (List.Mem.tail x h)) initialCases

private theorem fold_before_marker
    (marker selected : Nat) :
    ∀ xs : List Nat,
      marker ∉ xs →
      xs.foldl
          (fun current x =>
            oppositeMul current (markerValuation marker selected x))
          4 =
        (if selected ∈ xs then 2 else 4)
  | [], _ => by simp
  | x :: xs, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      by_cases hsel : x = selected
      · subst x
        have step :
            oppositeMul 4
              (markerValuation marker selected selected) = 2 := by
          simp [oppositeMul, markerValuation, hx,
            Generated.Catalogue.S5_614.mul]
        rw [step]
        rw [fold_values_two_four_preserves marker selected xs 2
          (fun h => markerNotMem (List.Mem.tail selected h))
          (Or.inr (Or.inr rfl))]
        simp
      · have step :
            oppositeMul 4 (markerValuation marker selected x) = 4 := by
          simp [oppositeMul, markerValuation, hx, hsel,
            Generated.Catalogue.S5_614.mul]
        rw [step, fold_before_marker marker selected xs
          (fun h => markerNotMem (List.Mem.tail x h))]
        simp [Ne.symm hsel]

theorem marker_not_mem_parts_of_count_one
    (marker : Nat) (pre suffix : List Nat)
    (countOne : (pre ++ marker :: suffix).count marker = 1) :
    marker ∉ pre ∧ marker ∉ suffix := by
  rw [List.count_append, List.count_cons_self] at countOne
  constructor
  · intro hmem
    have positive : 0 < pre.count marker :=
      List.count_pos_iff.mpr hmem
    omega
  · intro hmem
    have positive : 0 < suffix.count marker :=
      List.count_pos_iff.mpr hmem
    omega

theorem prefixBefore_eq_of_split_count_one
    (marker : Nat) (pre suffix : List Nat)
    (countOne : (pre ++ marker :: suffix).count marker = 1) :
    prefixBefore marker (pre ++ marker :: suffix) = pre := by
  exact prefixBefore_split marker pre suffix
    (marker_not_mem_parts_of_count_one
      marker pre suffix countOne).1

private theorem listEval_marker_split
    (marker selected : Nat) (pre suffix : List Nat)
    (markerPrefix : marker ∉ pre)
    (markerSuffix : marker ∉ suffix) :
    listEval (markerValuation marker selected)
        (pre ++ marker :: suffix) =
      if selected ∈ pre then 0 else 1 := by
  unfold listEval
  rw [List.foldl_append]
  rw [fold_before_marker marker selected pre markerPrefix]
  simp only [List.foldl_cons]
  split <;> rename_i selectedMem
  · have markerNeSelected : marker ≠ selected := by
      intro h
      subst selected
      exact markerPrefix selectedMem
    have markerValue :
        markerValuation marker selected marker = (1 : Fin 5) := by
      simp [markerValuation]
    rw [markerValue]
    have kill : oppositeMul 2 1 = (0 : Fin 5) := rfl
    rw [kill]
    exact fold_values_two_four_preserves marker selected suffix 0
      markerSuffix (Or.inl rfl)
  · have markerValue :
        markerValuation marker selected marker = (1 : Fin 5) := by
      simp [markerValuation]
    rw [markerValue]
    have start : oppositeMul 4 1 = (1 : Fin 5) := rfl
    rw [start]
    exact fold_values_two_four_preserves marker selected suffix 1
      markerSuffix (Or.inr (Or.inl rfl))

theorem listEval_marker
    (marker selected : Nat) (xs : List Nat)
    (countOne : xs.count marker = 1) :
    listEval (markerValuation marker selected) xs =
      if selected ∈ prefixBefore marker xs then 0 else 1 := by
  have markerMem : marker ∈ xs :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨pre, suffix, split⟩ := List.mem_iff_append.mp markerMem
  have splitCount :
      (pre ++ marker :: suffix).count marker = 1 := by
    rw [← split]
    exact countOne
  have notMem :=
    marker_not_mem_parts_of_count_one marker pre suffix splitCount
  rw [split, prefixBefore_split marker pre suffix notMem.1]
  exact listEval_marker_split marker selected pre suffix
    notMem.1 notMem.2

theorem valid_prefixBefore_iff
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        Generated.Catalogue.S5_614.table.semigroup.opposite)
    (marker selected : Nat)
    (lhsSingleton : e.lhs.toList.count marker = 1)
    (rhsSingleton : e.rhs.toList.count marker = 1) :
    selected ∈ prefixBefore marker e.lhs.toList ↔
      selected ∈ prefixBefore marker e.rhs.toList := by
  have evaluated := valid (markerValuation marker selected)
  rw [eval_eq_listEval, eval_eq_listEval,
    listEval_marker marker selected e.lhs.toList lhsSingleton,
    listEval_marker marker selected e.rhs.toList rhsSingleton] at evaluated
  by_cases lhsMem :
      selected ∈ prefixBefore marker e.lhs.toList <;>
    by_cases rhsMem :
      selected ∈ prefixBefore marker e.rhs.toList <;>
    simp_all

theorem prefixBefore_mem_iff_of_equalEval
    {left right : List Nat}
    (equalEval :
      ∀ valuation : Nat → Fin 5,
        listEval valuation left = listEval valuation right)
    (marker selected : Nat)
    (leftSingleton : left.count marker = 1)
    (rightSingleton : right.count marker = 1) :
    selected ∈ prefixBefore marker left ↔
      selected ∈ prefixBefore marker right := by
  have evaluated := equalEval (markerValuation marker selected)
  rw [listEval_marker marker selected left leftSingleton,
    listEval_marker marker selected right rightSingleton] at evaluated
  by_cases leftMem : selected ∈ prefixBefore marker left <;>
    by_cases rightMem : selected ∈ prefixBefore marker right <;>
    simp_all

private theorem fold_congr
    (v₁ v₂ : Nat → Fin 5) :
    ∀ (xs : List Nat) (acc : Fin 5),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x => oppositeMul current (v₁ x)) acc =
        xs.foldl
          (fun current x => oppositeMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact fold_congr v₁ v₂ xs
        (oppositeMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

theorem listEval_congr
    (v₁ v₂ : Nat → Fin 5) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    listEval v₁ xs = listEval v₂ xs :=
  fold_congr v₁ v₂ xs 4 agree

private theorem fold_all_identity :
    ∀ (xs : List Nat) (acc : Fin 5),
      xs.foldl (fun current _ => oppositeMul current 4) acc = acc
  | [], _ => rfl
  | _ :: xs, acc => by
      simp only [List.foldl_cons]
      have identity : oppositeMul acc 4 = acc := by
        apply Fin.ext
        revert acc
        decide
      rw [identity]
      exact fold_all_identity xs acc

def maskValuation
    (labels : List Nat) (valuation : Nat → Fin 5) :
    Nat → Fin 5 :=
  fun z => if z ∈ labels then 4 else valuation z

theorem listEval_mask_prefix
    (labels prefixList suffix : List Nat)
    (valuation : Nat → Fin 5)
    (prefixCovered : ∀ z, z ∈ prefixList → z ∈ labels)
    (suffixDisjoint : ∀ z, z ∈ suffix → z ∉ labels) :
    listEval (maskValuation labels valuation) (prefixList ++ suffix) =
      listEval valuation suffix := by
  unfold listEval
  rw [List.foldl_append]
  have prefixIdentity :
      prefixList.foldl
          (fun current z =>
            oppositeMul current (maskValuation labels valuation z))
          4 = 4 := by
    have congruent :=
      fold_congr
        (maskValuation labels valuation)
        (fun _ => (4 : Fin 5)) prefixList 4
        (fun z hz => by
          simp [maskValuation, prefixCovered z hz])
    rw [congruent]
    exact fold_all_identity prefixList 4
  rw [prefixIdentity]
  exact fold_congr
    (maskValuation labels valuation) valuation suffix 4
    (fun z hz => by
      simp [maskValuation, suffixDisjoint z hz])

end SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics

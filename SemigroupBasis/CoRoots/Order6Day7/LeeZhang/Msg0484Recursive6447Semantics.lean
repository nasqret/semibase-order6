import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484Recursive6447Observations

/-! Unrestricted semantic necessity of the exact capped simple-suffix key.
The prefix before a unique nilpotent probe acts neutrally; the suffix reads
its capped count. The final completeness theorem has only FOUR fixed finite
inputs, not an arbitrary-word separation or reachability hypothesis. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis Order6Sunday

theorem run_left_neutral (valuation : Nat → Fin 6) (letters : List Nat) (initial terminal : Fin 6)
    (neutral : ∀ letter ∈ letters, table.mul (valuation letter) terminal = terminal) :
    table.mul (run valuation letters initial) terminal = table.mul initial terminal := by
  induction letters generalizing initial with
  | nil => rfl
  | cons head tail induction =>
      rw [run_cons]
      have restNeutral : ∀ letter ∈ tail, table.mul (valuation letter) terminal = terminal :=
        fun letter member => neutral letter (List.mem_cons_of_mem head member)
      rw [induction (table.mul initial (valuation head)) restNeutral,
        table.assoc, neutral head (by simp)]

def probeValuation (tested separator letter : Nat) : Fin 6 :=
  if letter = separator then 2 else if letter = tested then 4 else 5

theorem run_simple_probe (controls : ObservationControls) (tested separator : Nat)
    (prefixWords tail : List Nat) (prefixAbsent : separator ∉ prefixWords) (tailAbsent : separator ∉ tail) :
    run (probeValuation tested separator) (prefixWords ++ separator :: tail) 5 =
      lowValue (tail.count tested) := by
  have neutral : ∀ letter ∈ prefixWords,
      table.mul (probeValuation tested separator letter) (2 : Fin 6) = (2 : Fin 6) := by
    intro letter member
    have different : letter ≠ separator := fun equal => prefixAbsent (equal ▸ member)
    by_cases selected : letter = tested
    · change RecursivePublishedFinite.S6_6447.mul (probeValuation tested separator letter) 2 = 2
      rw [show probeValuation tested separator letter = 4 by
        simp only [probeValuation, if_neg different, if_pos selected]]
      exact (RecursivePublishedFinite.S6_6447.structuralControl.2.2.2 2 (by decide)).2
    · change RecursivePublishedFinite.S6_6447.mul (probeValuation tested separator letter) 2 = 2
      rw [show probeValuation tested separator letter = 5 by
        simp only [probeValuation, if_neg different, if_neg selected]]
      exact (RecursivePublishedFinite.S6_6447.identityControl 2).1
  have prefixValue : table.mul (run (probeValuation tested separator) prefixWords 5) (2 : Fin 6) = (2 : Fin 6) :=
    (run_left_neutral (probeValuation tested separator) prefixWords 5 2 neutral).trans
      (RecursivePublishedFinite.S6_6447.identityControl 2).1
  rw [run_append, run_cons,
    show probeValuation tested separator separator = 2 by simp [probeValuation], prefixValue]
  have tailSame : run (probeValuation tested separator) tail 2 = run (powerValuation tested) tail 2 := by
    apply run_congr
    intro letter member
    have different : letter ≠ separator := fun equal => tailAbsent (equal ▸ member)
    simp [probeValuation, powerValuation, different]
  rw [tailSame]
  exact run_low_zero controls tested tail

theorem sameCapsTwo_of_valid (controls : ObservationControls) (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ tested, min 2 (identity.lhs.toList.count tested) = min 2 (identity.rhs.toList.count tested) := by
  intro tested
  have equal : run (powerValuation tested) identity.lhs.toList 5 =
      run (powerValuation tested) identity.rhs.toList 5 :=
    (run_word _ _).trans ((valid _).trans (run_word _ _).symm)
  rw [run_high_zero controls, run_high_zero controls] at equal
  exact highValue_separates equal

theorem before_reverse_of_split (separator : Nat) (prefixWords tail : List Nat)
    (absent : separator ∉ tail) :
    PrefixCount.before separator (prefixWords ++ separator :: tail).reverse = tail.reverse := by
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc]
  rw [PrefixCount.before_append_of_not_mem separator tail.reverse _ (by simpa using absent)]
  simp

theorem simpleSuffixCounts_of_valid (controls : ObservationControls) (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (separator : Nat)
    (one : identity.lhs.toList.count separator = 1) (tested : Nat) :
    min 2 ((PrefixCount.before separator identity.lhs.toList.reverse).count tested) =
      min 2 ((PrefixCount.before separator identity.rhs.toList.reverse).count tested) := by
  have otherOne : identity.rhs.toList.count separator = 1 := by
    have counts := sameCapsTwo_of_valid controls identity valid separator
    omega
  have leftMember : separator ∈ identity.lhs.toList := List.count_pos_iff.mp (by omega)
  have rightMember : separator ∈ identity.rhs.toList := List.count_pos_iff.mp (by omega)
  obtain ⟨leftPrefix, leftTail, leftShape, leftAbsent⟩ := PrefixCount.split_first separator leftMember
  obtain ⟨rightPrefix, rightTail, rightShape, rightAbsent⟩ := PrefixCount.split_first separator rightMember
  have leftTailAbsent : separator ∉ leftTail := by
    apply List.not_mem_of_count_eq_zero
    have count := one
    rw [leftShape] at count
    simp only [List.count_append, List.count_cons_self] at count
    omega
  have rightTailAbsent : separator ∉ rightTail := by
    apply List.not_mem_of_count_eq_zero
    have count := otherOne
    rw [rightShape] at count
    simp only [List.count_append, List.count_cons_self] at count
    omega
  have equal : run (probeValuation tested separator) identity.lhs.toList 5 =
      run (probeValuation tested separator) identity.rhs.toList 5 :=
    (run_word _ _).trans ((valid _).trans (run_word _ _).symm)
  rw [leftShape, rightShape,
    run_simple_probe controls tested separator leftPrefix leftTail leftAbsent leftTailAbsent,
    run_simple_probe controls tested separator rightPrefix rightTail rightAbsent rightTailAbsent] at equal
  rw [leftShape, rightShape,
    before_reverse_of_split separator leftPrefix leftTail leftTailAbsent,
    before_reverse_of_split separator rightPrefix rightTail rightTailAbsent]
  simpa only [List.count_reverse] using lowValue_separates equal

theorem signature_of_valid (controls : ObservationControls) (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SimplePrefix.CappedSignature identity.lhs.toList.reverse identity.rhs.toList.reverse := by
  refine ⟨?_, ?_⟩
  · intro tested
    simpa using sameCapsTwo_of_valid controls identity valid tested
  · intro separator one tested
    have originalOne : identity.lhs.toList.count separator = 1 := by simpa using one
    exact simpleSuffixCounts_of_valid controls identity valid separator originalOne tested

theorem complete_of_fixed_interface (fixed : FixedSwaps) (controls : ObservationControls)
    (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature fixed (signature_of_valid controls identity valid)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

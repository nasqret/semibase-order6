import SemigroupBasis.FiniteTable
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal

/-! Basis-independent marker observations for the four distinct theories in
sib-9638. These are necessary observations, not a complete semantic key or a
reach/completeness theorem. The terminal observation uses an explicit nonempty
prefix/last-letter cut; singleton words are covered separately. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal

theorem associative : ∀ (family : Fin 4) (a b c : Fin 6),
    mul family (mul family a b) c = mul family a (mul family b c) := by
  intro family
  refine Fin.cases (by decide) (fun f1 => ?_) family
  refine Fin.cases (by decide) (fun f2 => ?_) f1
  refine Fin.cases (by decide) (fun f3 => ?_) f2
  exact Fin.cases (by decide) (fun f0 => Fin.elim0 f0) f3

def table (family : Fin 4) : FiniteTable where
  order := 6
  mul := mul family
  assoc := associative family

theorem table_eval (family : Fin 4) (valuation : α → Fin 6) (word : Word α) :
    (table family).semigroup.eval valuation word = eval family valuation word := rfl

theorem mul_four_left : ∀ (family : Fin 4), family ≠ 3 → ∀ (a b : Fin 6),
    mul family a b = 4 ↔ a = 4 ∧ Low b := by
  unfold Low
  decide

theorem mul_four_right : ∀ (a b : Fin 6),
    mul 3 a b = 4 ↔ Low a ∧ b = 4 := by
  unfold Low
  decide

theorem fold_four_left (family : Fin 4) (notRight : family ≠ 3)
    (valuation : α → Fin 6) (letters : List α) (initial : Fin 6) :
    letters.foldl (fun state a => mul family state (valuation a)) initial = 4 ↔
      initial = 4 ∧ ∀ a ∈ letters, Low (valuation a) := by
  induction letters generalizing initial with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldl_cons, ih, mul_four_left family notRight,
        List.forall_mem_cons, and_assoc]

theorem eval_four_left (family : Fin 4) (notRight : family ≠ 3)
    (valuation : α → Fin 6) (word : Word α) :
    eval family valuation word = 4 ↔
      valuation word.head = 4 ∧ ∀ a ∈ word.tail, Low (valuation a) :=
  fold_four_left family notRight valuation word.tail (valuation word.head)

theorem eval_snoc (family : Fin 4) (valuation : α → Fin 6)
    (stem : Word α) (last : α) :
    eval family valuation (stem ++ Word.singleton last) =
      mul family (eval family valuation stem) (valuation last) := by
  simp only [eval, Word.append_head, Word.append_tail, Word.singleton_head,
    Word.singleton_tail, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem eval_four_right_cut (valuation : α → Fin 6) (stem : Word α) (last : α) :
    eval 3 valuation (stem ++ Word.singleton last) = 4 ↔
      (∀ a ∈ stem.toList, Low (valuation a)) ∧ valuation last = 4 := by
  rw [eval_snoc, mul_four_right, eval_low_iff]

def probe [DecidableEq α] (marker a : α) : Fin 6 := if a = marker then 4 else 0

theorem probe_eq_four [DecidableEq α] (marker a : α) :
    probe marker a = 4 ↔ a = marker := by
  by_cases h : a = marker <;> simp [probe, h]

theorem probe_low [DecidableEq α] (marker a : α) :
    Low (probe marker a) ↔ a ≠ marker := by
  by_cases h : a = marker
  · rw [probe, if_pos h]
    have impossible : ¬ Low (4 : Fin 6) := by unfold Low; decide
    constructor
    · intro low
      exact False.elim (impossible low)
    · intro different
      exact False.elim (different h)
  · rw [probe, if_neg h]
    constructor
    · intro _
      exact h
    · intro _
      unfold Low
      decide

theorem all_probe_low_iff [DecidableEq α] (marker : α) (letters : List α) :
    (∀ a ∈ letters, Low (probe marker a)) ↔ marker ∉ letters := by
  simp only [probe_low]
  constructor
  · intro all present
    exact all marker present rfl
  · intro absent a present same
    subst a
    exact absent present

theorem probe_four_left [DecidableEq α] (family : Fin 4) (notRight : family ≠ 3)
    (marker : α) (word : Word α) :
    eval family (probe marker) word = 4 ↔
      word.head = marker ∧ marker ∉ word.tail := by
  rw [eval_four_left family notRight, probe_eq_four, all_probe_low_iff]

theorem probe_four_right_cut [DecidableEq α] (marker : α)
    (stem : Word α) (last : α) :
    eval 3 (probe marker) (stem ++ Word.singleton last) = 4 ↔
      marker ∉ stem.toList ∧ last = marker := by
  rw [eval_four_right_cut, all_probe_low_iff, probe_eq_four]

theorem probe_singleton [DecidableEq α] (family : Fin 4) (marker a : α) :
    eval family (probe marker) (Word.singleton a) = 4 ↔ a = marker :=
  probe_eq_four marker a

theorem head_absence_of_eval_four (family : Fin 4) (notRight : family ≠ 3)
    (valuation : α → Fin 6) (word : Word α) (four : eval family valuation word = 4) :
    word.head ∉ word.tail := by
  rcases (eval_four_left family notRight valuation word).mp four with ⟨head, low⟩
  intro present
  have bad := low word.head present
  rw [head] at bad
  have impossible : ¬ Low (4 : Fin 6) := by unfold Low; decide
  exact impossible bad

theorem first_absorbers : ∀ (state letter : Fin 6),
    state = 3 ∨ state = 5 → mul 0 state letter = state := by decide

theorem fold_first_absorber (valuation : α → Fin 6) (letters : List α)
    (initial : Fin 6) (absorbing : initial = 3 ∨ initial = 5) :
    letters.foldl (fun state a => mul 0 state (valuation a)) initial = initial := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      rw [List.foldl_cons, first_absorbers initial (valuation a) absorbing]
      exact ih

theorem initial_marker_of_valid [DecidableEq α] (family : Fin 4)
    (notRight : family ≠ 3) (identity : Identity α)
    (valid : identity.SatisfiedBy (table family).semigroup) (marker : α) :
    (identity.lhs.head = marker ∧ marker ∉ identity.lhs.tail) ↔
      (identity.rhs.head = marker ∧ marker ∉ identity.rhs.tail) := by
  have equal := valid (probe marker)
  change eval family (probe marker) identity.lhs =
    eval family (probe marker) identity.rhs at equal
  rw [← probe_four_left family notRight marker identity.lhs,
    ← probe_four_left family notRight marker identity.rhs, equal]

theorem terminal_marker_cut_of_valid [DecidableEq α]
    (left right : Word α) (a b : α)
    (valid : (Identity.mk (left ++ Word.singleton a) (right ++ Word.singleton b)).SatisfiedBy
      (table 3).semigroup) (marker : α) :
    (marker ∉ left.toList ∧ a = marker) ↔ (marker ∉ right.toList ∧ b = marker) := by
  have equal := valid (probe marker)
  change eval 3 (probe marker) (left ++ Word.singleton a) =
    eval 3 (probe marker) (right ++ Word.singleton b) at equal
  rw [← probe_four_right_cut marker left a, ← probe_four_right_cut marker right b, equal]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations

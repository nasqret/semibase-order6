import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Counts

/-! The literal counts/ford/postS/first-prefix-parity signature and its
necessary direction. First-occurrence parity is not restricted to simple markers. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Observations

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395Markers Msg0457S11395Parity
open Msg0457S11395Suffix Msg0457S11395Counts

structure SameSignature (left right : Word Nat) : Prop where
  counts : ∀ letter, countCap (left.toList.count letter) = countCap (right.toList.count letter)
  firstOrder : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList
  suffixSupport : ∀ separator,
    S5_254.GloballySimple left separator → S5_254.GloballySimple right separator →
    ∀ tested, tested ∈ suffixAfter separator left.toList ↔ tested ∈ suffixAfter separator right.toList
  prefixParity : ∀ separator, separator ∈ left.toList → separator ∈ right.toList →
    ∀ tested, (S5_254.simplePrefixBefore separator left.toList).count tested % 2 =
      (S5_254.simplePrefixBefore separator right.toList).count tested % 2

theorem SameSignature.support {left right : Word Nat} (same : SameSignature left right) :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList := by
  intro letter
  have capped := ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts letter)).1
  constructor
  · intro member
    have positive := List.count_pos_iff.mpr member
    exact List.count_pos_iff.mp (by omega)
  · intro member
    have positive := List.count_pos_iff.mpr member
    exact List.count_pos_iff.mp (by omega)

theorem SameSignature.simple {left right : Word Nat} (same : SameSignature left right) (letter : Nat) :
    S5_254.GloballySimple left letter ↔ S5_254.GloballySimple right letter := by
  have capped := ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts letter)).1
  change left.toList.count letter = 1 ↔ right.toList.count letter = 1
  omega

theorem prefix_absent (separator : Nat) (xs : List Nat) :
    separator ∉ S5_254.simplePrefixBefore separator xs := by
  induction xs with
  | nil => simp [S5_254.simplePrefixBefore]
  | cons x xs ih =>
      by_cases equal : x = separator
      · simp [S5_254.simplePrefixBefore, equal]
      · simp [S5_254.simplePrefixBefore, equal, Ne.symm equal, ih]

theorem suffix_absent_of_simple (word : Word Nat) (separator : Nat)
    (simple : S5_254.GloballySimple word separator) : separator ∉ suffixAfter separator word.toList := by
  have present : separator ∈ word.toList := List.count_pos_iff.mp (by rw [simple]; decide)
  obtain ⟨before, after, shape, absent⟩ := PrefixCount.split_first separator present
  rw [shape, suffixAfter_split separator before after absent]
  intro member
  have positive := List.count_pos_iff.mpr member
  change word.toList.count separator = 1 at simple
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

theorem sameSignature_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) : SameSignature identity.lhs identity.rhs := by
  refine ⟨countCap_of_valid identity valid, firstOrder_of_valid identity valid, ?_, ?_⟩
  · intro separator ls rs tested
    by_cases equal : tested = separator
    · subst tested
      simp only [suffix_absent_of_simple identity.lhs separator ls,
        suffix_absent_of_simple identity.rhs separator rs]
    · exact suffixSupport_of_valid identity valid separator tested ls rs equal
  · intro separator lp rp tested
    by_cases equal : tested = separator
    · subst tested
      rw [List.count_eq_zero.mpr (prefix_absent _ _), List.count_eq_zero.mpr (prefix_absent _ _)]
    · exact firstPrefixParity_of_valid identity valid separator tested lp rp equal

theorem any_eq_of_support (left right : List α) (predicate : α → Bool)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : left.any predicate = right.any predicate := by
  cases hl : left.any predicate <;> cases hr : right.any predicate
  · rfl
  · obtain ⟨x, hx, px⟩ := List.any_eq_true.mp hr
    have yes := List.any_eq_true.mpr ⟨x, (same x).mpr hx, px⟩
    simp [hl] at yes
  · obtain ⟨x, hx, px⟩ := List.any_eq_true.mp hl
    have yes := List.any_eq_true.mpr ⟨x, (same x).mp hx, px⟩
    simp [hr] at yes
  · rfl

theorem SameSignature.countPMin {left right : Word Nat} (same : SameSignature left right)
    (predicate : Nat → Bool) : min (left.toList.countP predicate) 2 = min (right.toList.countP predicate) 2 :=
  countP_min_eq _ _ predicate (fun x => ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts x)).1)

theorem groupBit_eq_of_parities (left right : List Nat) (valuation : Nat → Fin 6)
    (same : ∀ x, left.count x % 2 = right.count x % 2) : groupBit valuation left = groupBit valuation right := by
  rw [groupBit_eq_parityBit, groupBit_eq_parityBit]
  unfold parityBit
  rw [countP_mod_eq left right (fun x => valuation x == (3 : Fin 6)) same]

theorem SameSignature.groupBit {left right : Word Nat} (same : SameSignature left right)
    (valuation : Nat → Fin 6) : groupBit valuation left.toList = groupBit valuation right.toList :=
  groupBit_eq_of_parities _ _ valuation
    (fun x => ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts x)).2)

def firstHit (predicate : Nat → Bool) (xs : List Nat) : Option Nat := (xs.filter predicate).head?

theorem firstHit_eq_ford (predicate : Nat → Bool) (xs : List Nat) :
    firstHit predicate xs = firstHit predicate (firstOccurrenceSequence xs) := by
  have heads : ∀ ys : List Nat, (firstOccurrenceSequence ys).head? = ys.head? := by
    intro ys
    cases ys <;> rfl
  have equal := congrArg List.head? (firstOccurrenceSequence_filter predicate xs)
  rw [heads] at equal
  exact equal

theorem SameSignature.firstHit {left right : Word Nat} (same : SameSignature left right)
    (predicate : Nat → Bool) : firstHit predicate left.toList = firstHit predicate right.toList := by
  rw [firstHit_eq_ford predicate left.toList, firstHit_eq_ford predicate right.toList, same.firstOrder]

theorem firstHit_some_split (predicate : Nat → Bool) (xs : List Nat) (separator : Nat)
    (hit : firstHit predicate xs = some separator) :
    ∃ before after, xs = before ++ separator :: after ∧ predicate separator = true ∧
      ∀ x ∈ before, predicate x = false := by
  induction xs with
  | nil => simp [firstHit] at hit
  | cons x xs ih =>
      cases px : predicate x with
      | true =>
          have equal : x = separator := by simpa [firstHit, px] using hit
          subst separator
          exact ⟨[], xs, rfl, px, by simp⟩
      | false =>
          have tailHit : firstHit predicate xs = some separator := by simpa [firstHit, px] using hit
          obtain ⟨before, after, shape, selected, prior⟩ := ih tailHit
          refine ⟨x :: before, after, by simp [shape], selected, ?_⟩
          intro y member
          rcases List.mem_cons.mp member with equal | later
          · simpa [equal] using px
          · exact prior y later

theorem firstHit_none (predicate : Nat → Bool) (xs : List Nat)
    (empty : firstHit predicate xs = none) : ∀ x ∈ xs, predicate x = false := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases px : predicate x with
      | true => simp [firstHit, px] at empty
      | false =>
          have tailNone : firstHit predicate xs = none := by simpa [firstHit, px] using empty
          intro y member
          rcases List.mem_cons.mp member with equal | later
          · simpa [equal] using px
          · exact ih tailNone y later

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Observations

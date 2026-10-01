import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Observations

/-! Exact unrestricted semantic signature of the literal S11395 table.
Actual derivational reach in the approved B12 is a separate obligation. -/

set_option maxRecDepth 1000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Signature

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395Markers Msg0457S11395Parity
open Msg0457S11395Suffix Msg0457S11395Counts Msg0457S11395Observations

theorem false_of_countP_zero (predicate : α → Bool) (xs : List α)
    (zero : xs.countP predicate = 0) (x : α) (member : x ∈ xs) : predicate x = false := by
  cases hit : predicate x with
  | false => rfl
  | true =>
      have positive : 0 < xs.countP predicate := List.countP_pos_iff.mpr ⟨x, member, hit⟩
      omega

theorem false_of_any_false (predicate : α → Bool) (xs : List α)
    (zero : xs.any predicate = false) (x : α) (member : x ∈ xs) : predicate x = false := by
  cases hit : predicate x with
  | false => rfl
  | true =>
      have yes : xs.any predicate = true := List.any_eq_true.mpr ⟨x, member, hit⟩
      simp [zero] at yes

theorem safe_of_tests : ∀ a : Fin 6, (a == 0) = false → isNil a = false → 2 ≤ a.val := by decide
theorem units_of_safe : ∀ a : Fin 6, 2 ≤ a.val → isLeft a = false → a = 2 ∨ a = 3 := by decide

theorem safe_of_zero_nil_absent (valuation : Nat → Fin 6) (xs : List Nat)
    (zero : xs.any (fun x => valuation x == (0 : Fin 6)) = false)
    (nilZero : xs.countP (fun x => isNil (valuation x)) = 0) :
    ∀ x ∈ xs, 2 ≤ (valuation x).val := by
  intro x member
  exact safe_of_tests _ (false_of_any_false _ _ zero x member)
    (false_of_countP_zero _ _ nilZero x member)

theorem simple_of_unique_nil (valuation : Nat → Fin 6) (xs : List Nat) (separator : Nat)
    (member : separator ∈ xs) (nilSeparator : isNil (valuation separator) = true)
    (unique : xs.countP (fun x => isNil (valuation x)) = 1) : xs.count separator = 1 := by
  have positive := List.count_pos_iff.mpr member
  have bound : xs.count separator ≤ xs.countP (fun x => isNil (valuation x)) := by
    rw [← List.count_filter (l := xs) (p := fun x => isNil (valuation x)) nilSeparator,
      List.countP_eq_length_filter]
    exact List.count_le_length
  omega

theorem eval_one_nil (valuation : Nat → Fin 6) (word : Word Nat) (separator : Nat)
    (zero : word.toList.any (fun x => valuation x == (0 : Fin 6)) = false)
    (unique : word.toList.countP (fun x => isNil (valuation x)) = 1)
    (present : separator ∈ word.toList) (nilSeparator : isNil (valuation separator) = true) :
    table.semigroup.eval valuation word =
      if (suffixAfter separator word.toList).any (fun x => isLeft (valuation x)) then (0 : Fin 6) else (1 : Fin 6) := by
  obtain ⟨before, after, shape, absent⟩ := PrefixCount.split_first separator present
  have counts : before.countP (fun x => isNil (valuation x)) +
      (after.countP (fun x => isNil (valuation x)) + 1) = 1 := by
    simpa [shape, List.countP_cons, nilSeparator] using unique
  have beforeZero : before.countP (fun x => isNil (valuation x)) = 0 := by omega
  have afterZero : after.countP (fun x => isNil (valuation x)) = 0 := by omega
  have beforeSafe : ∀ x ∈ before, 2 ≤ (valuation x).val := by
    intro x member
    exact safe_of_tests _
      (false_of_any_false _ _ zero x (by rw [shape]; simp [member]))
      (false_of_countP_zero _ _ beforeZero x member)
  have afterSafe : ∀ x ∈ after, 2 ≤ (valuation x).val := by
    intro x member
    exact safe_of_tests _
      (false_of_any_false _ _ zero x (by rw [shape]; simp [member]))
      (false_of_countP_zero _ _ afterZero x member)
  have nilValue : valuation separator = (1 : Fin 6) := by simpa [isNil] using nilSeparator
  rw [eval_eq_evalList, shape, suffixAfter_split separator before after absent]
  exact uniqueNil_split valuation before after separator nilValue beforeSafe afterSafe

theorem firstHit_some_mem (predicate : Nat → Bool) (xs : List Nat) (separator : Nat)
    (hit : firstHit predicate xs = some separator) : separator ∈ xs := by
  obtain ⟨before, after, shape, _, _⟩ := firstHit_some_split predicate xs separator hit
  simp [shape]

theorem eval_first_left (valuation : Nat → Fin 6) (word : Word Nat) (separator : Nat)
    (zero : word.toList.any (fun x => valuation x == (0 : Fin 6)) = false)
    (nilZero : word.toList.countP (fun x => isNil (valuation x)) = 0)
    (hit : firstHit (fun x => isLeft (valuation x)) word.toList = some separator) :
    table.semigroup.eval valuation word =
      leftValue ((valuation separator == (5 : Fin 6)) !=
        groupBit valuation (S5_254.simplePrefixBefore separator word.toList)) := by
  obtain ⟨before, after, shape, selected, prior⟩ := firstHit_some_split _ word.toList separator hit
  have safe := safe_of_zero_nil_absent valuation word.toList zero nilZero
  have absent : separator ∉ before := by
    intro member
    have no := prior separator member
    simp [selected] at no
  have units : ∀ x ∈ before, valuation x = (2 : Fin 6) ∨ valuation x = (3 : Fin 6) := by
    intro x member
    exact units_of_safe _ (safe x (by rw [shape]; simp [member])) (prior x member)
  have afterSafe : ∀ x ∈ after, 2 ≤ (valuation x).val := by
    intro x member
    exact safe x (by rw [shape]; simp [member])
  rw [eval_eq_evalList, shape, S5_254.simplePrefixBefore_split separator before after absent]
  exact firstLeft_split valuation before after separator selected units afterSafe

theorem eval_all_units (valuation : Nat → Fin 6) (word : Word Nat)
    (zero : word.toList.any (fun x => valuation x == (0 : Fin 6)) = false)
    (nilZero : word.toList.countP (fun x => isNil (valuation x)) = 0)
    (hit : firstHit (fun x => isLeft (valuation x)) word.toList = none) :
    table.semigroup.eval valuation word = groupValue (groupBit valuation word.toList) := by
  rw [eval_eq_evalList]
  apply evalList_units
  intro x member
  exact units_of_safe _ (safe_of_zero_nil_absent valuation word.toList zero nilZero x member)
    (firstHit_none _ _ hit x member)

theorem valid_of_sameSignature (identity : Identity Nat)
    (same : SameSignature identity.lhs identity.rhs) : identity.SatisfiedBy table.semigroup := by
  intro valuation
  have zeroEqual := any_eq_of_support identity.lhs.toList identity.rhs.toList
    (fun x => valuation x == (0 : Fin 6)) same.support
  cases leftZero : identity.lhs.toList.any (fun x => valuation x == (0 : Fin 6)) with
  | true =>
      have rightZero := zeroEqual.symm.trans leftZero
      rw [eval_zero_of_zero valuation identity.lhs leftZero,
        eval_zero_of_zero valuation identity.rhs rightZero]
  | false =>
      have rightZero := zeroEqual.symm.trans leftZero
      have counts := same.countPMin (fun x => isNil (valuation x))
      by_cases many : 2 ≤ identity.lhs.toList.countP (fun x => isNil (valuation x))
      · have rightMany : 2 ≤ identity.rhs.toList.countP (fun x => isNil (valuation x)) := by omega
        rw [eval_zero_of_two_nil valuation identity.lhs many,
          eval_zero_of_two_nil valuation identity.rhs rightMany]
      · by_cases noneNil : identity.lhs.toList.countP (fun x => isNil (valuation x)) = 0
        · have rightNone : identity.rhs.toList.countP (fun x => isNil (valuation x)) = 0 := by omega
          have firstEqual := same.firstHit (fun x => isLeft (valuation x))
          cases leftHit : firstHit (fun x => isLeft (valuation x)) identity.lhs.toList with
          | none =>
              have rightHit := firstEqual.symm.trans leftHit
              rw [eval_all_units valuation identity.lhs leftZero noneNil leftHit,
                eval_all_units valuation identity.rhs rightZero rightNone rightHit, same.groupBit valuation]
          | some separator =>
              have rightHit := firstEqual.symm.trans leftHit
              have lp := firstHit_some_mem _ _ separator leftHit
              have rp := firstHit_some_mem _ _ separator rightHit
              have bits := groupBit_eq_of_parities _ _ valuation (same.prefixParity separator lp rp)
              rw [eval_first_left valuation identity.lhs separator leftZero noneNil leftHit,
                eval_first_left valuation identity.rhs separator rightZero rightNone rightHit, bits]
        · have leftOne : identity.lhs.toList.countP (fun x => isNil (valuation x)) = 1 := by omega
          have rightOne : identity.rhs.toList.countP (fun x => isNil (valuation x)) = 1 := by omega
          have positive : 0 < identity.lhs.toList.countP (fun x => isNil (valuation x)) := by omega
          obtain ⟨separator, lp, nilSeparator⟩ := List.countP_pos_iff.mp positive
          have rp := (same.support separator).mp lp
          have ls : S5_254.GloballySimple identity.lhs separator :=
            simple_of_unique_nil valuation _ separator lp nilSeparator leftOne
          have rs := (same.simple separator).mp ls
          have suffixEqual := any_eq_of_support _ _ (fun x => isLeft (valuation x))
            (same.suffixSupport separator ls rs)
          rw [eval_one_nil valuation identity.lhs separator leftZero leftOne lp nilSeparator,
            eval_one_nil valuation identity.rhs separator rightZero rightOne rp nilSeparator, suffixEqual]

theorem valid_iff_sameSignature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨sameSignature_of_valid identity, valid_of_sameSignature identity⟩

theorem derives_preserve_signature {left right : Word Nat} (derivation : Derives basis left right) :
    SameSignature left right := sameSignature_of_valid ⟨left, right⟩ (derivation.sound models)

/-- This actual-B12 obligation is not assumed or inhabited by this semantic theorem. -/
def SignatureReach : Prop := ∀ left right : Word Nat, SameSignature left right → Derives basis left right

theorem basisFor_iff_signatureReach : BasisFor table.semigroup basis ↔ SignatureReach := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left,right⟩ (valid_of_sameSignature ⟨left,right⟩ same)
  · intro reach
    exact ⟨models, fun identity valid => reach _ _ (sameSignature_of_valid identity valid)⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Signature

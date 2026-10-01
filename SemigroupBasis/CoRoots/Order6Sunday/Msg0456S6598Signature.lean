import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Prefix

/-! Exact unrestricted counts/preS/bL semantics for the literal S6598 table.
The final equivalence exposes, but does not inhabit, B25 derivational reach. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Signature

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Erasure
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Prefix
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang

structure SameSignature (left right : Word Nat) : Prop where
  counts : ∀ letter, countCap (left.toList.count letter) = countCap (right.toList.count letter)
  prefixSupport : ∀ separator,
    S5_254.GloballySimple left separator → S5_254.GloballySimple right separator →
    ∀ tested, tested ∈ S5_254.simplePrefixBefore separator left.toList ↔
      tested ∈ S5_254.simplePrefixBefore separator right.toList
  prefixParity : ∀ separator,
    S5_254.GloballySimple left separator → S5_254.GloballySimple right separator →
    ∀ tested, (S5_254.simplePrefixBefore separator left.toList).count tested % 2 =
      (S5_254.simplePrefixBefore separator right.toList).count tested % 2

theorem SameSignature.toM18 {left right : Word Nat} (same : SameSignature left right) :
    S5_254.SameM18Signature left right where
  support := by
    intro letter
    have capped := ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts letter)).1
    constructor
    · intro member
      have positive := List.count_pos_iff.mpr member
      exact List.count_pos_iff.mp (by omega)
    · intro member
      have positive := List.count_pos_iff.mpr member
      exact List.count_pos_iff.mp (by omega)
  totalParity := fun letter => ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts letter)).2
  globallySimple := by
    intro letter
    have capped := ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts letter)).1
    change left.toList.count letter = 1 ↔ right.toList.count letter = 1
    omega
  prefixParity := by
    intro separator ls rs tested parity
    rw [S5_254.prefixParityBefore_iff_prefixValue ls,
      S5_254.prefixParityBefore_iff_prefixValue rs, same.prefixParity separator ls rs tested]

theorem separator_absent_from_prefix (separator : Nat) (xs : List Nat) :
    separator ∉ S5_254.simplePrefixBefore separator xs := by
  induction xs with
  | nil => simp [S5_254.simplePrefixBefore]
  | cons x xs ih =>
      by_cases equal : x = separator
      · simp [S5_254.simplePrefixBefore, equal]
      · simp [S5_254.simplePrefixBefore, equal, Ne.symm equal, ih]

theorem sameSignature_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) : SameSignature identity.lhs identity.rhs := by
  have m18 := m18Signature_of_valid identity valid
  refine ⟨cap_eq_of_m18 m18, ?_, fun separator ls rs tested => m18.prefixValue_eq separator tested ls rs⟩
  intro separator ls rs tested
  by_cases equal : tested = separator
  · subst tested
    simp only [separator_absent_from_prefix]
  · have evaluated := valid (prefixProbe separator tested)
    rw [prefixProbe_eval _ _ _ ls equal, prefixProbe_eval _ _ _ rs equal] at evaluated
    by_cases leftPresent : tested ∈ S5_254.simplePrefixBefore separator identity.lhs.toList <;>
      by_cases rightPresent : tested ∈ S5_254.simplePrefixBefore separator identity.rhs.toList <;>
      simp_all

theorem blocked_eq_of_sameSignature_nil {left right : Word Nat}
    (same : SameSignature left right) (valuation : Nat → Fin 6)
    (leftNil : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) left = (1 : Fin 5) ∨
      S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) left = (2 : Fin 5))
    (rightNil : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) right = (1 : Fin 5) ∨
      S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) right = (2 : Fin 5)) :
    (summaryList valuation left.toList).blockedNil = (summaryList valuation right.toList).blockedNil := by
  have leftUnique := nil_count_eq_one_of_erased valuation left leftNil
  have rightUnique := nil_count_eq_one_of_erased valuation right rightNil
  have positive : 0 < left.toList.countP (fun x => isNil (valuation x)) := by omega
  obtain ⟨separator, member, nilSeparator⟩ := List.countP_pos_iff.mp positive
  have ls : S5_254.GloballySimple left separator :=
    simple_of_unique_nil valuation left.toList separator member nilSeparator leftUnique
  have rs := (same.toM18.globallySimple separator).mp ls
  rw [blocked_eq_prefix_any valuation left separator ls nilSeparator leftUnique,
    blocked_eq_prefix_any valuation right separator rs nilSeparator rightUnique]
  exact any_eq_of_sameSupport _ _ _ (same.prefixSupport separator ls rs)

theorem valid_of_sameSignature (identity : Identity Nat)
    (same : SameSignature identity.lhs identity.rhs) : identity.SatisfiedBy table.semigroup := by
  have m18Valid : identity.SatisfiedBy S5_254.table.semigroup :=
    (S5_254.derivesOfSameM18Signature same.toM18).sound S5_254.models
  intro valuation
  have erasedEqual := m18Valid (fun x => eraseKill (valuation x))
  have killEqual := any_eq_of_sameSupport identity.lhs.toList identity.rhs.toList
    (fun x => valuation x == (5 : Fin 6)) same.toM18.support
  by_cases leftNil : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs = (1 : Fin 5) ∨
      S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs = (2 : Fin 5)
  · have rightNil : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.rhs = (1 : Fin 5) ∨
        S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.rhs = (2 : Fin 5) := by
      simpa only [erasedEqual] using leftNil
    have blockedEqual := blocked_eq_of_sameSignature_nil same valuation leftNil rightNil
    rw [eval_eq_restore valuation identity.lhs, eval_eq_restore valuation identity.rhs,
      erasedEqual, killEqual, blockedEqual]
  · by_cases leftZero : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs = (0 : Fin 5)
    · have rightZero : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.rhs = (0 : Fin 5) :=
        erasedEqual.symm.trans leftZero
      rw [eval_eq_restore valuation identity.lhs, eval_eq_restore valuation identity.rhs, leftZero, rightZero]
      simp [restore, embedValue]
    · have values : ∀ a : Fin 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by decide
      have leftUnit : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs = (3 : Fin 5) ∨
          S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs = (4 : Fin 5) := by
        rcases values (S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.lhs) with h|h|h|h|h
        · exact False.elim (leftZero h)
        · exact False.elim (leftNil (Or.inl h))
        · exact False.elim (leftNil (Or.inr h))
        · exact Or.inl h
        · exact Or.inr h
      have rightUnit : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.rhs = (3 : Fin 5) ∨
          S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) identity.rhs = (4 : Fin 5) := by
        simpa only [erasedEqual] using leftUnit
      have leftCount := nil_count_eq_zero_of_erased valuation identity.lhs leftUnit
      have rightCount := nil_count_eq_zero_of_erased valuation identity.rhs rightUnit
      rw [eval_eq_restore valuation identity.lhs, eval_eq_restore valuation identity.rhs,
        summary_blocked_noNil valuation identity.lhs.toList leftCount,
        summary_blocked_noNil valuation identity.rhs.toList rightCount, erasedEqual, killEqual]

theorem valid_iff_sameSignature (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨sameSignature_of_valid identity, valid_of_sameSignature identity⟩

theorem derives_preserve_signature {left right : Word Nat} (derivation : Derives basis left right) :
    SameSignature left right := sameSignature_of_valid ⟨left,right⟩ (derivation.sound models)

/-- This remains a separate, uninhabited target-B25 obligation. -/
def SignatureReach : Prop :=
  ∀ left right : Word Nat, SameSignature left right → Derives basis left right

theorem basisFor_iff_signatureReach : BasisFor table.semigroup basis ↔ SignatureReach := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left,right⟩ (valid_of_sameSignature ⟨left,right⟩ same)
  · intro reach
    exact ⟨models, fun identity valid => reach _ _ (sameSignature_of_valid identity valid)⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Signature

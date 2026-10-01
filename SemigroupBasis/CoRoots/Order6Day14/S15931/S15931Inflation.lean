import SemigroupBasis.CoRoots.Order6Day14.S15931.S15931Presentation
import SemigroupBasis.CoRoots.S5_1155Invariant

/-! Inflate only the tail, keeping a nonempty prefix at every rewrite.
The lower factor's semantic signature then fixes every inflated exponent. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S15931

open SemigroupBasis

def inflateList : List Nat → List Nat
  | [] => []
  | letter :: tail => letter :: letter :: letter :: letter :: inflateList tail

theorem inflateList_eq_flatMap (tail : List Nat) :
    inflateList tail = tail.flatMap (fun letter => List.replicate 4 letter) := by
  induction tail with
  | nil => rfl
  | cons letter tail ih =>
      simp [inflateList, List.replicate_succ, ih]

def inflateWord (word : Word Nat) : Word Nat :=
  ⟨word.head, inflateList word.tail⟩

theorem inflateWord_head (word : Word Nat) : (inflateWord word).head = word.head := rfl

theorem derivesInflateTail (tail : List Nat) (pre : Word Nat) :
    Derives basis (appendTail pre tail) (appendTail pre (inflateList tail)) := by
  induction tail generalizing pre with
  | nil => exact Derives.refl _
  | cons letter rest ih =>
      have expanded : Derives basis (appendTail pre (letter :: rest))
          (appendTail (appendTail pre [letter, letter, letter, letter]) rest) := by
        have contextual := derivesAppendTail (rawLaw01 pre (Word.singleton letter)) rest
        simpa [appendTail, Word.append, Word.singleton, List.append_assoc] using contextual
      have remainder := ih (appendTail pre [letter, letter, letter, letter])
      simpa [inflateList, appendTail, List.append_assoc] using expanded.trans remainder

theorem derivesInflateWord (word : Word Nat) : Derives basis word (inflateWord word) := by
  cases word with
  | mk head tail =>
      simpa [appendTail, Word.singleton, inflateWord] using
        derivesInflateTail tail (Word.singleton head)

theorem inflateList_count (tail : List Nat) (letter : Nat) :
    (inflateList tail).count letter = 4 * tail.count letter := by
  induction tail with
  | nil => simp [inflateList]
  | cons head rest ih =>
      by_cases equal : head = letter
      · subst head
        simp only [inflateList, List.count_cons_self, ih]
        omega
      · simp [inflateList, equal, ih]

theorem word_count (word : Word Nat) (letter : Nat) :
    word.toList.count letter = (if word.head = letter then 1 else 0) + word.tail.count letter := by
  cases word with
  | mk head tail =>
      by_cases equal : head = letter
      · subst head
        simp [Word.toList, Nat.add_comm]
      · simp [Word.toList, equal]

theorem inflated_count (word : Word Nat) (letter : Nat) :
    (inflateWord word).toList.count letter =
      (if word.head = letter then 1 else 0) + 4 * word.tail.count letter := by
  rw [word_count]
  change (if word.head = letter then 1 else 0) + (inflateList word.tail).count letter = _
  rw [inflateList_count]

theorem inflated_count_zero_iff (word : Word Nat) (letter : Nat) :
    (inflateWord word).toList.count letter = 0 ↔ word.toList.count letter = 0 := by
  rw [inflated_count, word_count]
  by_cases equal : word.head = letter
  · simp only [if_pos equal]
    omega
  · simp only [if_neg equal]
    omega

theorem inflated_count_one_iff (word : Word Nat) (letter : Nat) :
    (inflateWord word).toList.count letter = 1 ↔
      letter = word.head ∧ word.toList.count word.head = 1 := by
  constructor
  · intro one
    have formula := inflated_count word letter
    have equal : word.head = letter := by
      by_cases equal : word.head = letter
      · exact equal
      · rw [if_neg equal] at formula
        omega
    rw [if_pos equal] at formula
    have tailZero : word.tail.count letter = 0 := by omega
    have headTailZero : word.tail.count word.head = 0 := by
      rw [equal]
      exact tailZero
    have original := word_count word word.head
    rw [if_pos rfl] at original
    refine ⟨equal.symm, ?_⟩
    omega
  · rintro ⟨equal, one⟩
    have original := word_count word word.head
    rw [if_pos rfl] at original
    have headTailZero : word.tail.count word.head = 0 := by omega
    have tailZero : word.tail.count letter = 0 := by
      rw [equal]
      exact headTailZero
    have formula := inflated_count word letter
    rw [if_pos equal.symm] at formula
    omega

theorem inflated_count_mod_three (word : Word Nat) (letter : Nat) :
    (inflateWord word).toList.count letter % 3 = word.toList.count letter % 3 := by
  rw [inflated_count, word_count]
  by_cases equal : word.head = letter
  · simp only [if_pos equal]
    omega
  · simp only [if_neg equal]
    omega

theorem uniqueHead_iff_of_sameSignature (left right : Word Nat)
    (same : SemigroupBasis.CoRoots.S5_1155.SameSemanticSignature left right) :
    left.toList.count left.head = 1 ↔ right.toList.count right.head = 1 := by
  have markers := same.simpleInitial
  unfold SemigroupBasis.CoRoots.S5_1155.simpleInitialMarker at markers
  by_cases leftOne : left.toList.count left.head = 1
  · by_cases rightOne : right.toList.count right.head = 1
    · exact iff_of_true leftOne rightOne
    · simp only [if_pos leftOne, if_neg rightOne] at markers
      cases markers
  · by_cases rightOne : right.toList.count right.head = 1
    · simp only [if_neg leftOne, if_pos rightOne] at markers
      cases markers
    · exact iff_of_false leftOne rightOne

theorem exponent_eq_of_zero_one_mod (left right : Nat)
    (zero : left = 0 ↔ right = 0) (one : left = 1 ↔ right = 1)
    (modulo : left % 3 = right % 3) :
    Examples.periodThreeFromTwoExponent left = Examples.periodThreeFromTwoExponent right := by
  by_cases leftZero : left = 0
  · have rightZero := zero.mp leftZero
    rw [leftZero, rightZero]
  · by_cases leftOne : left = 1
    · have rightOne := one.mp leftOne
      rw [leftOne, rightOne]
    · have rightNotZero : right ≠ 0 := fun h => leftZero (zero.mpr h)
      have rightNotOne : right ≠ 1 := fun h => leftOne (one.mpr h)
      unfold Examples.periodThreeFromTwoExponent
      rw [if_neg (by omega : ¬ left < 2), if_neg (by omega : ¬ right < 2)]
      omega

theorem inflated_exponents_eq (left right : Word Nat)
    (heads : left.head = right.head)
    (same : SemigroupBasis.CoRoots.S5_1155.SameSemanticSignature left right)
    (letter : Nat) :
    Examples.periodThreeFromTwoExponent ((inflateWord left).toList.count letter) =
      Examples.periodThreeFromTwoExponent ((inflateWord right).toList.count letter) := by
  apply exponent_eq_of_zero_one_mod
  · rw [inflated_count_zero_iff, inflated_count_zero_iff]
    constructor
    · intro leftZero
      apply List.count_eq_zero.mpr
      intro member
      exact List.count_eq_zero.mp leftZero ((same.support letter).mpr member)
    · intro rightZero
      apply List.count_eq_zero.mpr
      intro member
      exact List.count_eq_zero.mp rightZero ((same.support letter).mp member)
  · rw [inflated_count_one_iff, inflated_count_one_iff]
    have unique := uniqueHead_iff_of_sameSignature left right same
    constructor
    · rintro ⟨equal, count⟩
      exact ⟨equal.trans heads, unique.mp count⟩
    · rintro ⟨equal, count⟩
      exact ⟨equal.trans heads.symm, unique.mpr count⟩
  · rw [inflated_count_mod_three, inflated_count_mod_three]
    exact same.positiveMultiplicityModuloThree letter

theorem derivesOfHeadAndSignature (left right : Word Nat)
    (heads : left.head = right.head)
    (same : SemigroupBasis.CoRoots.S5_1155.SameSemanticSignature left right) :
    Derives basis left right := by
  have middle : Derives Examples.headSortedPeriodThreeFromTwoBasis
      (inflateWord left) (inflateWord right) :=
    Examples.headSortedPeriodThreeFromTwoDerivesOfInvariantEq
      (inflateWord left) (inflateWord right) heads (inflated_exponents_eq left right heads same)
  exact (derivesInflateWord left).trans
    ((transportNormalizer middle).trans (derivesInflateWord right).symm)

end SemigroupBasis.CoRoots.Order6Day14.S15931

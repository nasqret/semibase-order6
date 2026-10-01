import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Moves
import SemigroupBasis.CoRoots.S5_443Semantics

/-! Unrestricted necessity of msg0447 section A's exact proposed key.
The first-occurrence coordinate is read in LRB3. Capped counts and support
after simple letters are transported from the existing S5_614 semantics in
the reversed orientation. No bounded test is a premise of these proofs. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis
open SemigroupBasis.Examples

namespace KeyTheory

private def initialEval (valuation : Nat → Fin 3) (word : List Nat) : Fin 3 :=
  word.foldl (fun current x => leftRegularBandThreeMul current (valuation x)) 1

private theorem initialEval_word (valuation : Nat → Fin 3) (word : Word Nat) :
    initialTable.semigroup.eval valuation word = initialEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change tail.foldl (fun current x => leftRegularBandThreeMul current (valuation x))
          (valuation head) =
        tail.foldl (fun current x => leftRegularBandThreeMul current (valuation x))
          (leftRegularBandThreeMul 1 (valuation head))
      rw [show leftRegularBandThreeMul 1 (valuation head) = valuation head by
        simp [leftRegularBandThreeMul]]

private theorem initialFold_absorbs (valuation : Nat → Fin 3) (value : Fin 3)
    (nonidentity : value ≠ 1) (word : List Nat) :
    word.foldl (fun current x => leftRegularBandThreeMul current (valuation x)) value = value := by
  induction word with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.foldl_cons]
      rw [show leftRegularBandThreeMul value (valuation x) = value by
        simp [leftRegularBandThreeMul, nonidentity]]
      exact ih

private theorem initialEval_hit (valuation : Nat → Fin 3) (x : Nat) (rest : List Nat)
    (nonidentity : valuation x ≠ 1) : initialEval valuation (x :: rest) = valuation x := by
  unfold initialEval
  simp only [List.foldl_cons]
  rw [show leftRegularBandThreeMul 1 (valuation x) = valuation x by simp [leftRegularBandThreeMul]]
  exact initialFold_absorbs valuation (valuation x) nonidentity rest

private theorem initialEval_skip (valuation : Nat → Fin 3) (x : Nat) (rest : List Nat)
    (identity : valuation x = 1) : initialEval valuation (x :: rest) = initialEval valuation rest := by
  simp [initialEval, leftRegularBandThreeMul, identity]

private theorem initialFold_congr (first second : Nat → Fin 3) :
    ∀ (word : List Nat) (acc : Fin 3),
      (∀ x, x ∈ word → first x = second x) →
      word.foldl (fun current x => leftRegularBandThreeMul current (first x)) acc =
        word.foldl (fun current x => leftRegularBandThreeMul current (second x)) acc
  | [], _, _ => rfl
  | x :: rest, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head rest)]
      exact initialFold_congr first second rest (leftRegularBandThreeMul acc (second x))
        (fun y member => agree y (List.Mem.tail x member))

private theorem initialEval_congr (first second : Nat → Fin 3) (word : List Nat)
    (agree : ∀ x, x ∈ word → first x = second x) :
    initialEval first word = initialEval second word :=
  initialFold_congr first second word 1 agree

private theorem nodup_separated : ∀ {left right : List Nat}, left.Nodup → right.Nodup →
    (∀ valuation : Nat → Fin 3, initialEval valuation left = initialEval valuation right) → left = right
  | [], [], _, _, _ => rfl
  | [], y :: rest, _, _, same => by
      let valuation : Nat → Fin 3 := fun z => if z = y then 0 else 1
      have equal := same valuation
      have rightValue : initialEval valuation (y :: rest) = 0 := by
        simpa [valuation] using initialEval_hit valuation y rest (by simp [valuation])
      have leftValue : initialEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at equal
      exact False.elim ((by decide : (1 : Fin 3) ≠ 0) equal)
  | x :: rest, [], _, _, same => by
      let valuation : Nat → Fin 3 := fun z => if z = x then 0 else 1
      have equal := same valuation
      have leftValue : initialEval valuation (x :: rest) = 0 := by
        simpa [valuation] using initialEval_hit valuation x rest (by simp [valuation])
      have rightValue : initialEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at equal
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) equal)
  | x :: left, y :: right, leftNodup, rightNodup, same => by
      have heads : x = y := by
        apply Decidable.byContradiction
        intro different
        let valuation : Nat → Fin 3 := fun z => if z = x then 0 else if z = y then 2 else 1
        have equal := same valuation
        have leftValue : initialEval valuation (x :: left) = 0 := by
          simpa [valuation] using initialEval_hit valuation x left (by simp [valuation])
        have rightValue : initialEval valuation (y :: right) = 2 := by
          simpa [valuation, Ne.symm different] using
            initialEval_hit valuation y right (by simp [valuation, Ne.symm different])
        rw [leftValue, rightValue] at equal
        exact (by decide : (0 : Fin 3) ≠ 2) equal
      subst y
      have leftAbsent : x ∉ left := (List.nodup_cons.mp leftNodup).1
      have rightAbsent : x ∉ right := (List.nodup_cons.mp rightNodup).1
      have tails : ∀ valuation : Nat → Fin 3, initialEval valuation left = initialEval valuation right := by
        intro valuation
        let masked : Nat → Fin 3 := fun z => if z = x then 1 else valuation z
        have full := same masked
        have maskX : masked x = 1 := by simp [masked]
        rw [initialEval_skip masked x left maskX, initialEval_skip masked x right maskX] at full
        calc
          initialEval valuation left = initialEval masked left := by
            apply initialEval_congr
            intro z member
            have different : z ≠ x := by intro equal; subst z; exact leftAbsent member
            simp [masked, different]
          _ = initialEval masked right := full
          _ = initialEval valuation right := by
            apply initialEval_congr
            intro z member
            have different : z ≠ x := by intro equal; subst z; exact rightAbsent member
            simp [masked, different]
      exact congrArg (List.cons x)
        (nodup_separated (List.nodup_cons.mp leftNodup).2 (List.nodup_cons.mp rightNodup).2 tails)

private theorem initialEval_normal (word : Word Nat) (valuation : Nat → Fin 3) :
    initialEval valuation (firstOccurrenceSequence word.toList) = initialTable.semigroup.eval valuation word := by
  have normal := lrbDerivesNormal word
  cases shape : firstOccurrenceSequence word.toList with
  | nil => rw [shape] at normal; exact False.elim normal
  | cons head tail =>
      rw [shape] at normal
      change Derives leftRegularBandThreeBasis word (Word.mk head tail) at normal
      have sound := normal.sound leftRegularBandThreeBasis_models valuation
      calc
        initialEval valuation (head :: tail) = initialTable.semigroup.eval valuation (Word.mk head tail) :=
          (initialEval_word valuation (Word.mk head tail)).symm
        _ = initialTable.semigroup.eval valuation word := sound.symm

theorem valid_ford (identity : Identity Nat) (valid : identity.SatisfiedBy initialTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList = firstOccurrenceSequence identity.rhs.toList := by
  apply nodup_separated (firstOccurrenceSequence_nodup _) (firstOccurrenceSequence_nodup _)
  intro valuation
  exact (initialEval_normal identity.lhs valuation).trans
    ((valid valuation).trans (initialEval_normal identity.rhs valuation).symm)

theorem cap22_eq_exponent (count : Nat) : cap22 count = periodTwoFromTwoExponent count := rfl

theorem cap22_eq_one_iff (count : Nat) : cap22 count = 1 ↔ count = 1 := by
  unfold cap22
  split <;> omega

theorem cap22_eq_zero_iff (count : Nat) : cap22 count = 0 ↔ count = 0 := by
  unfold cap22
  split <;> omega

private theorem lower_reversed_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy lowerTable.semigroup) :
    identity.reversed.SatisfiedBy lowerTable.semigroup.opposite := by
  apply (Identity.satisfiedBy_opposite_iff_reversed identity.reversed lowerTable.semigroup).mpr
  simpa using valid

theorem lower_valid_counts (identity : Identity Nat)
    (valid : identity.SatisfiedBy lowerTable.semigroup) (letter : Nat) :
    cap22 (identity.lhs.toList.count letter) = cap22 (identity.rhs.toList.count letter) := by
  have same := SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics.valid_exponent_eq
    identity.reversed (lower_reversed_valid identity valid) letter
  simpa [cap22_eq_exponent, Identity.reversed] using same

/-- The actual suffix after a unique marker. Defining it by reversal reuses
the certified lower-table prefix separator without changing its orientation. -/
def postList (word : List Nat) (marker : Nat) : List Nat :=
  (SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics.prefixBefore marker word.reverse).reverse

theorem postList_split (marker : Nat) (before after : List Nat)
    (simple : (before ++ marker :: after).count marker = 1) :
    postList (before ++ marker :: after) marker = after := by
  have absent := SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics.marker_not_mem_parts_of_count_one
    marker before after simple
  unfold postList
  have reversed : (before ++ marker :: after).reverse = after.reverse ++ marker :: before.reverse := by
    simp [List.append_assoc]
  rw [reversed, SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics.prefixBefore_split
    marker after.reverse before.reverse (by simpa using absent.2)]
  simp

theorem lower_valid_post (identity : Identity Nat)
    (valid : identity.SatisfiedBy lowerTable.semigroup) (marker selected : Nat)
    (lhsSimple : identity.lhs.toList.count marker = 1)
    (rhsSimple : identity.rhs.toList.count marker = 1) :
    selected ∈ postList identity.lhs.toList marker ↔ selected ∈ postList identity.rhs.toList marker := by
  have leftCount : identity.reversed.lhs.toList.count marker = 1 := by
    simpa [Identity.reversed] using lhsSimple
  have rightCount : identity.reversed.rhs.toList.count marker = 1 := by
    simpa [Identity.reversed] using rhsSimple
  have same := SemigroupBasis.CoRoots.S5_443Family.S5_614Semantics.valid_prefixBefore_iff
    identity.reversed (lower_reversed_valid identity valid) marker selected leftCount rightCount
  simpa [postList, Identity.reversed] using same

structure SameKey (left right : List Nat) : Prop where
  ford : firstOccurrenceSequence left = firstOccurrenceSequence right
  counts : ∀ letter, cap22 (left.count letter) = cap22 (right.count letter)
  post : ∀ marker selected, left.count marker = 1 →
    (selected ∈ postList left marker ↔ selected ∈ postList right marker)

namespace SameKey

theorem simple {left right : List Nat} (same : SameKey left right) (letter : Nat) :
    left.count letter = 1 ↔ right.count letter = 1 := by
  rw [← cap22_eq_one_iff (left.count letter), ← cap22_eq_one_iff (right.count letter),
    same.counts letter]

theorem absent {left right : List Nat} (same : SameKey left right) (letter : Nat) :
    letter ∉ left ↔ letter ∉ right := by
  rw [← List.count_eq_zero, ← List.count_eq_zero, ← cap22_eq_zero_iff (left.count letter),
    ← cap22_eq_zero_iff (right.count letter), same.counts letter]

theorem refl (word : List Nat) : SameKey word word :=
  ⟨rfl, fun _ => rfl, fun _ _ _ => Iff.rfl⟩

theorem symm {left right : List Nat} (same : SameKey left right) : SameKey right left :=
  ⟨same.ford.symm, fun x => (same.counts x).symm,
   fun marker selected simpleRight => (same.post marker selected ((same.simple marker).mpr simpleRight)).symm⟩

theorem trans {left middle right : List Nat} (first : SameKey left middle) (second : SameKey middle right) :
    SameKey left right :=
  ⟨first.ford.trans second.ford, fun x => (first.counts x).trans (second.counts x),
   fun marker selected simpleLeft => (first.post marker selected simpleLeft).trans
     (second.post marker selected ((first.simple marker).mp simpleLeft))⟩

end SameKey

/-- The three proposed key coordinates are necessary at unrestricted rank
and length for the literal table. Sufficiency is the remaining reach proof. -/
theorem valid_sameKey (identity : Identity Nat)
    (valid : identity.SatisfiedBy Representative.table.semigroup) :
    SameKey identity.lhs.toList identity.rhs.toList := by
  have factors := (Representative.valid_iff_factors identity).mp valid
  have counts := lower_valid_counts identity factors.2
  refine ⟨valid_ford identity factors.1, counts, ?_⟩
  intro marker selected simpleLeft
  have simpleRight : identity.rhs.toList.count marker = 1 := by
    apply (cap22_eq_one_iff _).mp
    rw [← counts marker, (cap22_eq_one_iff _).mpr simpleLeft]
  exact lower_valid_post identity factors.2 marker selected simpleLeft simpleRight

theorem derives_sameKey {left right : Word Nat} (derivation : Derives basis left right) :
    SameKey left.toList right.toList :=
  valid_sameKey ⟨left, right⟩ (derivation.sound Representative.models)

theorem listDerives_sameKey {left right : List Nat} (derivation : Moves.L left right) :
    SameKey left right := by
  cases derivation with
  | empty => exact SameKey.refl []
  | words wordDerivation => exact derives_sameKey wordDerivation

end KeyTheory
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

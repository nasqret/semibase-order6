import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the stored three-element left normal band
`[[1,1,1],[1,2,1],[3,3,3]]`. -/
def leftNormalBandThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 1 then 1 else 0) else 2

/-- The Smallsemi representative `S3_13`. -/
def leftNormalBandThree : FiniteTable where
  order := 3
  mul := leftNormalBandThreeMul
  assoc := by decide

def leftNormalBandX : Word Nat := Word.singleton 0
def leftNormalBandXX : Word Nat := ⟨0, [0]⟩
def leftNormalBandXYZ : Word Nat := ⟨0, [1, 2]⟩
def leftNormalBandXZY : Word Nat := ⟨0, [2, 1]⟩

def leftNormalBandIdempotenceLaw : Identity Nat :=
  ⟨leftNormalBandX, leftNormalBandXX⟩

def leftNormalBandSuffixCommutationLaw : Identity Nat :=
  ⟨leftNormalBandXYZ, leftNormalBandXZY⟩

/-- The exact basis `x = xx`, `xyz = xzy`. -/
def leftNormalBandThreeBasis : List (Identity Nat) :=
  [leftNormalBandIdempotenceLaw, leftNormalBandSuffixCommutationLaw]

private def instantiateThreeWords (p u v : Word Nat) : Nat → Word Nat
  | 0 => p
  | 1 => u
  | 2 => v
  | n + 3 => Word.singleton (n + 3)

theorem leftNormalBandDerivesIdempotence (u : Word Nat) :
    Derives leftNormalBandThreeBasis u (u ++ u) := by
  have hbase :
      Derives leftNormalBandThreeBasis leftNormalBandX leftNormalBandXX :=
    Derives.fromBasis (e := leftNormalBandIdempotenceLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [leftNormalBandThreeBasis, leftNormalBandIdempotenceLaw,
    leftNormalBandX, leftNormalBandXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton] using h

/-- Arbitrary nonempty blocks after a fixed nonempty prefix may be swapped. -/
theorem leftNormalBandDerivesSuffixSwap (p u v : Word Nat) :
    Derives leftNormalBandThreeBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives leftNormalBandThreeBasis
        leftNormalBandXYZ leftNormalBandXZY :=
    Derives.fromBasis (e := leftNormalBandSuffixCommutationLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [leftNormalBandThreeBasis, leftNormalBandSuffixCommutationLaw,
    leftNormalBandXYZ, leftNormalBandXZY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton] using h

/-- A letter already occurring in a word may be appended.  If it is the first
letter, duplicate it there and commute the duplicate past the suffix; otherwise
recurse inside the suffix and preserve the original first letter. -/
theorem leftNormalBandDerivesAppendMember (w : Word Nat) (x : Nat)
    (hx : x ∈ w.toList) :
    Derives leftNormalBandThreeBasis w (w ++ Word.singleton x) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp only [Word.toList, List.mem_singleton] at hx
          subst x
          exact leftNormalBandDerivesIdempotence (Word.singleton head)
      | cons next rest =>
          let suffix : Word Nat := ⟨next, rest⟩
          simp only [Word.toList, List.mem_cons] at hx
          rcases hx with hxHead | hxTail
          · subst x
            have duplicateHead :=
              leftNormalBandDerivesIdempotence (Word.singleton head)
            have duplicateBeforeSuffix :=
              Derives.appendRight duplicateHead suffix
            have moveDuplicate :=
              leftNormalBandDerivesSuffixSwap
                (Word.singleton head) (Word.singleton head) suffix
            exact Derives.trans
              (by
                simpa [suffix, Word.append_assoc] using duplicateBeforeSuffix)
              (by
                simpa [suffix, Word.append_assoc] using moveDuplicate)
          · have suffixMembership : x ∈ suffix.toList := by
              simpa [suffix, Word.toList] using hxTail
            have suffixStep :=
              leftNormalBandDerivesAppendMember suffix x suffixMembership
            have prefixed :=
              Derives.prepend (Word.singleton head) suffixStep
            simpa [suffix, Word.append_assoc] using prefixed

theorem leftNormalBandDerivesAppendList (w : Word Nat) (xs : List Nat)
    (hcontent : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives leftNormalBandThreeBasis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have hx : x ∈ w.toList :=
        hcontent x (List.Mem.head xs)
      have firstStep :=
        leftNormalBandDerivesAppendMember w x hx
      have remainingContent :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          hcontent y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) remainingContent
      exact Derives.trans firstStep <| by
        simpa [Word.append, Word.singleton, List.append_assoc] using restStep

theorem leftNormalBandDerivesContentExpansion (u v : Word Nat)
    (hcontent : ∀ x, x ∈ v.toList → x ∈ u.toList) :
    Derives leftNormalBandThreeBasis u (u ++ v) := by
  have h := leftNormalBandDerivesAppendList u v.toList hcontent
  simpa [Word.toList, Word.append] using h

/-- Words with the same first letter commute as whole blocks.  The proof only
uses suffix commutation, with separate singleton-tail cases because words are
nonempty. -/
theorem leftNormalBandDerivesConcatSwap (u v : Word Nat)
    (heads : u.head = v.head) :
    Derives leftNormalBandThreeBasis (u ++ v) (v ++ u) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads
          subst vHead
          cases uTail with
          | nil =>
              cases vTail with
              | nil =>
                  exact Derives.refl _
              | cons vNext vRest =>
                  let vSuffix : Word Nat := ⟨vNext, vRest⟩
                  simpa [vSuffix, Word.append_assoc] using
                    leftNormalBandDerivesSuffixSwap
                      (Word.singleton uHead) (Word.singleton uHead) vSuffix
          | cons uNext uRest =>
              let uSuffix : Word Nat := ⟨uNext, uRest⟩
              cases vTail with
              | nil =>
                  exact Derives.symm <| by
                    simpa [uSuffix, Word.append_assoc] using
                      leftNormalBandDerivesSuffixSwap
                        (Word.singleton uHead) (Word.singleton uHead) uSuffix
              | cons vNext vRest =>
                  let vSuffix : Word Nat := ⟨vNext, vRest⟩
                  have firstSwap :=
                    leftNormalBandDerivesSuffixSwap
                      (Word.singleton uHead) uSuffix
                      (Word.singleton uHead ++ vSuffix)
                  have secondSwap :=
                    Derives.appendRight
                      (leftNormalBandDerivesSuffixSwap
                        (Word.singleton uHead) (Word.singleton uHead) vSuffix)
                      uSuffix
                  exact Derives.trans
                    (by
                      simpa [uSuffix, vSuffix, Word.append_assoc] using
                        firstSwap)
                    (by
                      simpa [uSuffix, vSuffix, Word.append_assoc] using
                        secondSwap)

private theorem leftNormalBandMul_eq_one_iff (a b : Fin 3) :
    leftNormalBandThreeMul a b = (1 : Fin 3) ↔
      a = (1 : Fin 3) ∧ b = (1 : Fin 3) := by
  decide +revert

private theorem leftNormalBandFold_eq_one_iff
    (valuation : Nat → Fin 3) (xs : List Nat) (acc : Fin 3) :
    xs.foldl
        (fun current x => leftNormalBandThreeMul current (valuation x)) acc =
          (1 : Fin 3) ↔
      acc = (1 : Fin 3) ∧
        ∀ x, x ∈ xs → valuation x = (1 : Fin 3) := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil, List.not_mem_nil, false_implies,
        forall_const, and_true]
  | cons x xs ih =>
      rw [List.foldl_cons, ih, leftNormalBandMul_eq_one_iff]
      constructor
      · rintro ⟨⟨hacc, hx⟩, hxs⟩
        exact ⟨hacc, fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · simpa [hy] using hx
          · exact hxs y hy⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall x (List.Mem.head xs)⟩,
          fun y hy => hall y (List.Mem.tail x hy)⟩

theorem leftNormalBandEval_eq_one_iff (valuation : Nat → Fin 3)
    (w : Word Nat) :
    leftNormalBandThree.semigroup.eval valuation w = (1 : Fin 3) ↔
      ∀ x, x ∈ w.toList → valuation x = (1 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftNormalBandThreeMul current (valuation x))
            (valuation head) = (1 : Fin 3) ↔
          ∀ x, x ∈ head :: tail → valuation x = (1 : Fin 3)
      rw [leftNormalBandFold_eq_one_iff]
      constructor
      · rintro ⟨hhead, htail⟩ x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · simpa [hx] using hhead
        · exact htail x hx
      · intro hall
        exact ⟨hall head (List.Mem.head tail),
          fun x hx => hall x (List.Mem.tail head hx)⟩

private theorem leftNormalBandFold_from_zero
    (valuation : Nat → Fin 3) (xs : List Nat) :
    xs.foldl
        (fun current x => leftNormalBandThreeMul current (valuation x))
        (0 : Fin 3) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, leftNormalBandThreeMul, if_pos]
      exact ih

private theorem leftNormalBandFold_from_two
    (valuation : Nat → Fin 3) (xs : List Nat) :
    xs.foldl
        (fun current x => leftNormalBandThreeMul current (valuation x))
        (2 : Fin 3) = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have twoNeZero : (2 : Fin 3) ≠ 0 := by decide
      have twoNeOne : (2 : Fin 3) ≠ 1 := by decide
      simpa [List.foldl_cons, leftNormalBandThreeMul, twoNeZero,
        twoNeOne] using ih

private theorem leftNormalBandEval_of_head_zero
    (valuation : Nat → Fin 3) (w : Word Nat)
    (headZero : valuation w.head = (0 : Fin 3)) :
    leftNormalBandThree.semigroup.eval valuation w = (0 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftNormalBandThreeMul current (valuation x))
            (valuation head) = 0
      rw [headZero]
      exact leftNormalBandFold_from_zero valuation tail

private theorem leftNormalBandEval_of_head_two
    (valuation : Nat → Fin 3) (w : Word Nat)
    (headTwo : valuation w.head = (2 : Fin 3)) :
    leftNormalBandThree.semigroup.eval valuation w = (2 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftNormalBandThreeMul current (valuation x))
            (valuation head) = 2
      rw [headTwo]
      exact leftNormalBandFold_from_two valuation tail

private def supportSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 0 else 1

theorem leftNormalBandSeparator_eq_one_iff (z : Nat) (w : Word Nat) :
    leftNormalBandThree.semigroup.eval (supportSeparator z) w =
        (1 : Fin 3) ↔
      z ∉ w.toList := by
  rw [leftNormalBandEval_eq_one_iff]
  constructor
  · intro hall hz
    have := hall z hz
    simp [supportSeparator] at this
  · intro hz x hx
    have hne : x ≠ z := by
      intro h
      apply hz
      simpa [h] using hx
    simp [supportSeparator, hne]

theorem leftNormalBandValid_support_eq (e : Identity Nat)
    (valid : e.SatisfiedBy leftNormalBandThree.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have rhsOne :
        leftNormalBandThree.semigroup.eval (supportSeparator z) e.rhs =
          (1 : Fin 3) :=
      (leftNormalBandSeparator_eq_one_iff z e.rhs).2 hr
    have lhsNotOne :
        leftNormalBandThree.semigroup.eval (supportSeparator z) e.lhs ≠
          (1 : Fin 3) := by
      intro lhsOne
      exact (leftNormalBandSeparator_eq_one_iff z e.lhs).1 lhsOne hl
    exact lhsNotOne (evaluated.trans rhsOne)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have lhsOne :
        leftNormalBandThree.semigroup.eval (supportSeparator z) e.lhs =
          (1 : Fin 3) :=
      (leftNormalBandSeparator_eq_one_iff z e.lhs).2 hl
    have rhsNotOne :
        leftNormalBandThree.semigroup.eval (supportSeparator z) e.rhs ≠
          (1 : Fin 3) := by
      intro rhsOne
      exact (leftNormalBandSeparator_eq_one_iff z e.rhs).1 rhsOne hr
    exact rhsNotOne (evaluated.symm.trans lhsOne)

private def firstLetterSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 0 else 2

theorem leftNormalBandValid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy leftNormalBandThree.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation := firstLetterSeparator e.lhs.head
  have evaluated := valid valuation
  have lhsZero : valuation e.lhs.head = (0 : Fin 3) := by
    simp [valuation, firstLetterSeparator]
  have rhsTwo : valuation e.rhs.head = (2 : Fin 3) := by
    simp [valuation, firstLetterSeparator, Ne.symm headsNe]
  rw [leftNormalBandEval_of_head_zero valuation e.lhs lhsZero,
    leftNormalBandEval_of_head_two valuation e.rhs rhsTwo] at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

private theorem leftNormalBandMul_idempotent (a : Fin 3) :
    leftNormalBandThreeMul a a = a := by
  decide +revert

private theorem leftNormalBandMul_left_normal (a b c : Fin 3) :
    leftNormalBandThreeMul (leftNormalBandThreeMul a b) c =
      leftNormalBandThreeMul (leftNormalBandThreeMul a c) b := by
  decide +revert

theorem leftNormalBandThreeBasis_models :
    Models leftNormalBandThree.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      leftNormalBandThreeMul (valuation 0) (valuation 0)
    exact (leftNormalBandMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      leftNormalBandThreeMul
          (leftNormalBandThreeMul (valuation 0) (valuation 1))
          (valuation 2) =
        leftNormalBandThreeMul
          (leftNormalBandThreeMul (valuation 0) (valuation 2))
          (valuation 1)
    exact leftNormalBandMul_left_normal
      (valuation 0) (valuation 1) (valuation 2)

theorem leftNormalBandThreeBasis_complete :
    BasisFor leftNormalBandThree.semigroup leftNormalBandThreeBasis := by
  refine ⟨leftNormalBandThreeBasis_models, ?_⟩
  intro e valid
  have heads := leftNormalBandValid_head_eq e valid
  have supportEq := leftNormalBandValid_support_eq e valid
  have lhsExpansion :
      Derives leftNormalBandThreeBasis e.lhs (e.lhs ++ e.rhs) :=
    leftNormalBandDerivesContentExpansion e.lhs e.rhs
      (fun x hx => (supportEq x).2 hx)
  have rhsExpansion :
      Derives leftNormalBandThreeBasis e.rhs (e.rhs ++ e.lhs) :=
    leftNormalBandDerivesContentExpansion e.rhs e.lhs
      (fun x hx => (supportEq x).1 hx)
  exact Derives.trans lhsExpansion <|
    Derives.trans
      (leftNormalBandDerivesConcatSwap e.lhs e.rhs heads)
      (Derives.symm rhsExpansion)

def leftNormalBandThreeOppositeBasis : List (Identity Nat) :=
  reversedBasis leftNormalBandThreeBasis

theorem leftNormalBandThreeOppositeBasis_complete :
    BasisFor leftNormalBandThree.semigroup.opposite
      leftNormalBandThreeOppositeBasis := by
  simpa [leftNormalBandThreeOppositeBasis] using
    leftNormalBandThreeBasis_complete.oppositeReversed

end SemigroupBasis.Examples

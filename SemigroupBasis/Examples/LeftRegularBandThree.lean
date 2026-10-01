import SemigroupBasis.Opposite
import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the exact zero-based form of
`[[1,1,1],[1,2,3],[3,3,3]]`. -/
def leftRegularBandThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 1 then b else a

/-- The three-element left regular band `S3_16`. -/
def leftRegularBandThree : FiniteTable where
  order := 3
  mul := leftRegularBandThreeMul
  assoc := by decide

def lrbX : Word Nat := Word.singleton 0
def lrbXX : Word Nat := ⟨0, [0]⟩
def lrbXY : Word Nat := ⟨0, [1]⟩
def lrbXYX : Word Nat := ⟨0, [1, 0]⟩

def lrbIdempotenceLaw : Identity Nat :=
  ⟨lrbX, lrbXX⟩

def lrbRegularLaw : Identity Nat :=
  ⟨lrbXY, lrbXYX⟩

/-- The classical left-regular-band basis `x = xx`, `xy = xyx`. -/
def leftRegularBandThreeBasis : List (Identity Nat) :=
  [lrbIdempotenceLaw, lrbRegularLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem lrbDerivesIdempotenceContraction (u : Word Nat) :
    Derives leftRegularBandThreeBasis (u ++ u) u := by
  have hbase :
      Derives leftRegularBandThreeBasis lrbX lrbXX :=
    Derives.fromBasis (e := lrbIdempotenceLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  exact Derives.symm <| by
    simpa [leftRegularBandThreeBasis, lrbIdempotenceLaw, lrbX, lrbXX,
      instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem lrbDerivesRegularContraction (u v : Word Nat) :
    Derives leftRegularBandThreeBasis ((u ++ v) ++ u) (u ++ v) := by
  have hbase :
      Derives leftRegularBandThreeBasis lrbXY lrbXYX :=
    Derives.fromBasis (e := lrbRegularLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  exact Derives.symm <| by
    simpa [leftRegularBandThreeBasis, lrbRegularLaw, lrbXY, lrbXYX,
      instantiateTwoWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Delete one later occurrence of the initial letter, across an arbitrary
middle block and with an arbitrary suffix. -/
private theorem lrbDerivesDeleteOne (x : Nat) (middle suffix : List Nat) :
    Derives leftRegularBandThreeBasis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton] using
            lrbDerivesIdempotenceContraction (Word.singleton x)
      | cons y ys =>
          have h :=
            Derives.appendRight
              (lrbDerivesIdempotenceContraction (Word.singleton x))
              (wordOfCons y ys)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
  | cons y ys =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              lrbDerivesRegularContraction
                (Word.singleton x) (wordOfCons y ys)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (lrbDerivesRegularContraction
                (Word.singleton x) (wordOfCons y ys))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h

/-- Delete every occurrence of `x` in `rest`, preserving the intervening
letters and their order. -/
private theorem lrbDerivesDeleteAfter :
    ∀ (x : Nat) (middle rest : List Nat),
      Derives leftRegularBandThreeBasis
        (wordOfCons x (middle ++ rest))
        (wordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x))))
  | x, middle, [] => by
      simpa using Derives.refl (wordOfCons x middle)
  | x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        have first := lrbDerivesDeleteOne x middle ys
        have remaining := lrbDerivesDeleteAfter x middle ys
        exact Derives.trans first <| by
          simpa using remaining
      · have remaining :=
          lrbDerivesDeleteAfter x (middle ++ [y]) ys
        simpa [hy, List.append_assoc] using remaining

/-- Keep precisely the first occurrence of each letter, in its original
order. The definition is structurally recursive from the right. -/
def firstOccurrenceSequence : List Nat → List Nat
  | [] => []
  | x :: xs =>
      x :: (firstOccurrenceSequence xs).filter
        (fun y => decide (y ≠ x))

theorem firstOccurrenceSequence_nodup (xs : List Nat) :
    (firstOccurrenceSequence xs).Nodup := by
  induction xs with
  | nil =>
      exact List.nodup_nil
  | cons x xs ih =>
      simp only [firstOccurrenceSequence]
      exact List.nodup_cons.2 ⟨by simp, ih.filter _⟩

theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat)
    (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬ keep selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat} (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro next member
      exact decide_eq_true <| by
        intro equal
        subst next
        exact data.1 member

private theorem firstOccurrenceSequence_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    firstOccurrenceSequence (x :: xs) ≠ [] := by
  simp [firstOccurrenceSequence]

/-- Every nonempty word derives to its first-occurrence sequence. -/
private theorem lrbDerivesNormalizeList :
    ∀ x xs,
      match firstOccurrenceSequence (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives leftRegularBandThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := lrbDerivesNormalizeList y ys
      cases hs : firstOccurrenceSequence (y :: ys) with
      | nil =>
          exact False.elim
            (firstOccurrenceSequence_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have deleted :=
            lrbDerivesDeleteAfter x [] (z :: zs)
          have reduced :
              firstOccurrenceSequence (x :: y :: ys) =
                x :: (z :: zs).filter (fun a => decide (a ≠ x)) := by
            change
              x :: (firstOccurrenceSequence (y :: ys)).filter
                  (fun a => decide (a ≠ x)) =
                x :: (z :: zs).filter (fun a => decide (a ≠ x))
            rw [hs]
          rw [reduced]
          exact Derives.trans
            (by
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc] using prefixed)
            (by simpa [wordOfCons] using deleted)
termination_by
  _ xs => xs.length

theorem lrbDerivesNormal (w : Word Nat) :
    match firstOccurrenceSequence w.toList with
    | [] => False
    | x :: xs =>
        Derives leftRegularBandThreeBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact lrbDerivesNormalizeList head tail

/-- Evaluation of a possibly empty list, using the identity element `1`. -/
private def lrbListEval (valuation : Nat → Fin 3) (xs : List Nat) : Fin 3 :=
  xs.foldl
    (fun current x => leftRegularBandThreeMul current (valuation x)) 1

private theorem lrbEval_eq_listEval
    (valuation : Nat → Fin 3) (w : Word Nat) :
    leftRegularBandThree.semigroup.eval valuation w =
      lrbListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftRegularBandThreeMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              leftRegularBandThreeMul current (valuation x))
            (leftRegularBandThreeMul 1 (valuation head))
      rw [show leftRegularBandThreeMul 1 (valuation head) =
          valuation head by
        simp [leftRegularBandThreeMul]]

private theorem lrbFold_left_zero
    (valuation : Nat → Fin 3) (a : Fin 3) (ha : a ≠ 1)
    (xs : List Nat) :
    xs.foldl
        (fun current x => leftRegularBandThreeMul current (valuation x)) a =
      a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show leftRegularBandThreeMul a (valuation x) = a by
        simp [leftRegularBandThreeMul, ha]]
      exact ih

private theorem lrbListEval_cons_of_ne_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x ≠ 1) :
    lrbListEval valuation (x :: xs) = valuation x := by
  unfold lrbListEval
  simp only [List.foldl_cons]
  rw [show leftRegularBandThreeMul 1 (valuation x) = valuation x by
    simp [leftRegularBandThreeMul]]
  exact lrbFold_left_zero valuation (valuation x) hx xs

private theorem lrbListEval_cons_of_eq_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1) :
    lrbListEval valuation (x :: xs) = lrbListEval valuation xs := by
  simp [lrbListEval, leftRegularBandThreeMul, hx]

private theorem lrbFold_congr
    (v₁ v₂ : Nat → Fin 3) :
    ∀ (xs : List Nat) (acc : Fin 3),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            leftRegularBandThreeMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            leftRegularBandThreeMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact lrbFold_congr v₁ v₂ xs
        (leftRegularBandThreeMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem lrbListEval_congr
    (v₁ v₂ : Nat → Fin 3) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    lrbListEval v₁ xs = lrbListEval v₂ xs :=
  lrbFold_congr v₁ v₂ xs 1 agree

/-- Duplicate-free lists are separated by valuations in the three-element
band. Different heads receive the two left-zero values; after equal heads are
masked to the identity, induction compares the tails. -/
private theorem nodup_eq_of_lrbListEval_eq :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ valuation : Nat → Fin 3,
        lrbListEval valuation xs = lrbListEval valuation ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = y then 0 else 1
      have h := equalEval valuation
      have rightValue :
          lrbListEval valuation (y :: ys) = 0 :=
        by
          simpa [valuation] using
            lrbListEval_cons_of_ne_one valuation y ys (by
              simp [valuation])
      have leftValue : lrbListEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = x then 0 else 1
      have h := equalEval valuation
      have leftValue :
          lrbListEval valuation (x :: xs) = 0 :=
        by
          simpa [valuation] using
            lrbListEval_cons_of_ne_one valuation x xs (by
              simp [valuation])
      have rightValue : lrbListEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
  | x :: xs, y :: ys, nodupX, nodupY, equalEval => by
      have heads : x = y := by
        apply Decidable.byContradiction
        intro hxy
        let valuation : Nat → Fin 3 :=
          fun z => if z = x then 0 else if z = y then 2 else 1
        have h := equalEval valuation
        have leftValue :
            lrbListEval valuation (x :: xs) = 0 :=
          by
            simpa [valuation] using
              lrbListEval_cons_of_ne_one valuation x xs (by
                simp [valuation])
        have rightValue :
            lrbListEval valuation (y :: ys) = 2 :=
          by
            simpa [valuation, Ne.symm hxy] using
              lrbListEval_cons_of_ne_one valuation y ys (by
                simp [valuation, Ne.symm hxy])
        rw [leftValue, rightValue] at h
        exact (by decide : (0 : Fin 3) ≠ 2) h
      subst y
      have xNotMemXs : x ∉ xs := (List.nodup_cons.mp nodupX).1
      have xNotMemYs : x ∉ ys := (List.nodup_cons.mp nodupY).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 3,
            lrbListEval valuation xs = lrbListEval valuation ys := by
        intro valuation
        let masked : Nat → Fin 3 :=
          fun z => if z = x then 1 else valuation z
        have fullEqual := equalEval masked
        have maskedX : masked x = 1 := by simp [masked]
        rw [lrbListEval_cons_of_eq_one masked x xs maskedX,
          lrbListEval_cons_of_eq_one masked x ys maskedX] at fullEqual
        calc
          lrbListEval valuation xs =
              lrbListEval masked xs := by
                apply lrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemXs
                  simpa [h] using hz
                simp [masked, hzx]
          _ = lrbListEval masked ys := fullEqual
          _ = lrbListEval valuation ys := by
                apply lrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemYs
                  simpa [h] using hz
                simp [masked, hzx]
      congr 1
      exact nodup_eq_of_lrbListEval_eq
        (List.nodup_cons.mp nodupX).2
        (List.nodup_cons.mp nodupY).2 tailsEqual

private theorem lrbMul_idempotent (a : Fin 3) :
    leftRegularBandThreeMul a a = a := by
  decide +revert

private theorem lrbMul_regular (a b : Fin 3) :
    leftRegularBandThreeMul a b =
      leftRegularBandThreeMul (leftRegularBandThreeMul a b) a := by
  decide +revert

theorem leftRegularBandThreeBasis_models :
    Models leftRegularBandThree.semigroup
      leftRegularBandThreeBasis := by
  intro e he
  simp only [leftRegularBandThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      leftRegularBandThreeMul (valuation 0) (valuation 0)
    exact (lrbMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      leftRegularBandThreeMul (valuation 0) (valuation 1) =
        leftRegularBandThreeMul
          (leftRegularBandThreeMul (valuation 0) (valuation 1))
          (valuation 0)
    exact lrbMul_regular (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Every nonempty word
derives to its duplicate-free first-occurrence sequence, and the exact
three-element table separates any two different such sequences. -/
theorem leftRegularBandThreeBasis_complete :
    BasisFor leftRegularBandThree.semigroup
      leftRegularBandThreeBasis := by
  refine ⟨leftRegularBandThreeBasis_models, ?_⟩
  intro e valid
  have lhsNormal := lrbDerivesNormal e.lhs
  have rhsNormal := lrbDerivesNormal e.rhs
  cases hl : firstOccurrenceSequence e.lhs.toList with
  | nil =>
      exact False.elim
        (firstOccurrenceSequence_cons_ne_nil
          e.lhs.head e.lhs.tail (by
            simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : firstOccurrenceSequence e.rhs.toList with
      | nil =>
          exact False.elim
            (firstOccurrenceSequence_cons_ne_nil
              e.rhs.head e.rhs.tail (by
                simpa [Word.toList] using hr))
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 3,
                lrbListEval valuation (x :: xs) =
                  lrbListEval valuation (y :: ys) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound leftRegularBandThreeBasis_models valuation
            have rhsSound :=
              rhsNormal.sound leftRegularBandThreeBasis_models valuation
            rw [lrbEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have lhsNodup : (x :: xs).Nodup := by
            rw [← hl]
            exact firstOccurrenceSequence_nodup e.lhs.toList
          have rhsNodup : (y :: ys).Nodup := by
            rw [← hr]
            exact firstOccurrenceSequence_nodup e.rhs.toList
          have reducedEqual : x :: xs = y :: ys :=
            nodup_eq_of_lrbListEval_eq
              lhsNodup rhsNodup reducedEvalEqual
          cases reducedEqual
          exact Derives.trans lhsNormal (Derives.symm rhsNormal)

/-- Validity in the three-element left regular band determines the complete
first-occurrence sequence, not merely the support. -/
theorem firstOccurrenceSequence_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftRegularBandThree.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have lhsNormal := lrbDerivesNormal identity.lhs
  have rhsNormal := lrbDerivesNormal identity.rhs
  cases lhsShape :
      firstOccurrenceSequence identity.lhs.toList with
  | nil =>
      exact False.elim
        (firstOccurrenceSequence_cons_ne_nil
          identity.lhs.head identity.lhs.tail (by
            simpa [Word.toList] using lhsShape))
  | cons leftHead leftTail =>
      cases rhsShape :
          firstOccurrenceSequence identity.rhs.toList with
      | nil =>
          exact False.elim
            (firstOccurrenceSequence_cons_ne_nil
              identity.rhs.head identity.rhs.tail (by
                simpa [Word.toList] using rhsShape))
      | cons rightHead rightTail =>
          rw [lhsShape] at lhsNormal
          rw [rhsShape] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 3,
                lrbListEval valuation (leftHead :: leftTail) =
                  lrbListEval valuation (rightHead :: rightTail) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound leftRegularBandThreeBasis_models valuation
            have rhsSound :=
              rhsNormal.sound leftRegularBandThreeBasis_models valuation
            rw [lrbEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have leftNodup : (leftHead :: leftTail).Nodup := by
            rw [← lhsShape]
            exact firstOccurrenceSequence_nodup identity.lhs.toList
          have rightNodup : (rightHead :: rightTail).Nodup := by
            rw [← rhsShape]
            exact firstOccurrenceSequence_nodup identity.rhs.toList
          have reducedEqual : leftHead :: leftTail =
              rightHead :: rightTail :=
            nodup_eq_of_lrbListEval_eq
              leftNodup rightNodup reducedEvalEqual
          simpa [lhsShape, rhsShape] using reducedEqual

def leftRegularBandThreeOppositeBasis : List (Identity Nat) :=
  reversedBasis leftRegularBandThreeBasis

theorem leftRegularBandThreeOppositeBasis_complete :
    BasisFor leftRegularBandThree.semigroup.opposite
      leftRegularBandThreeOppositeBasis :=
  leftRegularBandThreeBasis_complete.oppositeReversed

end SemigroupBasis.Examples

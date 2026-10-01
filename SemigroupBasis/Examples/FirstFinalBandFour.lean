import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def firstFinalBandX : Word Nat := Word.singleton 0
def firstFinalBandXX : Word Nat := ⟨0, [0]⟩
def firstFinalBandXYZ : Word Nat := ⟨0, [1, 2]⟩
def firstFinalBandXYXZ : Word Nat := ⟨0, [1, 0, 2]⟩

def firstFinalBandIdempotenceLaw : Identity Nat :=
  ⟨firstFinalBandX, firstFinalBandXX⟩

def firstFinalBandReturnLaw : Identity Nat :=
  ⟨firstFinalBandXYZ, firstFinalBandXYXZ⟩

/-- The basis `x = xx`, `xyz = xyxz`. -/
def firstFinalBandBasis : List (Identity Nat) :=
  [firstFinalBandIdempotenceLaw, firstFinalBandReturnLaw]

private def firstFinalBandInstantiateThree
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem firstFinalBandDerivesIdempotenceContraction (u : Word Nat) :
    Derives firstFinalBandBasis (u ++ u) u := by
  have hbase :
      Derives firstFinalBandBasis firstFinalBandX firstFinalBandXX :=
    Derives.fromBasis (e := firstFinalBandIdempotenceLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (firstFinalBandInstantiateThree u u u)
  exact Derives.symm <| by
    simpa [firstFinalBandBasis, firstFinalBandIdempotenceLaw,
      firstFinalBandX, firstFinalBandXX,
      firstFinalBandInstantiateThree, Word.bind, Word.append,
      Word.singleton] using h

/-- A repeated nonempty block may be deleted when a nonempty suffix remains:
`uvuw = uvw`. -/
theorem firstFinalBandDerivesReturnContraction
    (u v q : Word Nat) :
    Derives firstFinalBandBasis
      (((u ++ v) ++ u) ++ q) ((u ++ v) ++ q) := by
  have hbase :
      Derives firstFinalBandBasis
        firstFinalBandXYZ firstFinalBandXYXZ :=
    Derives.fromBasis (e := firstFinalBandReturnLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (firstFinalBandInstantiateThree u v q)
  exact Derives.symm <| by
    simpa [firstFinalBandBasis, firstFinalBandReturnLaw,
      firstFinalBandXYZ, firstFinalBandXYXZ,
      firstFinalBandInstantiateThree, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using h

private def firstFinalWordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Delete one repeated letter while preserving a designated nonempty final
suffix. -/
private theorem firstFinalBandDerivesDeleteOne
    (x : Nat) (middle suffix : List Nat) (hsuffix : suffix ≠ []) :
    Derives firstFinalBandBasis
      (firstFinalWordOfCons x (middle ++ x :: suffix))
      (firstFinalWordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil => exact False.elim (hsuffix rfl)
      | cons y ys =>
          have h :=
            Derives.appendRight
              (firstFinalBandDerivesIdempotenceContraction
                (Word.singleton x))
              (firstFinalWordOfCons y ys)
          simpa [firstFinalWordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
  | cons y ys =>
      cases suffix with
      | nil => exact False.elim (hsuffix rfl)
      | cons z zs =>
          simpa [firstFinalWordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              firstFinalBandDerivesReturnContraction
                (Word.singleton x) (firstFinalWordOfCons y ys)
                (firstFinalWordOfCons z zs)

/-- Delete every later occurrence of `x` from a prefix while preserving a
fixed nonempty final suffix. -/
private theorem firstFinalBandDerivesDeleteAfter :
    ∀ (x : Nat) (middle rest suffix : List Nat), suffix ≠ [] →
      Derives firstFinalBandBasis
        (firstFinalWordOfCons x (middle ++ rest ++ suffix))
        (firstFinalWordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x)) ++ suffix))
  | x, middle, [], suffix, _ => by
      simpa using
        Derives.refl (firstFinalWordOfCons x (middle ++ suffix))
  | x, middle, y :: ys, suffix, hsuffix => by
      by_cases hy : y = x
      · subst y
        have first :=
          firstFinalBandDerivesDeleteOne
            x middle (ys ++ suffix) (by simp [hsuffix])
        have remaining :=
          firstFinalBandDerivesDeleteAfter
            x middle ys suffix hsuffix
        exact Derives.trans
          (by simpa [List.append_assoc] using first)
          (by simpa using remaining)
      · have remaining :=
          firstFinalBandDerivesDeleteAfter
            x (middle ++ [y]) ys suffix hsuffix
        simpa [hy, List.append_assoc] using remaining

/-- Normalize a nonempty prefix to its duplicate-free first-occurrence
sequence while preserving one final letter. -/
private theorem firstFinalBandDerivesNormalizePrefix :
    ∀ (x : Nat) (xs : List Nat) (final : Nat),
      match firstOccurrenceSequence (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives firstFinalBandBasis
            (firstFinalWordOfCons x (xs ++ [final]))
            (firstFinalWordOfCons y (ys ++ [final]))
  | x, [], final => by
      exact Derives.refl _
  | x, y :: ys, final => by
      have suffixNormal :=
        firstFinalBandDerivesNormalizePrefix y ys final
      cases hs : firstOccurrenceSequence (y :: ys) with
      | nil =>
          simp [firstOccurrenceSequence] at hs
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have deleted :=
            firstFinalBandDerivesDeleteAfter
              x [] (z :: zs) [final] (by simp)
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
              simpa [firstFinalWordOfCons, Word.append,
                Word.singleton, Word.append_assoc,
                List.append_assoc] using prefixed)
            (by
              simpa [firstFinalWordOfCons, List.append_assoc]
                using deleted)
termination_by
  _ xs _ => xs.length

/-- Remove a trailing copy of the designated final letter, if present. -/
def firstFinalBandTrimPrefix : List Nat → Nat → List Nat
  | [], _ => []
  | [x], final => if x = final then [] else [x]
  | x :: y :: ys, final =>
      x :: firstFinalBandTrimPrefix (y :: ys) final
termination_by
  xs _ => xs.length

private theorem firstFinalBandDerivesTrimPrefix :
    ∀ (pref : List Nat) (final : Nat),
      Derives firstFinalBandBasis
        (wordOfPrefixFinal pref final)
        (wordOfPrefixFinal
          (firstFinalBandTrimPrefix pref final) final)
  | [], final => by
      simpa [firstFinalBandTrimPrefix] using
        (Derives.refl (wordOfPrefixFinal [] final) :
          Derives firstFinalBandBasis
            (wordOfPrefixFinal [] final)
            (wordOfPrefixFinal [] final))
  | [x], final => by
      by_cases h : x = final
      · subst final
        simpa [firstFinalBandTrimPrefix, wordOfPrefixFinal,
          Word.append, Word.singleton] using
            firstFinalBandDerivesIdempotenceContraction
              (Word.singleton x)
      · simpa [firstFinalBandTrimPrefix, h] using
          (Derives.refl (wordOfPrefixFinal [x] final) :
            Derives firstFinalBandBasis
              (wordOfPrefixFinal [x] final)
              (wordOfPrefixFinal [x] final))
  | x :: y :: ys, final => by
      have tail :=
        firstFinalBandDerivesTrimPrefix (y :: ys) final
      simpa [firstFinalBandTrimPrefix, wordOfPrefixFinal] using
        Derives.prepend (Word.singleton x) tail
termination_by
  pref _ => pref.length

def firstFinalBandNormalPrefix
    (pref : List Nat) (final : Nat) : List Nat :=
  firstFinalBandTrimPrefix (firstOccurrenceSequence pref) final

private theorem firstFinalBandTrimPrefix_mem
    {z final : Nat} :
    ∀ {xs : List Nat},
      z ∈ firstFinalBandTrimPrefix xs final → z ∈ xs
  | [], h => by
      simp [firstFinalBandTrimPrefix] at h
  | [x], h => by
      by_cases hx : x = final
      · simp [firstFinalBandTrimPrefix, hx] at h
      · simpa [firstFinalBandTrimPrefix, hx] using h
  | x :: y :: ys, h => by
      simp only [firstFinalBandTrimPrefix, List.mem_cons] at h
      rcases h with rfl | htail
      · exact List.Mem.head _
      · exact List.Mem.tail x
          (firstFinalBandTrimPrefix_mem htail)
termination_by
  xs => xs.length

theorem firstFinalBandTrimPrefix_nodup
    (xs : List Nat) (final : Nat) (h : xs.Nodup) :
    (firstFinalBandTrimPrefix xs final).Nodup := by
  induction xs with
  | nil =>
      simp [firstFinalBandTrimPrefix]
  | cons x xs ih =>
      cases xs with
      | nil =>
          by_cases hx : x = final <;>
            simp [firstFinalBandTrimPrefix, hx]
      | cons y ys =>
          have hx :
              x ∉ firstFinalBandTrimPrefix (y :: ys) final := by
            intro hmem
            exact (List.nodup_cons.mp h).1 <|
              firstFinalBandTrimPrefix_mem hmem
          simpa [firstFinalBandTrimPrefix] using
            List.nodup_cons.2
              ⟨hx, ih (List.nodup_cons.mp h).2⟩

theorem firstFinalBandTrimPrefix_append_final
    (xs : List Nat) (final : Nat) :
    firstFinalBandTrimPrefix (xs ++ [final]) final = xs := by
  induction xs with
  | nil =>
      simp [firstFinalBandTrimPrefix]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [firstFinalBandTrimPrefix]
      | cons y ys =>
          simpa [firstFinalBandTrimPrefix] using
            congrArg (List.cons x) ih

private theorem firstFinalBandTrimPrefix_eq_self_of_not_mem
    (xs : List Nat) (final : Nat) (h : final ∉ xs) :
    firstFinalBandTrimPrefix xs final = xs := by
  induction xs with
  | nil => simp [firstFinalBandTrimPrefix]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx : x ≠ final := by
            intro hxf
            apply h
            simp [hxf]
          simp [firstFinalBandTrimPrefix, hx]
      | cons y ys =>
          have htail : final ∉ y :: ys := by
            intro hmem
            exact h (List.Mem.tail x hmem)
          simpa [firstFinalBandTrimPrefix] using
            congrArg (List.cons x) (ih htail)

private theorem firstFinalBandTrimPrefix_eq_nil :
    ∀ (xs : List Nat) (final : Nat),
      firstFinalBandTrimPrefix xs final = [] →
        xs = [] ∨ xs = [final]
  | [], _, _ => Or.inl rfl
  | [x], final, h => by
      by_cases hx : x = final
      · subst x
        exact Or.inr rfl
      · simp [firstFinalBandTrimPrefix, hx] at h
  | x :: y :: ys, final, h => by
      simp [firstFinalBandTrimPrefix] at h

theorem firstFinalBandTrimPrefix_idempotent_of_nodup
    (xs : List Nat) (final : Nat) (h : xs.Nodup) :
    firstFinalBandTrimPrefix
        (firstFinalBandTrimPrefix xs final) final =
      firstFinalBandTrimPrefix xs final := by
  induction xs with
  | nil => simp [firstFinalBandTrimPrefix]
  | cons x xs ih =>
      cases xs with
      | nil =>
          by_cases hx : x = final <;>
            simp [firstFinalBandTrimPrefix, hx]
      | cons y ys =>
          have htail := (List.nodup_cons.mp h).2
          have ih' := ih htail
          cases ht :
              firstFinalBandTrimPrefix (y :: ys) final with
          | nil =>
              have hxf : x ≠ final := by
                intro hxf
                subst x
                rcases firstFinalBandTrimPrefix_eq_nil
                    (y :: ys) final ht with hempty | hsingle
                · contradiction
                · exact (List.nodup_cons.mp h).1 <| by
                    simp [hsingle]
              simp [firstFinalBandTrimPrefix, ht, hxf]
          | cons z zs =>
              simpa [firstFinalBandTrimPrefix, ht] using
                congrArg (List.cons x) ih'

theorem firstFinalBandNormalPrefix_nodup
    (pref : List Nat) (final : Nat) :
    (firstFinalBandNormalPrefix pref final).Nodup := by
  exact firstFinalBandTrimPrefix_nodup
    (firstOccurrenceSequence pref) final
    (firstOccurrenceSequence_nodup pref)

theorem firstFinalBandNormalPrefix_fixed
    (pref : List Nat) (final : Nat) :
    firstFinalBandTrimPrefix
        (firstFinalBandNormalPrefix pref final) final =
      firstFinalBandNormalPrefix pref final := by
  exact firstFinalBandTrimPrefix_idempotent_of_nodup
    (firstOccurrenceSequence pref) final
    (firstOccurrenceSequence_nodup pref)

/-- Every word derives to a canonical duplicate-free first-occurrence prefix
followed by its final variable. If the prefix already ends in that variable,
the adjacent duplicate is contracted. -/
theorem firstFinalBandDerivesNormal (w : Word Nat) :
    Derives firstFinalBandBasis w
      (wordOfPrefixFinal
        (firstFinalBandNormalPrefix
          (splitPrefixFinal w).1 (splitPrefixFinal w).2)
        (splitPrefixFinal w).2) := by
  generalize hsplit : splitPrefixFinal w = split
  rcases split with ⟨pref, final⟩
  change
    Derives firstFinalBandBasis w
      (wordOfPrefixFinal
        (firstFinalBandNormalPrefix pref final) final)
  have reconstruct :
      wordOfPrefixFinal pref final = w := by
    have h := wordOfPrefixFinal_split w
    rw [hsplit] at h
    exact h
  cases pref with
  | nil =>
      have result :
          Derives firstFinalBandBasis
            (wordOfPrefixFinal [] final)
            (wordOfPrefixFinal
              (firstFinalBandNormalPrefix [] final)
              final) := by
        simpa [firstFinalBandNormalPrefix,
          firstOccurrenceSequence, firstFinalBandTrimPrefix] using
            (Derives.refl (wordOfPrefixFinal [] final) :
              Derives firstFinalBandBasis
                (wordOfPrefixFinal [] final)
                (wordOfPrefixFinal [] final))
      rw [reconstruct] at result
      exact result
  | cons x xs =>
      have prefixNormal :=
        firstFinalBandDerivesNormalizePrefix x xs final
      cases hs : firstOccurrenceSequence (x :: xs) with
      | nil =>
          simp [firstOccurrenceSequence] at hs
      | cons y ys =>
          rw [hs] at prefixNormal
          have trim :=
            firstFinalBandDerivesTrimPrefix (y :: ys) final
          have sourceEq :
              firstFinalWordOfCons x (xs ++ [final]) =
                wordOfPrefixFinal (x :: xs) final := by
            apply Word.toList_injective
            change
              x :: (xs ++ [final]) =
                (wordOfPrefixFinal (x :: xs) final).toList
            rw [toList_wordOfPrefixFinal]
            rfl
          have middleEq :
              firstFinalWordOfCons y (ys ++ [final]) =
                wordOfPrefixFinal (y :: ys) final := by
            apply Word.toList_injective
            change
              y :: (ys ++ [final]) =
                (wordOfPrefixFinal (y :: ys) final).toList
            rw [toList_wordOfPrefixFinal]
            rfl
          have normalEq :
              firstFinalBandNormalPrefix (x :: xs) final =
                firstFinalBandTrimPrefix (y :: ys) final := by
            simp [firstFinalBandNormalPrefix, hs]
          have result :
              Derives firstFinalBandBasis
                (wordOfPrefixFinal (x :: xs) final)
                (wordOfPrefixFinal
                  (firstFinalBandTrimPrefix (y :: ys) final)
                  final) :=
            Derives.trans
              (by simpa [sourceEq, middleEq] using prefixNormal)
              trim
          have normalized :
              Derives firstFinalBandBasis
                (wordOfPrefixFinal (x :: xs) final)
                (wordOfPrefixFinal
                  (firstFinalBandNormalPrefix (x :: xs) final)
                  final) := by
            simpa [normalEq] using result
          rw [reconstruct] at normalized
          exact normalized

/-- Exact zero-based multiplication for `S4_120`:
`[[1,1,1,1],[1,2,3,4],[1,2,3,4],[4,4,4,4]]`. -/
def firstFinalBandFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else if a = 3 then 3 else b

def firstFinalBandFour : FiniteTable where
  order := 4
  mul := firstFinalBandFourMul
  assoc := by decide

private theorem firstFinalBandFourMul_idempotent (a : Fin 4) :
    firstFinalBandFourMul a a = a := by
  decide +revert

private theorem firstFinalBandFourMul_return
    (a b c : Fin 4) :
    firstFinalBandFourMul
        (firstFinalBandFourMul a b) c =
      firstFinalBandFourMul
        (firstFinalBandFourMul
          (firstFinalBandFourMul a b) a) c := by
  decide +revert

theorem firstFinalBandBasis_models :
    Models firstFinalBandFour.semigroup firstFinalBandBasis := by
  intro e he
  simp only [firstFinalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      valuation 0 =
        firstFinalBandFourMul (valuation 0) (valuation 0)
    exact (firstFinalBandFourMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      firstFinalBandFourMul
          (firstFinalBandFourMul (valuation 0) (valuation 1))
          (valuation 2) =
        firstFinalBandFourMul
          (firstFinalBandFourMul
            (firstFinalBandFourMul
              (valuation 0) (valuation 1))
            (valuation 0))
          (valuation 2)
    exact firstFinalBandFourMul_return
      (valuation 0) (valuation 1) (valuation 2)

private def firstFinalBandFinalSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun x => if x = tested then 1 else 2

private theorem firstFinalBandFinalSeparator_mul
    (tested x y : Nat) :
    firstFinalBandFourMul
        (firstFinalBandFinalSeparator tested x)
        (firstFinalBandFinalSeparator tested y) =
      firstFinalBandFinalSeparator tested y := by
  by_cases hx : x = tested <;>
    by_cases hy : y = tested <;>
      simp [firstFinalBandFinalSeparator,
        firstFinalBandFourMul, hx, hy]

theorem firstFinalBandFinalSeparator_eval
    (tested : Nat) (pref : List Nat) (final : Nat) :
    firstFinalBandFour.semigroup.eval
        (firstFinalBandFinalSeparator tested)
        (wordOfPrefixFinal pref final) =
      firstFinalBandFinalSeparator tested final := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      exact firstFinalBandFinalSeparator_mul tested x final

private def firstFinalBandLrbListEval
    (valuation : Nat → Fin 3) (xs : List Nat) : Fin 3 :=
  xs.foldl
    (fun current x => leftRegularBandThreeMul current (valuation x)) 1

private theorem firstFinalBandLrbEval_eq_listEval
    (valuation : Nat → Fin 3) (w : Word Nat) :
    leftRegularBandThree.semigroup.eval valuation w =
      firstFinalBandLrbListEval valuation w.toList := by
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

private theorem firstFinalBandLrbFold_left_zero
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

private theorem firstFinalBandLrbListEval_cons_of_ne_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x ≠ 1) :
    firstFinalBandLrbListEval valuation (x :: xs) = valuation x := by
  unfold firstFinalBandLrbListEval
  simp only [List.foldl_cons]
  rw [show leftRegularBandThreeMul 1 (valuation x) = valuation x by
    simp [leftRegularBandThreeMul]]
  exact firstFinalBandLrbFold_left_zero valuation (valuation x) hx xs

private theorem firstFinalBandLrbListEval_cons_of_eq_one
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1) :
    firstFinalBandLrbListEval valuation (x :: xs) =
      firstFinalBandLrbListEval valuation xs := by
  simp [firstFinalBandLrbListEval, leftRegularBandThreeMul, hx]

private theorem firstFinalBandLrbFold_congr
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
      exact firstFinalBandLrbFold_congr v₁ v₂ xs
        (leftRegularBandThreeMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem firstFinalBandLrbListEval_congr
    (v₁ v₂ : Nat → Fin 3) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    firstFinalBandLrbListEval v₁ xs =
      firstFinalBandLrbListEval v₂ xs :=
  firstFinalBandLrbFold_congr v₁ v₂ xs 1 agree

private theorem firstFinalBandNodup_eq_of_lrbListEval_eq :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ valuation : Nat → Fin 3,
        firstFinalBandLrbListEval valuation xs =
          firstFinalBandLrbListEval valuation ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = y then 0 else 1
      have h := equalEval valuation
      have rightValue :
          firstFinalBandLrbListEval valuation (y :: ys) = 0 := by
        simpa [valuation] using
          firstFinalBandLrbListEval_cons_of_ne_one
            valuation y ys (by simp [valuation])
      have leftValue :
          firstFinalBandLrbListEval valuation [] = 1 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 3 :=
        fun z => if z = x then 0 else 1
      have h := equalEval valuation
      have leftValue :
          firstFinalBandLrbListEval valuation (x :: xs) = 0 := by
        simpa [valuation] using
          firstFinalBandLrbListEval_cons_of_ne_one
            valuation x xs (by simp [valuation])
      have rightValue :
          firstFinalBandLrbListEval valuation [] = 1 := rfl
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
            firstFinalBandLrbListEval valuation (x :: xs) = 0 := by
          simpa [valuation] using
            firstFinalBandLrbListEval_cons_of_ne_one
              valuation x xs (by simp [valuation])
        have rightValue :
            firstFinalBandLrbListEval valuation (y :: ys) = 2 := by
          simpa [valuation, Ne.symm hxy] using
            firstFinalBandLrbListEval_cons_of_ne_one
              valuation y ys (by simp [valuation, Ne.symm hxy])
        rw [leftValue, rightValue] at h
        exact (by decide : (0 : Fin 3) ≠ 2) h
      subst y
      have xNotMemXs : x ∉ xs := (List.nodup_cons.mp nodupX).1
      have xNotMemYs : x ∉ ys := (List.nodup_cons.mp nodupY).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 3,
            firstFinalBandLrbListEval valuation xs =
              firstFinalBandLrbListEval valuation ys := by
        intro valuation
        let masked : Nat → Fin 3 :=
          fun z => if z = x then 1 else valuation z
        have fullEqual := equalEval masked
        have maskedX : masked x = 1 := by simp [masked]
        rw [firstFinalBandLrbListEval_cons_of_eq_one
              masked x xs maskedX,
          firstFinalBandLrbListEval_cons_of_eq_one
              masked x ys maskedX] at fullEqual
        calc
          firstFinalBandLrbListEval valuation xs =
              firstFinalBandLrbListEval masked xs := by
                apply firstFinalBandLrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemXs
                  simpa [h] using hz
                simp [masked, hzx]
          _ = firstFinalBandLrbListEval masked ys := fullEqual
          _ = firstFinalBandLrbListEval valuation ys := by
                apply firstFinalBandLrbListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemYs
                  simpa [h] using hz
                simp [masked, hzx]
      congr 1
      exact firstFinalBandNodup_eq_of_lrbListEval_eq
        (List.nodup_cons.mp nodupX).2
        (List.nodup_cons.mp nodupY).2 tailsEqual

private theorem firstFinalBandLrbValid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy leftRegularBandThree.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList := by
  have lhsNormal := lrbDerivesNormal e.lhs
  have rhsNormal := lrbDerivesNormal e.rhs
  cases hl : firstOccurrenceSequence e.lhs.toList with
  | nil =>
      cases e.lhs with
      | mk head tail =>
          simp [Word.toList, firstOccurrenceSequence] at hl
  | cons x xs =>
      cases hr : firstOccurrenceSequence e.rhs.toList with
      | nil =>
          cases e.rhs with
          | mk head tail =>
              simp [Word.toList, firstOccurrenceSequence] at hr
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 3,
                firstFinalBandLrbListEval valuation (x :: xs) =
                  firstFinalBandLrbListEval valuation (y :: ys) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound leftRegularBandThreeBasis_models valuation
            have rhsSound :=
              rhsNormal.sound leftRegularBandThreeBasis_models valuation
            rw [firstFinalBandLrbEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have lhsNodup : (x :: xs).Nodup := by
            rw [← hl]
            exact firstOccurrenceSequence_nodup e.lhs.toList
          have rhsNodup : (y :: ys).Nodup := by
            rw [← hr]
            exact firstOccurrenceSequence_nodup e.rhs.toList
          have reducedEqual : x :: xs = y :: ys :=
            firstFinalBandNodup_eq_of_lrbListEval_eq
              lhsNodup rhsNodup reducedEvalEqual
          simpa [hl, hr] using reducedEqual

private def firstFinalBandEmbedLrb (a : Fin 3) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 1 else 3

private theorem firstFinalBandEmbedLrb_injective
    (a b : Fin 3)
    (h : firstFinalBandEmbedLrb a = firstFinalBandEmbedLrb b) :
    a = b := by
  decide +revert

private theorem firstFinalBandEmbedLrb_mul (a b : Fin 3) :
    firstFinalBandFourMul
        (firstFinalBandEmbedLrb a)
        (firstFinalBandEmbedLrb b) =
      firstFinalBandEmbedLrb (leftRegularBandThreeMul a b) := by
  decide +revert

private theorem firstFinalBandEmbedLrb_fold
    (valuation : Nat → Fin 3) :
    ∀ (xs : List Nat) (a : Fin 3),
      xs.foldl
          (fun current x =>
            firstFinalBandFourMul current
              (firstFinalBandEmbedLrb (valuation x)))
          (firstFinalBandEmbedLrb a) =
        firstFinalBandEmbedLrb
          (xs.foldl
            (fun current x =>
              leftRegularBandThreeMul current (valuation x)) a)
  | [], _ => rfl
  | x :: xs, a => by
      simp only [List.foldl_cons]
      rw [firstFinalBandEmbedLrb_mul]
      exact firstFinalBandEmbedLrb_fold valuation xs
        (leftRegularBandThreeMul a (valuation x))

private theorem firstFinalBandEmbedLrb_eval
    (valuation : Nat → Fin 3) (w : Word Nat) :
    firstFinalBandFour.semigroup.eval
        (fun x => firstFinalBandEmbedLrb (valuation x)) w =
      firstFinalBandEmbedLrb
        (leftRegularBandThree.semigroup.eval valuation w) := by
  cases w with
  | mk head tail =>
      exact firstFinalBandEmbedLrb_fold valuation tail
        (valuation head)

private theorem firstFinalBandValid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy firstFinalBandFour.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList := by
  apply firstFinalBandLrbValid_firstOccurrenceSequence_eq e
  intro valuation
  have h :=
    valid (fun x => firstFinalBandEmbedLrb (valuation x))
  rw [firstFinalBandEmbedLrb_eval,
    firstFinalBandEmbedLrb_eval] at h
  exact firstFinalBandEmbedLrb_injective _ _ h

private theorem firstOccurrenceSequence_append_final_of_nodup :
    ∀ (xs : List Nat) (final : Nat), xs.Nodup →
      firstOccurrenceSequence (xs ++ [final]) =
        if final ∈ xs then xs else xs ++ [final]
  | [], final, _ => by
      simp [firstOccurrenceSequence]
  | x :: xs, final, hnodup => by
      have hx : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have ih :=
        firstOccurrenceSequence_append_final_of_nodup
          xs final hxs
      by_cases hfx : final = x
      · subst final
        have filterTail :
            (xs ++ [x]).filter (fun y => decide (y ≠ x)) = xs := by
          rw [List.filter_append]
          have keepXs :
              xs.filter (fun y => decide (y ≠ x)) = xs := by
            apply List.filter_eq_self.2
            intro y hy
            simp
            intro hyx
            apply hx
            simpa [hyx] using hy
          rw [keepXs]
          simp
        rw [firstOccurrenceSequence.eq_def]
        change
          x ::
              (firstOccurrenceSequence (xs ++ [x])).filter
                (fun y => decide (y ≠ x)) =
            if x ∈ x :: xs then x :: xs else x :: xs ++ [x]
        rw [ih, if_neg hx]
        simp only [List.mem_cons, true_or, if_true]
        exact congrArg (List.cons x) filterTail
      · rw [firstOccurrenceSequence.eq_def]
        change
          x ::
              (firstOccurrenceSequence
                (xs ++ [final])).filter
                (fun y => decide (y ≠ x)) =
            if final ∈ x :: xs then
              x :: xs
            else
              x :: xs ++ [final]
        rw [ih]
        by_cases hf : final ∈ xs
        · have keepXs :
              xs.filter (fun y => decide (y ≠ x)) = xs := by
            apply List.filter_eq_self.2
            intro y hy
            simp
            intro hyx
            apply hx
            simpa [hyx] using hy
          have hfull : final ∈ x :: xs := by
            exact List.Mem.tail x hf
          rw [if_pos hf, if_pos hfull, keepXs]
        · have keepXs :
              xs.filter (fun y => decide (y ≠ x)) = xs := by
            apply List.filter_eq_self.2
            intro y hy
            simp
            intro hyx
            apply hx
            simpa [hyx] using hy
          have hfull : final ∉ x :: xs := by
            simp [hfx, hf]
          rw [if_neg hf, if_neg hfull]
          rw [List.filter_append, keepXs]
          simp [hfx]

private theorem firstFinalBandTrim_occurrence_key
    (pref : List Nat) (final : Nat)
    (hnodup : pref.Nodup)
    (hfixed :
      firstFinalBandTrimPrefix pref final = pref) :
    firstFinalBandTrimPrefix
        (firstOccurrenceSequence (pref ++ [final])) final =
      pref := by
  rw [firstOccurrenceSequence_append_final_of_nodup
    pref final hnodup]
  by_cases hf : final ∈ pref
  · simpa [hf] using hfixed
  · simp [hf, firstFinalBandTrimPrefix_append_final]

private theorem firstFinalBandNormalized_eq_of_eval_eq
    (prefix₁ prefix₂ : List Nat) (final₁ final₂ : Nat)
    (nodup₁ : prefix₁.Nodup) (nodup₂ : prefix₂.Nodup)
    (fixed₁ :
      firstFinalBandTrimPrefix prefix₁ final₁ = prefix₁)
    (fixed₂ :
      firstFinalBandTrimPrefix prefix₂ final₂ = prefix₂)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        firstFinalBandFour.semigroup.eval valuation
            (wordOfPrefixFinal prefix₁ final₁) =
          firstFinalBandFour.semigroup.eval valuation
            (wordOfPrefixFinal prefix₂ final₂)) :
    wordOfPrefixFinal prefix₁ final₁ =
      wordOfPrefixFinal prefix₂ final₂ := by
  have finals : final₁ = final₂ := by
    have h := equalEval
      (firstFinalBandFinalSeparator final₁)
    rw [firstFinalBandFinalSeparator_eval,
      firstFinalBandFinalSeparator_eval] at h
    apply Decidable.byContradiction
    intro hne
    simp [firstFinalBandFinalSeparator, Ne.symm hne] at h
  subst final₂
  let normalizedIdentity : Identity Nat :=
    ⟨wordOfPrefixFinal prefix₁ final₁,
      wordOfPrefixFinal prefix₂ final₁⟩
  have sequenceEqual :
      firstOccurrenceSequence
          (wordOfPrefixFinal prefix₁ final₁).toList =
        firstOccurrenceSequence
          (wordOfPrefixFinal prefix₂ final₁).toList := by
    apply firstFinalBandValid_firstOccurrenceSequence_eq
      normalizedIdentity
    exact equalEval
  rw [toList_wordOfPrefixFinal,
    toList_wordOfPrefixFinal] at sequenceEqual
  have prefixes :
      prefix₁ = prefix₂ := by
    calc
      prefix₁ =
          firstFinalBandTrimPrefix
            (firstOccurrenceSequence
              (prefix₁ ++ [final₁])) final₁ := by
            symm
            exact firstFinalBandTrim_occurrence_key
              prefix₁ final₁ nodup₁ fixed₁
      _ = firstFinalBandTrimPrefix
            (firstOccurrenceSequence
              (prefix₂ ++ [final₁])) final₁ := by
            rw [sequenceEqual]
      _ = prefix₂ :=
            firstFinalBandTrim_occurrence_key
              prefix₂ final₁ nodup₂ fixed₂
  rw [prefixes]

theorem firstFinalBandBasis_complete :
    BasisFor firstFinalBandFour.semigroup
      firstFinalBandBasis := by
  refine ⟨firstFinalBandBasis_models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  let lhsPrefix :=
    firstFinalBandNormalPrefix lhsSplit.1 lhsSplit.2
  let rhsPrefix :=
    firstFinalBandNormalPrefix rhsSplit.1 rhsSplit.2
  have lhsNormal := firstFinalBandDerivesNormal e.lhs
  have rhsNormal := firstFinalBandDerivesNormal e.rhs
  change
    Derives firstFinalBandBasis e.lhs
      (wordOfPrefixFinal lhsPrefix lhsSplit.2) at lhsNormal
  change
    Derives firstFinalBandBasis e.rhs
      (wordOfPrefixFinal rhsPrefix rhsSplit.2) at rhsNormal
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        firstFinalBandFour.semigroup.eval valuation
            (wordOfPrefixFinal lhsPrefix lhsSplit.2) =
          firstFinalBandFour.semigroup.eval valuation
            (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound firstFinalBandBasis_models valuation
    have rhsSound :=
      rhsNormal.sound firstFinalBandBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have normalWordsEqual :=
    firstFinalBandNormalized_eq_of_eval_eq
      lhsPrefix rhsPrefix lhsSplit.2 rhsSplit.2
      (firstFinalBandNormalPrefix_nodup
        lhsSplit.1 lhsSplit.2)
      (firstFinalBandNormalPrefix_nodup
        rhsSplit.1 rhsSplit.2)
      (firstFinalBandNormalPrefix_fixed
        lhsSplit.1 lhsSplit.2)
      (firstFinalBandNormalPrefix_fixed
        rhsSplit.1 rhsSplit.2)
      normalizedEval
  rw [normalWordsEqual] at lhsNormal
  exact Derives.trans lhsNormal (Derives.symm rhsNormal)

def firstFinalBandOppositeBasis : List (Identity Nat) :=
  reversedBasis firstFinalBandBasis

theorem firstFinalBandOppositeBasis_complete :
    BasisFor firstFinalBandFour.semigroup.opposite
      firstFinalBandOppositeBasis := by
  simpa [firstFinalBandOppositeBasis] using
    firstFinalBandBasis_complete.oppositeReversed

end SemigroupBasis.Examples

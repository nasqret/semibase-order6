import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,3,4],[4,4,4,4]]`. -/
def firstOccurrenceFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then
        (if b = 2 then 2 else if b = 3 then 3 else 0)
      else 3

/-- The root catalogue representative `S4_59`. -/
def firstOccurrenceFour : FiniteTable where
  order := 4
  mul := firstOccurrenceFourMul
  assoc := by decide

def firstOccurrenceXX : Word Nat := ⟨0, [0]⟩
def firstOccurrenceXXX : Word Nat := ⟨0, [0, 0]⟩
def firstOccurrenceXY : Word Nat := ⟨0, [1]⟩
def firstOccurrenceXXY : Word Nat := ⟨0, [0, 1]⟩
def firstOccurrenceXYX : Word Nat := ⟨0, [1, 0]⟩

def firstOccurrencePowerLaw : Identity Nat :=
  ⟨firstOccurrenceXX, firstOccurrenceXXX⟩

def firstOccurrenceLeftDuplicationLaw : Identity Nat :=
  ⟨firstOccurrenceXY, firstOccurrenceXXY⟩

def firstOccurrenceReturnDuplicationLaw : Identity Nat :=
  ⟨firstOccurrenceXY, firstOccurrenceXYX⟩

/-- The exact basis `xx = xxx`, `xy = xxy`, `xy = xyx`. -/
def firstOccurrenceFourBasis : List (Identity Nat) :=
  [firstOccurrencePowerLaw, firstOccurrenceLeftDuplicationLaw,
    firstOccurrenceReturnDuplicationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem firstOccurrenceDerivesPowerContraction (u : Word Nat) :
    Derives firstOccurrenceFourBasis ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives firstOccurrenceFourBasis
        firstOccurrenceXXX firstOccurrenceXX :=
    Derives.symm <|
      Derives.fromBasis (e := firstOccurrencePowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [firstOccurrenceFourBasis, firstOccurrencePowerLaw,
    firstOccurrenceXXX, firstOccurrenceXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem firstOccurrenceDerivesLeftContraction (u v : Word Nat) :
    Derives firstOccurrenceFourBasis ((u ++ u) ++ v) (u ++ v) := by
  have hbase :
      Derives firstOccurrenceFourBasis
        firstOccurrenceXXY firstOccurrenceXY :=
    Derives.symm <|
      Derives.fromBasis (e := firstOccurrenceLeftDuplicationLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [firstOccurrenceFourBasis, firstOccurrenceLeftDuplicationLaw,
    firstOccurrenceXXY, firstOccurrenceXY, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem firstOccurrenceDerivesReturnContraction (u v : Word Nat) :
    Derives firstOccurrenceFourBasis ((u ++ v) ++ u) (u ++ v) := by
  have hbase :
      Derives firstOccurrenceFourBasis
        firstOccurrenceXYX firstOccurrenceXY :=
    Derives.symm <|
      Derives.fromBasis (e := firstOccurrenceReturnDuplicationLaw) <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [firstOccurrenceFourBasis, firstOccurrenceReturnDuplicationLaw,
    firstOccurrenceXYX, firstOccurrenceXY, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem firstOccurrenceDerivesRightContraction (u v : Word Nat) :
    Derives firstOccurrenceFourBasis (u ++ (v ++ v)) (u ++ v) := by
  have first :=
    Derives.symm (firstOccurrenceDerivesReturnContraction u v)
  have second :=
    Derives.prepend u <| Derives.symm
      (firstOccurrenceDerivesLeftContraction v u)
  have third :=
    firstOccurrenceDerivesReturnContraction u (v ++ v)
  exact Derives.symm <|
    Derives.trans first <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using third)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Delete one later copy of the initial letter when a nonempty word precedes
the displayed block. -/
private theorem firstOccurrenceDerivesDeleteOnePrefixed
    (p : Word Nat) (x : Nat) (middle suffix : List Nat) :
    Derives firstOccurrenceFourBasis
      (p ++ wordOfCons x (middle ++ x :: suffix))
      (p ++ wordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              firstOccurrenceDerivesRightContraction
                p (Word.singleton x)
      | cons y ys =>
          have h :=
            Derives.prepend p <|
              firstOccurrenceDerivesLeftContraction
                (Word.singleton x) (wordOfCons y ys)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
  | cons y ys =>
      have core :=
        firstOccurrenceDerivesReturnContraction
          (Word.singleton x) (wordOfCons y ys)
      cases suffix with
      | nil =>
          have h := Derives.prepend p core
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
      | cons z zs =>
          have h := Derives.prepend p <|
            Derives.appendRight core (wordOfCons z zs)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h

private theorem firstOccurrenceDerivesDeleteAfterPrefixed :
    ∀ (p : Word Nat) (x : Nat) (middle rest : List Nat),
      Derives firstOccurrenceFourBasis
        (p ++ wordOfCons x (middle ++ rest))
        (p ++ wordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x))))
  | p, x, middle, [] => by
      simpa using Derives.refl (p ++ wordOfCons x middle)
  | p, x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        have first :=
          firstOccurrenceDerivesDeleteOnePrefixed p x middle ys
        have remaining :=
          firstOccurrenceDerivesDeleteAfterPrefixed p x middle ys
        exact Derives.trans first <| by simpa using remaining
      · have remaining :=
          firstOccurrenceDerivesDeleteAfterPrefixed
            p x (middle ++ [y]) ys
        simpa [hy, List.append_assoc] using remaining

/-- Under a nonempty prefix, a word reduces to its duplicate-free sequence of
first occurrences. -/
private theorem firstOccurrenceDerivesPrefixedNormalizeList :
    ∀ (p : Word Nat) (x : Nat) (xs : List Nat),
      match firstOccurrenceSequence (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives firstOccurrenceFourBasis
            (p ++ wordOfCons x xs) (p ++ wordOfCons y ys)
  | p, x, [] => by
      exact Derives.refl _
  | p, x, y :: ys => by
      have suffixNormal :=
        firstOccurrenceDerivesPrefixedNormalizeList
          (p ++ Word.singleton x) y ys
      cases hs : firstOccurrenceSequence (y :: ys) with
      | nil =>
          simp [firstOccurrenceSequence] at hs
      | cons z zs =>
          rw [hs] at suffixNormal
          have deleted :=
            firstOccurrenceDerivesDeleteAfterPrefixed p x [] (z :: zs)
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
                Word.append_assoc] using suffixNormal)
            (by simpa [wordOfCons, Word.append_assoc] using deleted)
termination_by
  _ _ xs => xs.length

/-- Remove all later copies of the first letter once a different second
letter is fixed. -/
private theorem firstOccurrenceDerivesDeleteOneNonempty
    (x : Nat) (middle suffix : List Nat) (hmiddle : middle ≠ []) :
    Derives firstOccurrenceFourBasis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil => exact False.elim (hmiddle rfl)
  | cons y ys =>
      have core :=
        firstOccurrenceDerivesReturnContraction
          (Word.singleton x) (wordOfCons y ys)
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using core
      | cons q qs =>
          have h := Derives.appendRight core (wordOfCons q qs)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h

private theorem firstOccurrenceDerivesDeleteAfterNonemptyAux :
    ∀ (x : Nat) (middle rest : List Nat), middle ≠ [] →
      Derives firstOccurrenceFourBasis
        (wordOfCons x (middle ++ rest))
        (wordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x))))
  | x, middle, [], _ => by
      simpa using Derives.refl (wordOfCons x middle)
  | x, middle, y :: ys, hmiddle => by
      by_cases hy : y = x
      · subst y
        exact Derives.trans
          (firstOccurrenceDerivesDeleteOneNonempty
            x middle ys hmiddle) <| by
              simpa using
                firstOccurrenceDerivesDeleteAfterNonemptyAux
                  x middle ys hmiddle
      · have remaining :=
          firstOccurrenceDerivesDeleteAfterNonemptyAux
            x (middle ++ [y]) ys (by simp)
        simpa [hy, List.append_assoc] using remaining

private theorem firstOccurrenceDerivesDeleteAfterNonempty
    (x z : Nat) (zs : List Nat) (_hz : z ≠ x) :
    Derives firstOccurrenceFourBasis
      (wordOfCons x (z :: zs))
      (wordOfCons x
        (z :: zs.filter (fun y => decide (y ≠ x)))) := by
  simpa using
    firstOccurrenceDerivesDeleteAfterNonemptyAux
      x [z] zs (by simp)

/-- Singleton words remain projections. Longer words retain the sequence of
first occurrences; a unary sequence is represented by `xx`. -/
def firstOccurrenceLongNormalList : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: ys =>
      match firstOccurrenceSequence (x :: y :: ys) with
      | [z] => [z, z]
      | zs => zs

private theorem firstOccurrenceSequence_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    firstOccurrenceSequence (x :: xs) ≠ [] := by
  simp [firstOccurrenceSequence]

theorem firstOccurrenceDerivesNormal (w : Word Nat) :
    match firstOccurrenceLongNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives firstOccurrenceFourBasis w (wordOfCons x xs) := by
  cases w with
  | mk x tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons y ys =>
          change
            match firstOccurrenceLongNormalList (x :: y :: ys) with
            | [] => False
            | z :: zs =>
                Derives firstOccurrenceFourBasis
                  (wordOfCons x (y :: ys)) (wordOfCons z zs)
          have suffixNormal :=
            firstOccurrenceDerivesPrefixedNormalizeList
              (Word.singleton x) y ys
          cases hs : firstOccurrenceSequence (y :: ys) with
          | nil =>
              exact False.elim
                (firstOccurrenceSequence_cons_ne_nil y ys hs)
          | cons z zs =>
              rw [hs] at suffixNormal
              have suffixNodup : (z :: zs).Nodup := by
                rw [← hs]
                exact firstOccurrenceSequence_nodup (y :: ys)
              have whole :
                  firstOccurrenceSequence (x :: y :: ys) =
                    x :: (z :: zs).filter
                      (fun a => decide (a ≠ x)) := by
                change
                  x :: (firstOccurrenceSequence (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                    x :: (z :: zs).filter
                      (fun a => decide (a ≠ x))
                rw [hs]
              by_cases hz : z = x
              · subst z
                have hx : x ∉ zs :=
                  (List.nodup_cons.mp suffixNodup).1
                cases zs with
                | nil =>
                    have normalEq :
                        firstOccurrenceLongNormalList (x :: y :: ys) =
                          [x, x] := by
                      simp [firstOccurrenceLongNormalList, whole]
                    rw [normalEq]
                    simpa [wordOfCons, Word.append, Word.singleton] using
                      suffixNormal
                | cons q qs =>
                    have hfilter :
                        (q :: qs).filter
                            (fun a => decide (a ≠ x)) =
                          q :: qs := by
                      apply List.filter_eq_self.2
                      intro a ha
                      simp
                      intro hax
                      apply hx
                      simpa [hax] using ha
                    have normalEq :
                        firstOccurrenceLongNormalList (x :: y :: ys) =
                          x :: q :: qs := by
                      have hwholeFilter :
                          (x :: q :: qs).filter
                              (fun a => decide (a ≠ x)) =
                            q :: qs := by
                        rw [List.filter_cons]
                        rw [show decide (x ≠ x) = false by simp]
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact hfilter
                      rw [firstOccurrenceLongNormalList, whole,
                        hwholeFilter]
                    have contracted :=
                      firstOccurrenceDerivesLeftContraction
                        (Word.singleton x) (wordOfCons q qs)
                    rw [normalEq]
                    exact Derives.trans suffixNormal <| by
                      simpa [wordOfCons, Word.append, Word.singleton,
                        Word.append_assoc]
                        using contracted
              · have deleted :=
                  firstOccurrenceDerivesDeleteAfterNonempty x z zs hz
                have normalEq :
                    firstOccurrenceLongNormalList (x :: y :: ys) =
                      x :: z ::
                        zs.filter (fun a => decide (a ≠ x)) := by
                  simp [firstOccurrenceLongNormalList, whole, hz]
                rw [normalEq]
                exact Derives.trans suffixNormal <| by
                  simpa [wordOfCons, Word.append, Word.singleton,
                    Word.append_assoc]
                    using deleted

private theorem firstOccurrenceMul_power (a : Fin 4) :
    firstOccurrenceFourMul a a =
      firstOccurrenceFourMul (firstOccurrenceFourMul a a) a := by
  decide +revert

private theorem firstOccurrenceMul_left_duplication (a b : Fin 4) :
    firstOccurrenceFourMul a b =
      firstOccurrenceFourMul
        (firstOccurrenceFourMul a a) b := by
  decide +revert

private theorem firstOccurrenceMul_return_duplication (a b : Fin 4) :
    firstOccurrenceFourMul a b =
      firstOccurrenceFourMul
        (firstOccurrenceFourMul a b) a := by
  decide +revert

theorem firstOccurrenceFourBasis_models :
    Models firstOccurrenceFour.semigroup firstOccurrenceFourBasis := by
  intro e he
  simp only [firstOccurrenceFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      firstOccurrenceFourMul (valuation 0) (valuation 0) =
        firstOccurrenceFourMul
          (firstOccurrenceFourMul (valuation 0) (valuation 0))
          (valuation 0)
    exact firstOccurrenceMul_power (valuation 0)
  · intro valuation
    change
      firstOccurrenceFourMul (valuation 0) (valuation 1) =
        firstOccurrenceFourMul
          (firstOccurrenceFourMul (valuation 0) (valuation 0))
          (valuation 1)
    exact firstOccurrenceMul_left_duplication
      (valuation 0) (valuation 1)
  · intro valuation
    change
      firstOccurrenceFourMul (valuation 0) (valuation 1) =
        firstOccurrenceFourMul
          (firstOccurrenceFourMul (valuation 0) (valuation 1))
          (valuation 0)
    exact firstOccurrenceMul_return_duplication
      (valuation 0) (valuation 1)

private theorem firstOccurrenceFold_zero
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x => firstOccurrenceFourMul current (valuation x))
        (0 : Fin 4) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show firstOccurrenceFourMul 0 (valuation x) = (0 : Fin 4) by
        simp [firstOccurrenceFourMul]]
      exact ih

/-- The constant value `1` separates singleton projections from every longer
word. -/
theorem firstOccurrenceFourSingletonSeparator (w : Word Nat) :
    firstOccurrenceFour.semigroup.eval (fun _ => (1 : Fin 4)) w =
        (1 : Fin 4) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ => firstOccurrenceFourMul current (1 : Fin 4))
            (1 : Fin 4) = 1 ↔
          tail = []
      cases tail with
      | nil => simp
      | cons x xs =>
          simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
          rw [show firstOccurrenceFourMul 1 1 = (0 : Fin 4) by decide]
          rw [firstOccurrenceFold_zero]
          decide

private def bandListEval (valuation : Nat → Fin 4)
    (xs : List Nat) : Fin 4 :=
  xs.foldl
    (fun current x => firstOccurrenceFourMul current (valuation x)) 2

private theorem firstOccurrenceMul_two_of_ne_one (a : Fin 4)
    (h : a ≠ 1) :
    firstOccurrenceFourMul 2 a = a := by
  decide +revert

private theorem firstOccurrenceMul_idempotent_of_ne_one (a : Fin 4)
    (h : a ≠ 1) :
    firstOccurrenceFourMul a a = a := by
  decide +revert

private theorem eval_eq_bandListEval
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ x, valuation x ≠ 1) (w : Word Nat) :
    firstOccurrenceFour.semigroup.eval valuation w =
      bandListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              firstOccurrenceFourMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              firstOccurrenceFourMul current (valuation x))
            (firstOccurrenceFourMul 2 (valuation head))
      rw [show firstOccurrenceFourMul 2 (valuation head) =
          valuation head by
        exact firstOccurrenceMul_two_of_ne_one
          (valuation head) (avoidsOne head)]

private theorem bandFold_left_zero
    (valuation : Nat → Fin 4) (a : Fin 4)
    (ha0 : a = 0 ∨ a = 3) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          firstOccurrenceFourMul current (valuation x)) a = a := by
  rcases ha0 with rfl | rfl
  · exact firstOccurrenceFold_zero valuation xs
  · induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl_cons]
        rw [show firstOccurrenceFourMul 3 (valuation x) = (3 : Fin 4) by
          simp [firstOccurrenceFourMul]]
        exact ih

private theorem bandListEval_cons_of_left_zero
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 0 ∨ valuation x = 3) :
    bandListEval valuation (x :: xs) = valuation x := by
  unfold bandListEval
  simp only [List.foldl_cons]
  rw [show firstOccurrenceFourMul 2 (valuation x) = valuation x by
    rcases hx with hx | hx <;> simp [firstOccurrenceFourMul, hx]]
  exact bandFold_left_zero valuation (valuation x) hx xs

private theorem bandListEval_cons_of_two
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 2) :
    bandListEval valuation (x :: xs) =
      bandListEval valuation xs := by
  simp [bandListEval, firstOccurrenceFourMul, hx]

private theorem bandFold_congr
    (v₁ v₂ : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            firstOccurrenceFourMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            firstOccurrenceFourMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact bandFold_congr v₁ v₂ xs
        (firstOccurrenceFourMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem bandListEval_congr
    (v₁ v₂ : Nat → Fin 4) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    bandListEval v₁ xs = bandListEval v₂ xs :=
  bandFold_congr v₁ v₂ xs 2 agree

private theorem nodup_eq_of_bandListEval_eq :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ valuation : Nat → Fin 4,
        (∀ z, valuation z ≠ 1) →
        bandListEval valuation xs = bandListEval valuation ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = y then 0 else 2
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases hz : z = y <;> simp [valuation, hz]
      have h := equalEval valuation avoids
      have hy0 : valuation y = 0 := by simp [valuation]
      have rightValue :
          bandListEval valuation (y :: ys) = 0 := by
        simpa [hy0] using
          bandListEval_cons_of_left_zero valuation y ys (Or.inl hy0)
      have leftValue : bandListEval valuation [] = 2 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = x then 0 else 2
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases hz : z = x <;> simp [valuation, hz]
      have h := equalEval valuation avoids
      have hx0 : valuation x = 0 := by simp [valuation]
      have leftValue :
          bandListEval valuation (x :: xs) = 0 := by
        simpa [hx0] using
          bandListEval_cons_of_left_zero valuation x xs (Or.inl hx0)
      have rightValue : bandListEval valuation [] = 2 := rfl
      rw [leftValue, rightValue] at h
      exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
  | x :: xs, y :: ys, nodupX, nodupY, equalEval => by
      have heads : x = y := by
        apply Decidable.byContradiction
        intro hxy
        let valuation : Nat → Fin 4 :=
          fun z => if z = x then 0 else if z = y then 3 else 2
        have avoids : ∀ z, valuation z ≠ 1 := by
          intro z
          by_cases hzx : z = x
          · simp [valuation, hzx]
          · by_cases hzy : z = y
            · subst z
              simp [valuation, Ne.symm hxy]
            · simp [valuation, hzx, hzy]
        have h := equalEval valuation avoids
        have hx0 : valuation x = 0 := by simp [valuation]
        have hy3 : valuation y = 3 := by
          simp [valuation, Ne.symm hxy]
        have leftValue :
            bandListEval valuation (x :: xs) = 0 := by
          simpa [hx0] using
            bandListEval_cons_of_left_zero valuation x xs (Or.inl hx0)
        have rightValue :
            bandListEval valuation (y :: ys) = 3 := by
          simpa [hy3] using
            bandListEval_cons_of_left_zero valuation y ys (Or.inr hy3)
        rw [leftValue, rightValue] at h
        exact (by decide : (0 : Fin 4) ≠ 3) h
      subst y
      have xNotMemXs : x ∉ xs := (List.nodup_cons.mp nodupX).1
      have xNotMemYs : x ∉ ys := (List.nodup_cons.mp nodupY).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 4,
            (∀ z, valuation z ≠ 1) →
            bandListEval valuation xs =
              bandListEval valuation ys := by
        intro valuation avoidsOne
        let masked : Nat → Fin 4 :=
          fun z => if z = x then 2 else valuation z
        have maskedAvoids : ∀ z, masked z ≠ 1 := by
          intro z
          by_cases hzx : z = x
          · simp [masked, hzx]
          · simp [masked, hzx, avoidsOne z]
        have fullEqual := equalEval masked maskedAvoids
        have maskedX : masked x = 2 := by simp [masked]
        rw [bandListEval_cons_of_two masked x xs maskedX,
          bandListEval_cons_of_two masked x ys maskedX] at fullEqual
        calc
          bandListEval valuation xs =
              bandListEval masked xs := by
                apply bandListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemXs
                  simpa [h] using hz
                simp [masked, hzx]
          _ = bandListEval masked ys := fullEqual
          _ = bandListEval valuation ys := by
                apply bandListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemYs
                  simpa [h] using hz
                simp [masked, hzx]
      congr 1
      exact nodup_eq_of_bandListEval_eq
        (List.nodup_cons.mp nodupX).2
        (List.nodup_cons.mp nodupY).2 tailsEqual

private def occurrenceKey : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: ys => firstOccurrenceSequence (x :: y :: ys)

private def encodeLongOccurrenceKey : List Nat → List Nat
  | [x] => [x, x]
  | xs => xs

private theorem occurrenceKey_nodup (xs : List Nat) :
    (occurrenceKey xs).Nodup := by
  cases xs with
  | nil => simp [occurrenceKey]
  | cons x xs =>
      cases xs with
      | nil => simp [occurrenceKey]
      | cons y ys =>
          simpa [occurrenceKey] using
            firstOccurrenceSequence_nodup (x :: y :: ys)

private theorem firstOccurrenceSequence_eq_self_of_nodup_explicit
    (xs : List Nat) (h : xs.Nodup) :
    firstOccurrenceSequence xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp h).1
      have hxs : xs.Nodup := (List.nodup_cons.mp h).2
      rw [firstOccurrenceSequence, ih hxs]
      congr 1
      exact List.filter_eq_self.2 fun y hy => by
        simp
        intro hyx
        apply hx
        simpa [hyx] using hy

private theorem occurrenceKey_encodeLong_of_nodup
    (xs : List Nat) (h : xs.Nodup) :
    occurrenceKey (encodeLongOccurrenceKey xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil =>
          simp [encodeLongOccurrenceKey, occurrenceKey,
            firstOccurrenceSequence]
      | cons y ys =>
          simpa [encodeLongOccurrenceKey, occurrenceKey] using
            firstOccurrenceSequence_eq_self_of_nodup_explicit
              (x :: y :: ys) h

private theorem firstOccurrenceLongNormal_eq_encode
    (xs : List Nat) (hlong : xs.length ≠ 1) :
    firstOccurrenceLongNormalList xs =
      encodeLongOccurrenceKey (occurrenceKey xs) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => simp at hlong
      | cons y ys => rfl

private theorem bandListEval_encodeLongOccurrenceKey
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) (xs : List Nat) :
    bandListEval valuation (encodeLongOccurrenceKey xs) =
      bandListEval valuation xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [encodeLongOccurrenceKey, bandListEval,
            List.foldl_cons, List.foldl_nil]
          rw [firstOccurrenceMul_two_of_ne_one
            (valuation x) (avoidsOne x)]
          exact firstOccurrenceMul_idempotent_of_ne_one
            (valuation x) (avoidsOne x)
      | cons y ys => rfl

private theorem firstOccurrenceLongNormalList_ne_nil (w : Word Nat) :
    firstOccurrenceLongNormalList w.toList ≠ [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList, firstOccurrenceLongNormalList]
      | cons next rest =>
          simp only [Word.toList, firstOccurrenceLongNormalList]
          cases h :
              firstOccurrenceSequence (head :: next :: rest) with
          | nil =>
              exact False.elim <|
                firstOccurrenceSequence_cons_ne_nil head
                  (next :: rest) h
          | cons x xs =>
              cases xs <;> simp

private theorem word_eq_singleton_of_tail_eq (w : Word Nat)
    (h : w.tail = []) :
    w = Word.singleton w.head := by
  cases w
  simp_all [Word.singleton]

private theorem word_toList_length_ne_one_of_tail_ne_nil
    (w : Word Nat) (h : w.tail ≠ []) :
    w.toList.length ≠ 1 := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => exact False.elim (h rfl)
      | cons next rest => simp [Word.toList]

theorem firstOccurrenceFourBasis_complete :
    BasisFor firstOccurrenceFour.semigroup
      firstOccurrenceFourBasis := by
  refine ⟨firstOccurrenceFourBasis_models, ?_⟩
  intro e valid
  have singletonIff : e.lhs.tail = [] ↔ e.rhs.tail = [] := by
    have evaluated := valid (fun _ => (1 : Fin 4))
    constructor
    · intro hl
      apply (firstOccurrenceFourSingletonSeparator e.rhs).1
      exact evaluated.symm.trans <|
        (firstOccurrenceFourSingletonSeparator e.lhs).2 hl
    · intro hr
      apply (firstOccurrenceFourSingletonSeparator e.lhs).1
      exact evaluated.trans <|
        (firstOccurrenceFourSingletonSeparator e.rhs).2 hr
  by_cases lhsSingleton : e.lhs.tail = []
  · have rhsSingleton := singletonIff.mp lhsSingleton
    have heads : e.lhs.head = e.rhs.head := by
      let valuation : Nat → Fin 4 :=
        fun z => if z = e.lhs.head then 0 else 3
      have evaluated := valid valuation
      have lhsEq :=
        word_eq_singleton_of_tail_eq e.lhs lhsSingleton
      have rhsEq :=
        word_eq_singleton_of_tail_eq e.rhs rhsSingleton
      rw [lhsEq, rhsEq] at evaluated
      simp only [Semigroup.eval_singleton] at evaluated
      apply Decidable.byContradiction
      intro hne
      have : e.rhs.head = e.lhs.head := by
        simpa [valuation, hne] using evaluated
      exact hne this.symm
    cases e with
    | mk lhs rhs =>
        cases lhs with
        | mk lhsHead lhsTail =>
            cases rhs with
            | mk rhsHead rhsTail =>
                simp only at lhsSingleton rhsSingleton heads
                subst rhsHead
                subst lhsTail
                subst rhsTail
                exact Derives.refl _
  · have rhsLong : e.rhs.tail ≠ [] := by
      intro hr
      exact lhsSingleton (singletonIff.mpr hr)
    have lhsNormal := firstOccurrenceDerivesNormal e.lhs
    have rhsNormal := firstOccurrenceDerivesNormal e.rhs
    cases hl : firstOccurrenceLongNormalList e.lhs.toList with
    | nil =>
        exact False.elim
          (firstOccurrenceLongNormalList_ne_nil e.lhs hl)
    | cons x xs =>
        cases hr : firstOccurrenceLongNormalList e.rhs.toList with
        | nil =>
            exact False.elim
              (firstOccurrenceLongNormalList_ne_nil e.rhs hr)
        | cons y ys =>
            rw [hl] at lhsNormal
            rw [hr] at rhsNormal
            have keyEvalEqual :
                ∀ valuation : Nat → Fin 4,
                  (∀ z, valuation z ≠ 1) →
                  bandListEval valuation
                      (occurrenceKey e.lhs.toList) =
                    bandListEval valuation
                      (occurrenceKey e.rhs.toList) := by
              intro valuation avoidsOne
              have lhsSound :=
                lhsNormal.sound firstOccurrenceFourBasis_models valuation
              have rhsSound :=
                rhsNormal.sound firstOccurrenceFourBasis_models valuation
              have lhsNormalEval :
                  firstOccurrenceFour.semigroup.eval valuation
                      (wordOfCons x xs) =
                    bandListEval valuation (x :: xs) := by
                simpa [wordOfCons, Word.toList] using
                  eval_eq_bandListEval valuation avoidsOne
                    (wordOfCons x xs)
              have rhsNormalEval :
                  firstOccurrenceFour.semigroup.eval valuation
                      (wordOfCons y ys) =
                    bandListEval valuation (y :: ys) := by
                simpa [wordOfCons, Word.toList] using
                  eval_eq_bandListEval valuation avoidsOne
                    (wordOfCons y ys)
              have lhsLong :=
                word_toList_length_ne_one_of_tail_ne_nil
                  e.lhs lhsSingleton
              have rhsLongList :=
                word_toList_length_ne_one_of_tail_ne_nil
                  e.rhs rhsLong
              have lhsEncoded :
                  x :: xs =
                    encodeLongOccurrenceKey
                      (occurrenceKey e.lhs.toList) := by
                rw [← hl]
                exact firstOccurrenceLongNormal_eq_encode
                  e.lhs.toList lhsLong
              have rhsEncoded :
                  y :: ys =
                    encodeLongOccurrenceKey
                      (occurrenceKey e.rhs.toList) := by
                rw [← hr]
                exact firstOccurrenceLongNormal_eq_encode
                  e.rhs.toList rhsLongList
              calc
                bandListEval valuation
                    (occurrenceKey e.lhs.toList) =
                    bandListEval valuation (x :: xs) := by
                      rw [lhsEncoded,
                        bandListEval_encodeLongOccurrenceKey
                          valuation avoidsOne]
                _ = firstOccurrenceFour.semigroup.eval valuation
                    (wordOfCons x xs) := lhsNormalEval.symm
                _ = firstOccurrenceFour.semigroup.eval valuation
                    e.lhs := lhsSound.symm
                _ = firstOccurrenceFour.semigroup.eval valuation
                    e.rhs := valid valuation
                _ = firstOccurrenceFour.semigroup.eval valuation
                    (wordOfCons y ys) := rhsSound
                _ = bandListEval valuation (y :: ys) := rhsNormalEval
                _ = bandListEval valuation
                    (occurrenceKey e.rhs.toList) := by
                      rw [rhsEncoded,
                        bandListEval_encodeLongOccurrenceKey
                          valuation avoidsOne]
            have keysEqual :
                occurrenceKey e.lhs.toList =
                  occurrenceKey e.rhs.toList :=
              nodup_eq_of_bandListEval_eq
                (occurrenceKey_nodup e.lhs.toList)
                (occurrenceKey_nodup e.rhs.toList)
                keyEvalEqual
            have normalsEqual : x :: xs = y :: ys := by
              have lhsLong :=
                word_toList_length_ne_one_of_tail_ne_nil
                  e.lhs lhsSingleton
              have rhsLongList :=
                word_toList_length_ne_one_of_tail_ne_nil
                  e.rhs rhsLong
              calc
                x :: xs =
                    firstOccurrenceLongNormalList e.lhs.toList :=
                      hl.symm
                _ = encodeLongOccurrenceKey
                    (occurrenceKey e.lhs.toList) :=
                      firstOccurrenceLongNormal_eq_encode
                        e.lhs.toList lhsLong
                _ = encodeLongOccurrenceKey
                    (occurrenceKey e.rhs.toList) := by rw [keysEqual]
                _ = firstOccurrenceLongNormalList e.rhs.toList :=
                      (firstOccurrenceLongNormal_eq_encode
                        e.rhs.toList rhsLongList).symm
                _ = y :: ys := hr
            cases normalsEqual
            exact Derives.trans lhsNormal (Derives.symm rhsNormal)

def firstOccurrenceFourOppositeBasis : List (Identity Nat) :=
  reversedBasis firstOccurrenceFourBasis

theorem firstOccurrenceFourOppositeBasis_complete :
    BasisFor firstOccurrenceFour.semigroup.opposite
      firstOccurrenceFourOppositeBasis := by
  simpa [firstOccurrenceFourOppositeBasis] using
    firstOccurrenceFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples

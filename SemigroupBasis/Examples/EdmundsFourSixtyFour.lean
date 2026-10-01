import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for Edmunds' `S(4,11)`, the catalogue
representative `S4_64` with table
`[[1,1,1,1],[1,1,1,1],[1,2,3,4],[4,4,4,4]]`. -/
def edmundsFourSixtyFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then b else 3

/-- The exact four-element Smallsemi representative `S4_64`. -/
def edmundsFourSixtyFour : FiniteTable where
  order := 4
  mul := edmundsFourSixtyFourMul
  assoc := by decide

def edmundsFourSixtyFourXY : Word Nat := ⟨0, [1]⟩
def edmundsFourSixtyFourXXY : Word Nat := ⟨0, [0, 1]⟩
def edmundsFourSixtyFourXYY : Word Nat := ⟨0, [1, 1]⟩
def edmundsFourSixtyFourXYX : Word Nat := ⟨0, [1, 0]⟩

def edmundsFourSixtyFourLeftContractionLaw : Identity Nat :=
  ⟨edmundsFourSixtyFourXXY, edmundsFourSixtyFourXY⟩

def edmundsFourSixtyFourEndpointLaw : Identity Nat :=
  ⟨edmundsFourSixtyFourXYY, edmundsFourSixtyFourXYX⟩

/-- Edmunds' basis for `S(4,11)`: `xxy = xy`, `xyy = xyx`. -/
def edmundsFourSixtyFourBasis : List (Identity Nat) :=
  [edmundsFourSixtyFourLeftContractionLaw,
    edmundsFourSixtyFourEndpointLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Contract a duplicated nonempty block when a nonempty suffix follows. -/
theorem edmundsFourSixtyFourDerivesLeftContraction
    (u v : Word Nat) :
    Derives edmundsFourSixtyFourBasis ((u ++ u) ++ v) (u ++ v) := by
  have hbase :
      Derives edmundsFourSixtyFourBasis
        edmundsFourSixtyFourXXY edmundsFourSixtyFourXY :=
    Derives.fromBasis
      (e := edmundsFourSixtyFourLeftContractionLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [edmundsFourSixtyFourBasis,
    edmundsFourSixtyFourLeftContractionLaw,
    edmundsFourSixtyFourXXY, edmundsFourSixtyFourXY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Replace a doubled right block by a return to the initial block. -/
theorem edmundsFourSixtyFourDerivesEndpoint
    (u v : Word Nat) :
    Derives edmundsFourSixtyFourBasis
      (u ++ (v ++ v)) ((u ++ v) ++ u) := by
  have hbase :
      Derives edmundsFourSixtyFourBasis
        edmundsFourSixtyFourXYY edmundsFourSixtyFourXYX :=
    Derives.fromBasis
      (e := edmundsFourSixtyFourEndpointLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [edmundsFourSixtyFourBasis,
    edmundsFourSixtyFourEndpointLaw,
    edmundsFourSixtyFourXYY, edmundsFourSixtyFourXYX,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- A return to an earlier block is erasable whenever a nonempty suffix
remains: `uvuw = uvw`. -/
theorem edmundsFourSixtyFourDerivesDeleteReturn
    (u v w : Word Nat) :
    Derives edmundsFourSixtyFourBasis
      (((u ++ v) ++ u) ++ w) ((u ++ v) ++ w) := by
  have replaceReturn :=
    Derives.appendRight
      (Derives.symm (edmundsFourSixtyFourDerivesEndpoint u v)) w
  have contract :=
    Derives.prepend u <|
      edmundsFourSixtyFourDerivesLeftContraction v w
  exact Derives.trans
    (by simpa [Word.append_assoc] using replaceReturn)
    (by simpa [Word.append_assoc] using contract)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Delete one nonfinal repeated letter. -/
private theorem edmundsFourSixtyFourDerivesDeleteOne
    (x : Nat) (middle suffix : List Nat) (hsuffix : suffix ≠ []) :
    Derives edmundsFourSixtyFourBasis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil => exact False.elim (hsuffix rfl)
      | cons y ys =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              edmundsFourSixtyFourDerivesLeftContraction
                (Word.singleton x) (wordOfCons y ys)
  | cons y ys =>
      let middleWord := wordOfCons y ys
      cases suffix with
      | nil => exact False.elim (hsuffix rfl)
      | cons z zs =>
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using
              edmundsFourSixtyFourDerivesDeleteReturn
                (Word.singleton x) middleWord (wordOfCons z zs)

/-- Delete all occurrences of `x` in `rest`, while preserving a fixed
nonempty final suffix. -/
private theorem edmundsFourSixtyFourDerivesDeleteAfter :
    ∀ (x : Nat) (middle rest suffix : List Nat), suffix ≠ [] →
      Derives edmundsFourSixtyFourBasis
        (wordOfCons x (middle ++ rest ++ suffix))
        (wordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x)) ++ suffix))
  | x, middle, [], suffix, _ => by
      simpa using
        Derives.refl (wordOfCons x (middle ++ suffix))
  | x, middle, y :: ys, suffix, hsuffix => by
      by_cases hy : y = x
      · subst y
        have first :=
          edmundsFourSixtyFourDerivesDeleteOne
            x middle (ys ++ suffix) (by simp [hsuffix])
        have remaining :=
          edmundsFourSixtyFourDerivesDeleteAfter
            x middle ys suffix hsuffix
        exact Derives.trans
          (by simpa [List.append_assoc] using first)
          (by simpa using remaining)
      · have remaining :=
          edmundsFourSixtyFourDerivesDeleteAfter
            x (middle ++ [y]) ys suffix hsuffix
        simpa [hy, List.append_assoc] using remaining

/-- Normalize a nonempty prefix to its duplicate-free first-occurrence
sequence, while leaving one designated final letter untouched. -/
private theorem edmundsFourSixtyFourDerivesNormalizePrefix :
    ∀ (x : Nat) (xs : List Nat) (last : Nat),
      match firstOccurrenceSequence (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives edmundsFourSixtyFourBasis
            (wordOfCons x (xs ++ [last]))
            (wordOfCons y (ys ++ [last]))
  | x, [], last => by
      exact Derives.refl _
  | x, y :: ys, last => by
      have suffixNormal :=
        edmundsFourSixtyFourDerivesNormalizePrefix y ys last
      cases hs : firstOccurrenceSequence (y :: ys) with
      | nil =>
          simp [firstOccurrenceSequence] at hs
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have deleted :=
            edmundsFourSixtyFourDerivesDeleteAfter
              x [] (z :: zs) [last] (by simp)
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
                Word.append_assoc, List.append_assoc] using prefixed)
            (by
              simpa [wordOfCons, List.append_assoc] using deleted)
termination_by
  _ xs _ => xs.length

/-- If the final letter already occurs, replace it by the first letter. -/
private theorem edmundsFourSixtyFourDerivesClose :
    ∀ (x : Nat) (middle : List Nat) (last : Nat),
      last ∈ x :: middle →
      Derives edmundsFourSixtyFourBasis
        (wordOfCons x (middle ++ [last]))
        (wordOfCons x (middle ++ [x]))
  | x, [], last, hmem => by
      have : last = x := by simpa using hmem
      subst last
      exact Derives.refl _
  | x, y :: ys, last, hmem => by
      by_cases hlx : last = x
      · subst last
        exact Derives.refl _
      · have htail : last ∈ y :: ys := by
          simpa [hlx] using hmem
        have closeTail :=
          edmundsFourSixtyFourDerivesClose y ys last htail
        have prefixed :=
          Derives.prepend (Word.singleton x) closeTail
        have moveEndpoint :
            Derives edmundsFourSixtyFourBasis
              (wordOfCons x (y :: ys ++ [y]))
              (wordOfCons x (y :: ys ++ [x])) := by
          cases ys with
          | nil =>
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc] using
                  edmundsFourSixtyFourDerivesEndpoint
                    (Word.singleton x) (Word.singleton y)
          | cons z zs =>
              let middleWord := wordOfCons z zs
              have insertDuplicate :=
                Derives.prepend (Word.singleton x) <|
                  Derives.appendRight
                    (Derives.symm <|
                      edmundsFourSixtyFourDerivesLeftContraction
                        (Word.singleton y) middleWord)
                    (Word.singleton y)
              have duplicateLongSuffix :=
                Derives.prepend (Word.singleton x) <|
                  Derives.symm <|
                    edmundsFourSixtyFourDerivesEndpoint
                      (Word.singleton y)
                      (Word.singleton y ++ middleWord)
              have contractDuplicate :=
                Derives.prepend (Word.singleton x) <|
                  edmundsFourSixtyFourDerivesLeftContraction
                    (Word.singleton y)
                    (middleWord ++
                      (Word.singleton y ++ middleWord))
              have closeLongSuffix :=
                edmundsFourSixtyFourDerivesEndpoint
                  (Word.singleton x)
                  (Word.singleton y ++ middleWord)
              exact Derives.trans
                (by
                  simpa [wordOfCons, middleWord, Word.append,
                    Word.singleton, Word.append_assoc,
                    List.append_assoc] using insertDuplicate)
                (Derives.trans
                  (by
                    simpa [wordOfCons, middleWord, Word.append,
                      Word.singleton, Word.append_assoc,
                      List.append_assoc] using duplicateLongSuffix)
                  (Derives.trans
                    (by
                      simpa [wordOfCons, middleWord, Word.append,
                        Word.singleton, Word.append_assoc,
                        List.append_assoc] using contractDuplicate)
                    (by
                      simpa [wordOfCons, middleWord, Word.append,
                        Word.singleton, Word.append_assoc,
                        List.append_assoc] using closeLongSuffix)))
        exact Derives.trans
          (by
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc, List.append_assoc] using prefixed)
          moveEndpoint
termination_by
  _ middle _ _ => middle.length

/-- Canonical long form from a duplicate-free prefix and a designated final
letter. A fresh final letter remains; a repeated final letter closes the
sequence by its first letter. -/
def edmundsFourSixtyFourLongNormal
    (x : Nat) (xs : List Nat) (last : Nat) : Word Nat :=
  if last ∈ x :: xs then wordOfCons x (xs ++ [x])
  else wordOfCons x (xs ++ [last])

/-- Every non-singleton word derives to its canonical open-or-closed
first-occurrence form. -/
theorem edmundsFourSixtyFourDerivesLongNormal
    (x : Nat) (prefixTail : List Nat) (last : Nat) :
    match firstOccurrenceSequence (x :: prefixTail) with
    | [] => False
    | y :: ys =>
        Derives edmundsFourSixtyFourBasis
          (wordOfCons x (prefixTail ++ [last]))
          (edmundsFourSixtyFourLongNormal y ys last) := by
  have prefixNormal :=
    edmundsFourSixtyFourDerivesNormalizePrefix x prefixTail last
  cases hs : firstOccurrenceSequence (x :: prefixTail) with
  | nil =>
      rw [hs] at prefixNormal
      exact prefixNormal
  | cons y ys =>
      rw [hs] at prefixNormal
      by_cases hlast : last ∈ y :: ys
      · have close :=
          edmundsFourSixtyFourDerivesClose y ys last hlast
        exact Derives.trans prefixNormal <| by
          simpa [edmundsFourSixtyFourLongNormal, hlast,
            wordOfCons] using close
      · simpa [edmundsFourSixtyFourLongNormal, hlast,
          wordOfCons] using prefixNormal

private theorem edmundsFourSixtyFourMul_leftContraction
    (a b : Fin 4) :
    edmundsFourSixtyFourMul
        (edmundsFourSixtyFourMul a a) b =
      edmundsFourSixtyFourMul a b := by
  decide +revert

private theorem edmundsFourSixtyFourMul_endpoint
    (a b : Fin 4) :
    edmundsFourSixtyFourMul
        (edmundsFourSixtyFourMul a b) b =
      edmundsFourSixtyFourMul
        (edmundsFourSixtyFourMul a b) a := by
  decide +revert

theorem edmundsFourSixtyFourBasis_models :
    Models edmundsFourSixtyFour.semigroup
      edmundsFourSixtyFourBasis := by
  intro e he
  simp only [edmundsFourSixtyFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      edmundsFourSixtyFourMul
          (edmundsFourSixtyFourMul (valuation 0) (valuation 0))
          (valuation 1) =
        edmundsFourSixtyFourMul (valuation 0) (valuation 1)
    exact edmundsFourSixtyFourMul_leftContraction
      (valuation 0) (valuation 1)
  · intro valuation
    change
      edmundsFourSixtyFourMul
          (edmundsFourSixtyFourMul (valuation 0) (valuation 1))
          (valuation 1) =
        edmundsFourSixtyFourMul
          (edmundsFourSixtyFourMul (valuation 0) (valuation 1))
          (valuation 0)
    exact edmundsFourSixtyFourMul_endpoint
      (valuation 0) (valuation 1)

/-- Encode a duplicate-free key either openly or with its first letter
repeated at the endpoint. -/
def edmundsFourSixtyFourNormalWord
    (x : Nat) (xs : List Nat) (closed : Bool) : Word Nat :=
  if closed then wordOfCons x (xs ++ [x]) else wordOfCons x xs

/-- Evaluation of a possibly empty list, using the left identity `2`. -/
private def edmundsFourSixtyFourListEval
    (valuation : Nat → Fin 4) (xs : List Nat) : Fin 4 :=
  xs.foldl
    (fun current x => edmundsFourSixtyFourMul current (valuation x)) 2

private theorem edmundsFourSixtyFourEval_eq_listEval
    (valuation : Nat → Fin 4) (w : Word Nat) :
    edmundsFourSixtyFour.semigroup.eval valuation w =
      edmundsFourSixtyFourListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              edmundsFourSixtyFourMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              edmundsFourSixtyFourMul current (valuation x))
            (edmundsFourSixtyFourMul 2 (valuation head))
      rw [show edmundsFourSixtyFourMul 2 (valuation head) =
          valuation head by
        simp [edmundsFourSixtyFourMul]]

private theorem edmundsFourSixtyFourFold_left_zero
    (valuation : Nat → Fin 4) (a : Fin 4)
    (ha : a = 0 ∨ a = 3) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          edmundsFourSixtyFourMul current (valuation x)) a = a := by
  rcases ha with rfl | rfl
  · induction xs with
    | nil => rfl
    | cons x xs ih =>
        simpa [List.foldl_cons, edmundsFourSixtyFourMul] using ih
  · induction xs with
    | nil => rfl
    | cons x xs ih =>
        simpa [List.foldl_cons, edmundsFourSixtyFourMul] using ih

private theorem edmundsFourSixtyFourListEval_cons_of_left_zero
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 0 ∨ valuation x = 3) :
    edmundsFourSixtyFourListEval valuation (x :: xs) =
      valuation x := by
  unfold edmundsFourSixtyFourListEval
  simp only [List.foldl_cons]
  rw [show edmundsFourSixtyFourMul 2 (valuation x) =
      valuation x by
    simp [edmundsFourSixtyFourMul]]
  exact edmundsFourSixtyFourFold_left_zero
    valuation (valuation x) hx xs

private theorem edmundsFourSixtyFourListEval_cons_of_two
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 2) :
    edmundsFourSixtyFourListEval valuation (x :: xs) =
      edmundsFourSixtyFourListEval valuation xs := by
  simp [edmundsFourSixtyFourListEval,
    edmundsFourSixtyFourMul, hx]

private theorem edmundsFourSixtyFourFold_congr
    (v₁ v₂ : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            edmundsFourSixtyFourMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            edmundsFourSixtyFourMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact edmundsFourSixtyFourFold_congr v₁ v₂ xs
        (edmundsFourSixtyFourMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem edmundsFourSixtyFourListEval_congr
    (v₁ v₂ : Nat → Fin 4) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    edmundsFourSixtyFourListEval v₁ xs =
      edmundsFourSixtyFourListEval v₂ xs :=
  edmundsFourSixtyFourFold_congr v₁ v₂ xs 2 agree

/-- On valuations avoiding the transient value `1`, the table is the
three-element left regular band with identity `2` and left zeros `0,3`.
Consequently it separates duplicate-free first-occurrence sequences. -/
private theorem edmundsFourSixtyFourNodup_eq_of_listEval_eq :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ valuation : Nat → Fin 4,
        (∀ z, valuation z ≠ 1) →
        edmundsFourSixtyFourListEval valuation xs =
          edmundsFourSixtyFourListEval valuation ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = y then 0 else 2
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases hz : z = y <;> simp [valuation, hz]
      have h := equalEval valuation avoids
      have rightValue :
          edmundsFourSixtyFourListEval valuation (y :: ys) = 0 := by
        simpa [valuation] using
          edmundsFourSixtyFourListEval_cons_of_left_zero
            valuation y ys (Or.inl (by simp [valuation]))
      change (2 : Fin 4) =
        edmundsFourSixtyFourListEval valuation (y :: ys) at h
      rw [rightValue] at h
      exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = x then 0 else 2
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases hz : z = x <;> simp [valuation, hz]
      have h := equalEval valuation avoids
      have leftValue :
          edmundsFourSixtyFourListEval valuation (x :: xs) = 0 := by
        simpa [valuation] using
          edmundsFourSixtyFourListEval_cons_of_left_zero
            valuation x xs (Or.inl (by simp [valuation]))
      change
        edmundsFourSixtyFourListEval valuation (x :: xs) =
          (2 : Fin 4) at h
      rw [leftValue] at h
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
        have leftValue :
            edmundsFourSixtyFourListEval valuation (x :: xs) = 0 := by
          simpa [valuation] using
            edmundsFourSixtyFourListEval_cons_of_left_zero
              valuation x xs (Or.inl (by simp [valuation]))
        have rightValue :
            edmundsFourSixtyFourListEval valuation (y :: ys) = 3 := by
          simpa [valuation, Ne.symm hxy] using
            edmundsFourSixtyFourListEval_cons_of_left_zero
              valuation y ys
                (Or.inr (by simp [valuation, Ne.symm hxy]))
        rw [leftValue, rightValue] at h
        exact (by decide : (0 : Fin 4) ≠ 3) h
      subst y
      have xNotMemXs : x ∉ xs := (List.nodup_cons.mp nodupX).1
      have xNotMemYs : x ∉ ys := (List.nodup_cons.mp nodupY).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 4,
            (∀ z, valuation z ≠ 1) →
            edmundsFourSixtyFourListEval valuation xs =
              edmundsFourSixtyFourListEval valuation ys := by
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
        rw [edmundsFourSixtyFourListEval_cons_of_two
              masked x xs maskedX,
            edmundsFourSixtyFourListEval_cons_of_two
              masked x ys maskedX] at fullEqual
        calc
          edmundsFourSixtyFourListEval valuation xs =
              edmundsFourSixtyFourListEval masked xs := by
                apply edmundsFourSixtyFourListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemXs
                  simpa [h] using hz
                simp [masked, hzx]
          _ = edmundsFourSixtyFourListEval masked ys := fullEqual
          _ = edmundsFourSixtyFourListEval valuation ys := by
                apply edmundsFourSixtyFourListEval_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMemYs
                  simpa [h] using hz
                simp [masked, hzx]
      congr 1
      exact edmundsFourSixtyFourNodup_eq_of_listEval_eq
        (List.nodup_cons.mp nodupX).2
        (List.nodup_cons.mp nodupY).2 tailsEqual

private theorem edmundsFourSixtyFourMul_preserves_avoidsOne
    (a b : Fin 4) (ha : a ≠ 1) (hb : b ≠ 1) :
    edmundsFourSixtyFourMul a b ≠ 1 := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with
    rfl | rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with
      rfl | rfl | rfl | rfl <;>
    simp_all [edmundsFourSixtyFourMul]

private theorem edmundsFourSixtyFourFold_preserves_avoidsOne
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) :
    ∀ (xs : List Nat) (acc : Fin 4), acc ≠ 1 →
      xs.foldl
          (fun current x =>
            edmundsFourSixtyFourMul current (valuation x)) acc ≠ 1
  | [], _, hacc => hacc
  | x :: xs, acc, hacc => by
      simp only [List.foldl_cons]
      exact edmundsFourSixtyFourFold_preserves_avoidsOne
        valuation avoidsOne xs
        (edmundsFourSixtyFourMul acc (valuation x))
        (edmundsFourSixtyFourMul_preserves_avoidsOne
          acc (valuation x) hacc (avoidsOne x))

private theorem edmundsFourSixtyFourListEval_avoidsOne
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) (xs : List Nat) :
    edmundsFourSixtyFourListEval valuation xs ≠ 1 := by
  exact edmundsFourSixtyFourFold_preserves_avoidsOne
    valuation avoidsOne xs 2 (by decide)

private theorem edmundsFourSixtyFourMul_right_two_of_ne_one
    (a : Fin 4) (ha : a ≠ 1) :
    edmundsFourSixtyFourMul a 2 = a := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with
    rfl | rfl | rfl | rfl <;>
    simp_all [edmundsFourSixtyFourMul]

private theorem edmundsFourSixtyFourListEval_append_singleton
    (valuation : Nat → Fin 4) (xs : List Nat) (x : Nat) :
    edmundsFourSixtyFourListEval valuation (xs ++ [x]) =
      edmundsFourSixtyFourMul
        (edmundsFourSixtyFourListEval valuation xs) (valuation x) := by
  simp [edmundsFourSixtyFourListEval, List.foldl_append]

/-- Closing a key by its head is invisible on valuations avoiding `1`. -/
private theorem edmundsFourSixtyFourListEval_close_eq
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1)
    (x : Nat) (xs : List Nat) :
    edmundsFourSixtyFourListEval valuation
        ((x :: xs) ++ [x]) =
      edmundsFourSixtyFourListEval valuation (x :: xs) := by
  rw [edmundsFourSixtyFourListEval_append_singleton]
  rcases
      (show valuation x = 0 ∨ valuation x = 1 ∨
          valuation x = 2 ∨ valuation x = 3 by omega) with
    hx | hx | hx | hx
  · have value :
        edmundsFourSixtyFourListEval valuation (x :: xs) = 0 := by
      simpa [hx] using
        edmundsFourSixtyFourListEval_cons_of_left_zero
          valuation x xs (Or.inl hx)
    rw [value, hx]
    rfl
  · exact False.elim ((avoidsOne x) hx)
  · rw [hx]
    exact edmundsFourSixtyFourMul_right_two_of_ne_one _
      (edmundsFourSixtyFourListEval_avoidsOne
        valuation avoidsOne (x :: xs))
  · have value :
        edmundsFourSixtyFourListEval valuation (x :: xs) = 3 := by
      simpa [hx] using
        edmundsFourSixtyFourListEval_cons_of_left_zero
          valuation x xs (Or.inr hx)
    rw [value, hx]
    rfl

private def edmundsFourSixtyFourLastSeparator
    (key : List Nat) (hne : key ≠ []) : Nat → Fin 4 :=
  fun z => if z = key.getLast hne then 1 else 2

private theorem edmundsFourSixtyFourFold_all_two
    (valuation : Nat → Fin 4) :
    ∀ (xs : List Nat),
      (∀ z, z ∈ xs → valuation z = 2) →
      xs.foldl
          (fun current z =>
            edmundsFourSixtyFourMul current (valuation z)) 2 = 2
  | [], _ => rfl
  | z :: zs, hall => by
      simp only [List.foldl_cons]
      rw [hall z (List.Mem.head zs)]
      change
        zs.foldl
            (fun current z =>
              edmundsFourSixtyFourMul current (valuation z)) 2 = 2
      exact edmundsFourSixtyFourFold_all_two valuation zs
        (fun y hy => hall y (List.Mem.tail z hy))

/-- The last separator evaluates an open nonempty duplicate-free key to `1`. -/
private theorem edmundsFourSixtyFourLastSeparator_open
    (key : List Nat) (hne : key ≠ []) (hnodup : key.Nodup) :
    edmundsFourSixtyFourListEval
        (edmundsFourSixtyFourLastSeparator key hne) key = 1 := by
  let last := key.getLast hne
  have reconstruct : key.dropLast ++ [last] = key := by
    exact List.dropLast_concat_getLast hne
  have splitNodup : (key.dropLast ++ [last]).Nodup := by
    simpa [reconstruct] using hnodup
  have lastNotMem : last ∉ key.dropLast := by
    intro hmem
    exact
      (List.nodup_append.mp splitNodup).2.2
        last hmem last (by simp) rfl
  calc
    edmundsFourSixtyFourListEval
        (edmundsFourSixtyFourLastSeparator key hne) key =
        edmundsFourSixtyFourListEval
          (edmundsFourSixtyFourLastSeparator key hne)
          (key.dropLast ++ [last]) := by rw [reconstruct]
    _ = edmundsFourSixtyFourMul
        (edmundsFourSixtyFourListEval
          (edmundsFourSixtyFourLastSeparator key hne)
          key.dropLast)
        (edmundsFourSixtyFourLastSeparator key hne last) := by
          rw [edmundsFourSixtyFourListEval_append_singleton]
    _ = 1 := by
      have prefixValue :
          edmundsFourSixtyFourListEval
              (edmundsFourSixtyFourLastSeparator key hne)
              key.dropLast = 2 := by
        unfold edmundsFourSixtyFourListEval
        apply edmundsFourSixtyFourFold_all_two
        intro z hz
        have hneLast : z ≠ last := by
          intro h
          subst z
          exact lastNotMem hz
        simp [edmundsFourSixtyFourLastSeparator, last, hneLast]
      rw [prefixValue]
      simp [edmundsFourSixtyFourLastSeparator, last,
        edmundsFourSixtyFourMul]

/-- The same separator evaluates the closed key to `0`. -/
private theorem edmundsFourSixtyFourLastSeparator_closed
    (x : Nat) (xs : List Nat)
    (hnodup : (x :: xs).Nodup) :
    edmundsFourSixtyFourListEval
        (edmundsFourSixtyFourLastSeparator (x :: xs) (by simp))
        ((x :: xs) ++ [x]) = 0 := by
  rw [edmundsFourSixtyFourListEval_append_singleton,
    edmundsFourSixtyFourLastSeparator_open
      (x :: xs) (by simp) hnodup]
  by_cases hx :
      x = (x :: xs).getLast (by simp)
  · simp [edmundsFourSixtyFourMul]
  · simp [edmundsFourSixtyFourMul]

/-- Exact-table separators distinguish all open and closed duplicate-free
normal forms. -/
theorem edmundsFourSixtyFourNormalWord_eq_of_eval_eq
    (x y : Nat) (xs ys : List Nat) (closedX closedY : Bool)
    (nodupX : (x :: xs).Nodup) (nodupY : (y :: ys).Nodup)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        edmundsFourSixtyFour.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord x xs closedX) =
          edmundsFourSixtyFour.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord y ys closedY)) :
    edmundsFourSixtyFourNormalWord x xs closedX =
      edmundsFourSixtyFourNormalWord y ys closedY := by
  have keysEqual : x :: xs = y :: ys := by
    apply edmundsFourSixtyFourNodup_eq_of_listEval_eq
      nodupX nodupY
    intro valuation avoidsOne
    have h := equalEval valuation
    rw [edmundsFourSixtyFourEval_eq_listEval,
      edmundsFourSixtyFourEval_eq_listEval] at h
    cases closedX <;> cases closedY
    · simpa [edmundsFourSixtyFourNormalWord, wordOfCons,
        Word.toList] using h
    · have h' :
          edmundsFourSixtyFourListEval valuation (x :: xs) =
            edmundsFourSixtyFourListEval valuation
              ((y :: ys) ++ [y]) := by
          simpa [edmundsFourSixtyFourNormalWord, wordOfCons,
            Word.toList] using h
      exact h'.trans <|
        edmundsFourSixtyFourListEval_close_eq
          valuation avoidsOne y ys
    · have h' :
          edmundsFourSixtyFourListEval valuation
              ((x :: xs) ++ [x]) =
            edmundsFourSixtyFourListEval valuation (y :: ys) := by
          simpa [edmundsFourSixtyFourNormalWord, wordOfCons,
            Word.toList] using h
      exact
        (edmundsFourSixtyFourListEval_close_eq
          valuation avoidsOne x xs).symm.trans h'
    · have h' :
          edmundsFourSixtyFourListEval valuation
              ((x :: xs) ++ [x]) =
            edmundsFourSixtyFourListEval valuation
              ((y :: ys) ++ [y]) := by
          simpa [edmundsFourSixtyFourNormalWord, wordOfCons,
            Word.toList] using h
      exact
        (edmundsFourSixtyFourListEval_close_eq
          valuation avoidsOne x xs).symm.trans <|
            h'.trans <|
              edmundsFourSixtyFourListEval_close_eq
                valuation avoidsOne y ys
  cases keysEqual
  cases closedX <;> cases closedY
  · rfl
  · let valuation :=
      edmundsFourSixtyFourLastSeparator (x :: xs) (by simp)
    have h := equalEval valuation
    rw [edmundsFourSixtyFourEval_eq_listEval,
      edmundsFourSixtyFourEval_eq_listEval] at h
    simp [edmundsFourSixtyFourNormalWord, wordOfCons,
      Word.toList] at h
    have openValue :
        edmundsFourSixtyFourListEval valuation (x :: xs) = 1 := by
      dsimp [valuation]
      exact edmundsFourSixtyFourLastSeparator_open
        (x :: xs) (by simp) nodupX
    have closedValue :
        edmundsFourSixtyFourListEval valuation
            (x :: (xs ++ [x])) = 0 := by
      dsimp [valuation]
      simpa using
        edmundsFourSixtyFourLastSeparator_closed x xs nodupX
    rw [openValue, closedValue] at h
    exact False.elim ((by decide : (1 : Fin 4) ≠ 0) h)
  · let valuation :=
      edmundsFourSixtyFourLastSeparator (x :: xs) (by simp)
    have h := equalEval valuation
    rw [edmundsFourSixtyFourEval_eq_listEval,
      edmundsFourSixtyFourEval_eq_listEval] at h
    simp [edmundsFourSixtyFourNormalWord, wordOfCons,
      Word.toList] at h
    have openValue :
        edmundsFourSixtyFourListEval valuation (x :: xs) = 1 := by
      dsimp [valuation]
      exact edmundsFourSixtyFourLastSeparator_open
        (x :: xs) (by simp) nodupX
    have closedValue :
        edmundsFourSixtyFourListEval valuation
            (x :: (xs ++ [x])) = 0 := by
      dsimp [valuation]
      simpa using
        edmundsFourSixtyFourLastSeparator_closed x xs nodupX
    rw [closedValue, openValue] at h
    exact False.elim ((by decide : (0 : Fin 4) ≠ 1) h)
  · rfl

/-- Every word derives to an open or closed duplicate-free key. -/
private theorem edmundsFourSixtyFourDerivesSomeNormal
    (w : Word Nat) :
    ∃ x xs closed,
      (x :: xs).Nodup ∧
      Derives edmundsFourSixtyFourBasis w
        (edmundsFourSixtyFourNormalWord x xs closed) := by
  cases w with
  | mk head tail =>
      by_cases htail : tail = []
      · subst tail
        exact ⟨head, [], false, by simp, Derives.refl _⟩
      · let last := tail.getLast htail
        let prefixTail := tail.dropLast
        have reconstruct : prefixTail ++ [last] = tail := by
          exact List.dropLast_concat_getLast htail
        have normalizes :=
          edmundsFourSixtyFourDerivesLongNormal head prefixTail last
        cases hs : firstOccurrenceSequence (head :: prefixTail) with
        | nil =>
            have impossible :
                firstOccurrenceSequence (head :: prefixTail) ≠ [] := by
              simp [firstOccurrenceSequence]
            exact False.elim (impossible hs)
        | cons x xs =>
            rw [hs] at normalizes
            have keyNodup : (x :: xs).Nodup := by
              rw [← hs]
              exact firstOccurrenceSequence_nodup
                (head :: prefixTail)
            by_cases hlast : last ∈ x :: xs
            · refine ⟨x, xs, true, keyNodup, ?_⟩
              simpa [reconstruct,
                edmundsFourSixtyFourLongNormal, hlast,
                edmundsFourSixtyFourNormalWord] using normalizes
            · have extendedNodup : (x :: xs ++ [last]).Nodup := by
                apply List.nodup_append.mpr
                refine ⟨keyNodup, by simp, ?_⟩
                intro a ha b hb
                simp only [List.mem_singleton] at hb
                subst b
                intro halast
                subst a
                exact hlast ha
              refine ⟨x, xs ++ [last], false, extendedNodup, ?_⟩
              simpa [reconstruct,
                edmundsFourSixtyFourLongNormal, hlast,
                edmundsFourSixtyFourNormalWord] using normalizes

/-- Unrestricted completeness over `Nat` variables. Every word reduces to a
duplicate-free first-occurrence key, either open or closed by its head. The
exact four-element table separates the key on `{0,2,3}` and the endpoint bit
with the transient value `1`. -/
theorem edmundsFourSixtyFourBasis_complete :
    BasisFor edmundsFourSixtyFour.semigroup
      edmundsFourSixtyFourBasis := by
  refine ⟨edmundsFourSixtyFourBasis_models, ?_⟩
  intro e valid
  obtain ⟨x, xs, closedX, nodupX, lhsNormal⟩ :=
    edmundsFourSixtyFourDerivesSomeNormal e.lhs
  obtain ⟨y, ys, closedY, nodupY, rhsNormal⟩ :=
    edmundsFourSixtyFourDerivesSomeNormal e.rhs
  have normalEvalEqual :
      ∀ valuation : Nat → Fin 4,
        edmundsFourSixtyFour.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord x xs closedX) =
          edmundsFourSixtyFour.semigroup.eval valuation
            (edmundsFourSixtyFourNormalWord y ys closedY) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound edmundsFourSixtyFourBasis_models valuation
    have rhsSound :=
      rhsNormal.sound edmundsFourSixtyFourBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have normalWordsEqual :=
    edmundsFourSixtyFourNormalWord_eq_of_eval_eq
      x y xs ys closedX closedY nodupX nodupY normalEvalEqual
  rw [normalWordsEqual] at lhsNormal
  exact Derives.trans lhsNormal (Derives.symm rhsNormal)

def edmundsFourSixtyFourOppositeBasis : List (Identity Nat) :=
  reversedBasis edmundsFourSixtyFourBasis

theorem edmundsFourSixtyFourOppositeBasis_complete :
    BasisFor edmundsFourSixtyFour.semigroup.opposite
      edmundsFourSixtyFourOppositeBasis := by
  simpa [edmundsFourSixtyFourOppositeBasis] using
    edmundsFourSixtyFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples

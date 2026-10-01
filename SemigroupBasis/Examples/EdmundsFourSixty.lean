import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,2,3,1],[4,4,4,4]]`. -/
def edmundsFourSixtyMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then (if b = 3 then 0 else b) else 3

/-- The root catalogue representative `S4_60`. -/
def edmundsFourSixty : FiniteTable where
  order := 4
  mul := edmundsFourSixtyMul
  assoc := by decide

def edmundsFourSixtyXYXZ : Word Nat := ⟨0, [1, 0, 2]⟩
def edmundsFourSixtyXXYZ : Word Nat := ⟨0, [0, 1, 2]⟩
def edmundsFourSixtyXYZY : Word Nat := ⟨0, [1, 2, 1]⟩
def edmundsFourSixtyXZYY : Word Nat := ⟨0, [2, 1, 1]⟩
def edmundsFourSixtyXXY : Word Nat := ⟨0, [0, 1]⟩
def edmundsFourSixtyXY : Word Nat := ⟨0, [1]⟩
def edmundsFourSixtyXYZZ : Word Nat := ⟨0, [1, 2, 2]⟩

def edmundsFourSixtyInitialGatherLaw : Identity Nat :=
  ⟨edmundsFourSixtyXYXZ, edmundsFourSixtyXXYZ⟩

def edmundsFourSixtyFinalGatherLaw : Identity Nat :=
  ⟨edmundsFourSixtyXYZY, edmundsFourSixtyXZYY⟩

def edmundsFourSixtyLeftContractionLaw : Identity Nat :=
  ⟨edmundsFourSixtyXXY, edmundsFourSixtyXY⟩

def edmundsFourSixtyFinalSwitchLaw : Identity Nat :=
  ⟨edmundsFourSixtyXYZZ, edmundsFourSixtyXZYY⟩

/-- Edmunds' item 37 basis for `S4_60`:
`xyxz = xxyz`, `xyzy = xzyy`, `xxy = xy`, `xyzz = xzyy`. -/
def edmundsFourSixtyBasis : List (Identity Nat) :=
  [edmundsFourSixtyInitialGatherLaw,
    edmundsFourSixtyFinalGatherLaw,
    edmundsFourSixtyLeftContractionLaw,
    edmundsFourSixtyFinalSwitchLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem edmundsFourSixtyDerivesInitialGather
    (u v q : Word Nat) :
    Derives edmundsFourSixtyBasis
      (((u ++ v) ++ u) ++ q) (((u ++ u) ++ v) ++ q) := by
  have hbase :
      Derives edmundsFourSixtyBasis
        edmundsFourSixtyXYXZ edmundsFourSixtyXXYZ :=
    Derives.fromBasis (e := edmundsFourSixtyInitialGatherLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v q)
  simpa [edmundsFourSixtyBasis, edmundsFourSixtyInitialGatherLaw,
    edmundsFourSixtyXYXZ, edmundsFourSixtyXXYZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourSixtyDerivesFinalGather
    (p u v : Word Nat) :
    Derives edmundsFourSixtyBasis
      (((p ++ u) ++ v) ++ u) (((p ++ v) ++ u) ++ u) := by
  have hbase :
      Derives edmundsFourSixtyBasis
        edmundsFourSixtyXYZY edmundsFourSixtyXZYY :=
    Derives.fromBasis (e := edmundsFourSixtyFinalGatherLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [edmundsFourSixtyBasis, edmundsFourSixtyFinalGatherLaw,
    edmundsFourSixtyXYZY, edmundsFourSixtyXZYY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourSixtyDerivesLeftContraction
    (u v : Word Nat) :
    Derives edmundsFourSixtyBasis ((u ++ u) ++ v) (u ++ v) := by
  have hbase :
      Derives edmundsFourSixtyBasis
        edmundsFourSixtyXXY edmundsFourSixtyXY :=
    Derives.fromBasis (e := edmundsFourSixtyLeftContractionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [edmundsFourSixtyBasis, edmundsFourSixtyLeftContractionLaw,
    edmundsFourSixtyXXY, edmundsFourSixtyXY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourSixtyDerivesFinalSwitch
    (p u v : Word Nat) :
    Derives edmundsFourSixtyBasis
      (((p ++ u) ++ v) ++ v) (((p ++ v) ++ u) ++ u) := by
  have hbase :
      Derives edmundsFourSixtyBasis
        edmundsFourSixtyXYZZ edmundsFourSixtyXZYY :=
    Derives.fromBasis (e := edmundsFourSixtyFinalSwitchLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [edmundsFourSixtyBasis, edmundsFourSixtyFinalSwitchLaw,
    edmundsFourSixtyXYZZ, edmundsFourSixtyXZYY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Arbitrary nonempty blocks after a fixed nonempty prefix may be swapped
while a nonempty suffix remains. -/
theorem edmundsFourSixtyDerivesSuffixSwap
    (p u v q : Word Nat) :
    Derives edmundsFourSixtyBasis
      (((p ++ u) ++ v) ++ q) (((p ++ v) ++ u) ++ q) := by
  have expand :=
    Derives.prepend (p ++ u) <|
      Derives.symm (edmundsFourSixtyDerivesLeftContraction v q)
  have switch :=
    Derives.appendRight
      (edmundsFourSixtyDerivesFinalSwitch p u v) q
  have contract :=
    Derives.prepend (p ++ v) <|
      edmundsFourSixtyDerivesLeftContraction u q
  exact Derives.trans
    (by simpa [Word.append_assoc] using expand) <|
    Derives.trans
      (by simpa [Word.append_assoc] using switch)
      (by simpa [Word.append_assoc] using contract)

private theorem edmundsFourSixtyDerivesPrefixPermutation
    (anchor : Word Nat) {prefix₁ prefix₂ : List Nat}
    (hperm : prefix₁.Perm prefix₂) (final : Nat) :
    Derives edmundsFourSixtyBasis
      (anchor ++ wordOfPrefixFinal prefix₁ final)
      (anchor ++ wordOfPrefixFinal prefix₂ final) := by
  induction hperm generalizing anchor with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [Word.append_assoc] using
        ih (anchor := anchor ++ Word.singleton x)
  | swap x y xs =>
      simpa [Word.append_assoc] using
        edmundsFourSixtyDerivesSuffixSwap
          anchor (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ (anchor := anchor))
        (ih₂ (anchor := anchor))

private theorem edmundsFourSixtyDerivesDeleteDuplicate
    (anchor : Word Nat) (x : Nat) (reduced : List Nat)
    (final : Nat) (hx : x ∈ reduced) :
    Derives edmundsFourSixtyBasis
      (anchor ++ wordOfPrefixFinal (x :: reduced) final)
      (anchor ++ wordOfPrefixFinal reduced final) := by
  have expose : reduced.Perm (x :: reduced.erase x) :=
    List.perm_cons_erase hx
  have arrange :
      (x :: reduced).Perm (x :: x :: reduced.erase x) :=
    List.Perm.cons x expose
  have contract :=
    Derives.prepend anchor <|
      edmundsFourSixtyDerivesLeftContraction
        (Word.singleton x)
        (wordOfPrefixFinal (reduced.erase x) final)
  exact Derives.trans
    (edmundsFourSixtyDerivesPrefixPermutation
      anchor arrange final) <|
    Derives.trans
      (by simpa [wordOfPrefixFinal, Word.append_assoc] using contract)
      (edmundsFourSixtyDerivesPrefixPermutation
        anchor expose.symm final)

private theorem edmundsFourSixtyDerivesDedupUnderAnchor :
    ∀ (anchor : Word Nat) (pref : List Nat) (final : Nat),
      Derives edmundsFourSixtyBasis
        (anchor ++ wordOfPrefixFinal pref final)
        (anchor ++ wordOfPrefixFinal
          (finalMarkerPrefixReduce pref) final)
  | anchor, [], final => Derives.refl _
  | anchor, x :: xs, final => by
      have suffixNormal :=
        edmundsFourSixtyDerivesDedupUnderAnchor
          (anchor ++ Word.singleton x) xs final
      let reduced := finalMarkerPrefixReduce xs
      have firstStep :
          Derives edmundsFourSixtyBasis
            (anchor ++ wordOfPrefixFinal (x :: xs) final)
            (anchor ++ wordOfPrefixFinal (x :: reduced) final) := by
        simpa [wordOfPrefixFinal, reduced, Word.append_assoc] using
          suffixNormal
      by_cases hx : x ∈ reduced
      · have reducedEq :
            finalMarkerPrefixReduce (x :: xs) = reduced := by
          simp [finalMarkerPrefixReduce, reduced, hx]
        rw [reducedEq]
        exact Derives.trans firstStep <|
          edmundsFourSixtyDerivesDeleteDuplicate
            anchor x reduced final hx
      · have reducedEq :
            finalMarkerPrefixReduce (x :: xs) = x :: reduced := by
          simp [finalMarkerPrefixReduce, reduced, hx]
        rw [reducedEq]
        exact firstStep
termination_by
  _ pref _ => pref.length

/-- Preserve the first variable and retain one prefix copy of every other
variable. -/
def edmundsFourSixtyPrefixNormal : List Nat → List Nat
  | [] => []
  | head :: tail =>
      head :: (finalMarkerPrefixReduce tail).erase head

theorem edmundsFourSixtyPrefixNormal_nodup (pref : List Nat) :
    (edmundsFourSixtyPrefixNormal pref).Nodup := by
  cases pref with
  | nil =>
      exact List.nodup_nil
  | cons head tail =>
      have reducedNodup := finalMarkerPrefixReduce_nodup tail
      exact List.nodup_cons.mpr
        ⟨by simp [reducedNodup.mem_erase_iff],
          reducedNodup.erase head⟩

theorem edmundsFourSixtyPrefixNormal_mem
    (z : Nat) (pref : List Nat) :
    z ∈ edmundsFourSixtyPrefixNormal pref ↔ z ∈ pref := by
  cases pref with
  | nil =>
      simp [edmundsFourSixtyPrefixNormal]
  | cons head tail =>
      have reducedNodup := finalMarkerPrefixReduce_nodup tail
      by_cases hz : z = head
      · subst z
        simp [edmundsFourSixtyPrefixNormal]
      · simp [edmundsFourSixtyPrefixNormal, hz,
          reducedNodup.mem_erase_iff,
          finalMarkerPrefixReduce_mem]

private theorem edmundsFourSixtyDerivesNormalizeNonemptyPrefix
    (head : Nat) (tail : List Nat) (final : Nat) :
    Derives edmundsFourSixtyBasis
      (wordOfPrefixFinal (head :: tail) final)
      (wordOfPrefixFinal
        (edmundsFourSixtyPrefixNormal (head :: tail)) final) := by
  let reduced := finalMarkerPrefixReduce tail
  have dedup :=
    edmundsFourSixtyDerivesDedupUnderAnchor
      (Word.singleton head) tail final
  have firstStep :
      Derives edmundsFourSixtyBasis
        (wordOfPrefixFinal (head :: tail) final)
        (wordOfPrefixFinal (head :: reduced) final) := by
    simpa [wordOfPrefixFinal, reduced, Word.append_assoc] using dedup
  by_cases hhead : head ∈ reduced
  · have expose : reduced.Perm (head :: reduced.erase head) :=
      List.perm_cons_erase hhead
    have arrange :=
      edmundsFourSixtyDerivesPrefixPermutation
        (Word.singleton head) expose final
    have contract :=
      edmundsFourSixtyDerivesLeftContraction
        (Word.singleton head)
        (wordOfPrefixFinal (reduced.erase head) final)
    exact Derives.trans firstStep <|
      Derives.trans
        (by simpa [wordOfPrefixFinal, Word.append_assoc] using arrange)
        (by
          simpa [edmundsFourSixtyPrefixNormal, reduced,
            wordOfPrefixFinal, Word.append_assoc] using contract)
  · have eraseEq : reduced.erase head = reduced :=
      by simp [hhead]
    simpa [edmundsFourSixtyPrefixNormal, reduced, eraseEq] using
      firstStep

theorem edmundsFourSixtyDerivesNormal (w : Word Nat) :
    let split := splitPrefixFinal w
    Derives edmundsFourSixtyBasis w
      (wordOfPrefixFinal
        (edmundsFourSixtyPrefixNormal split.1) split.2) := by
  dsimp
  have reconstruct := wordOfPrefixFinal_split w
  cases hp : (splitPrefixFinal w).1 with
  | nil =>
      have reconstruct' :
          wordOfPrefixFinal [] (splitPrefixFinal w).2 = w := by
        simpa [hp] using reconstruct
      simpa [edmundsFourSixtyPrefixNormal, reconstruct'] using
        (Derives.refl w : Derives edmundsFourSixtyBasis w w)
  | cons head tail =>
      have normal :=
        edmundsFourSixtyDerivesNormalizeNonemptyPrefix
          head tail (splitPrefixFinal w).2
      have reconstruct' :
          wordOfPrefixFinal (head :: tail) (splitPrefixFinal w).2 = w := by
        simpa [hp] using reconstruct
      rw [reconstruct'] at normal
      exact normal

/-- The final switch law followed by the reverse final gather law changes
one repeated final marker to another prefix marker without changing the
prefix. -/
theorem edmundsFourSixtyDerivesLocalRepeatedFinalSwitch
    (p u v : Word Nat) :
    Derives edmundsFourSixtyBasis
      (((p ++ u) ++ v) ++ v) (((p ++ u) ++ v) ++ u) :=
  Derives.trans
    (edmundsFourSixtyDerivesFinalSwitch p u v)
    (Derives.symm (edmundsFourSixtyDerivesFinalGather p u v))

private theorem edmundsFourSixtyPerm_two_to_end
    (a b : Nat) :
    ∀ xs : List Nat, (a :: b :: xs).Perm (xs ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x
            (edmundsFourSixtyPerm_two_to_end a b xs)

private theorem edmundsFourSixtyDerivesRepeatedFinalSwitch
    (head : Nat) (tail : List Nat) (oldFinal newFinal : Nat)
    (hold : oldFinal ∈ head :: tail)
    (hnew : newFinal ∈ head :: tail) :
    Derives edmundsFourSixtyBasis
      (wordOfPrefixFinal (head :: tail) oldFinal)
      (wordOfPrefixFinal (head :: tail) newFinal) := by
  by_cases finals : oldFinal = newFinal
  · subst newFinal
    exact Derives.refl _
  · let augmented := head :: tail
    have inserted :
        Derives edmundsFourSixtyBasis
          (wordOfPrefixFinal (head :: tail) oldFinal)
          (wordOfPrefixFinal (head :: augmented) oldFinal) := by
      have h :=
        Derives.symm <|
          edmundsFourSixtyDerivesLeftContraction
            (Word.singleton head)
            (wordOfPrefixFinal tail oldFinal)
      simpa [augmented, wordOfPrefixFinal, Word.append_assoc] using h
    have holdAug : oldFinal ∈ augmented := by
      simpa [augmented] using hold
    have hnewAug : newFinal ∈ augmented := by
      simpa [augmented] using hnew
    have oldInErase : oldFinal ∈ augmented.erase newFinal := by
      simpa [finals] using holdAug
    let remainder := (augmented.erase newFinal).erase oldFinal
    have arrangeFront :
        augmented.Perm (newFinal :: oldFinal :: remainder) :=
      (List.perm_cons_erase hnewAug).trans <|
        List.Perm.cons newFinal <| by
          simpa [remainder] using List.perm_cons_erase oldInErase
    have arrange :
        augmented.Perm (remainder ++ [newFinal, oldFinal]) :=
      arrangeFront.trans <|
        edmundsFourSixtyPerm_two_to_end
          newFinal oldFinal remainder
    have arranged :=
      edmundsFourSixtyDerivesPrefixPermutation
        (Word.singleton head) arrange oldFinal
    have switched :
        Derives edmundsFourSixtyBasis
          (wordOfPrefixFinal
            (head :: remainder ++ [newFinal, oldFinal]) oldFinal)
          (wordOfPrefixFinal
            (head :: remainder ++ [newFinal, oldFinal]) newFinal) := by
      let anchor : Word Nat := ⟨head, remainder⟩
      have h :=
        edmundsFourSixtyDerivesLocalRepeatedFinalSwitch
          anchor (Word.singleton newFinal) (Word.singleton oldFinal)
      have sourceEq :
          wordOfPrefixFinal
              (head :: remainder ++ [newFinal, oldFinal]) oldFinal =
            (((anchor ++ Word.singleton newFinal) ++
              Word.singleton oldFinal) ++ Word.singleton oldFinal) := by
        apply Word.toList_injective
        rw [toList_wordOfPrefixFinal]
        simp [anchor, Word.toList, List.append_assoc]
      have targetEq :
          wordOfPrefixFinal
              (head :: remainder ++ [newFinal, oldFinal]) newFinal =
            (((anchor ++ Word.singleton newFinal) ++
              Word.singleton oldFinal) ++ Word.singleton newFinal) := by
        apply Word.toList_injective
        rw [toList_wordOfPrefixFinal]
        simp [anchor, Word.toList, List.append_assoc]
      rw [sourceEq, targetEq]
      exact h
    have restored :=
      edmundsFourSixtyDerivesPrefixPermutation
        (Word.singleton head) arrange.symm newFinal
    have deleted :
        Derives edmundsFourSixtyBasis
          (wordOfPrefixFinal (head :: augmented) newFinal)
          (wordOfPrefixFinal (head :: tail) newFinal) := by
      have h :=
        edmundsFourSixtyDerivesLeftContraction
          (Word.singleton head)
          (wordOfPrefixFinal tail newFinal)
      simpa [augmented, wordOfPrefixFinal, Word.append_assoc] using h
    exact Derives.trans inserted <|
      Derives.trans
        (by simpa [wordOfPrefixFinal, Word.append_assoc] using arranged) <|
      Derives.trans switched <|
      Derives.trans
        (by simpa [wordOfPrefixFinal, Word.append_assoc] using restored)
        deleted

private def edmundsFourSixtyFinalSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 2

theorem edmundsFourSixtyEval_finalSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourSixty.semigroup.eval
        (edmundsFourSixtyFinalSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 4) else
        if final = z then (1 : Fin 4) else (2 : Fin 4) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, edmundsFourSixtyFinalSeparator]
      · simp [wordOfPrefixFinal, edmundsFourSixtyFinalSeparator,
          hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      change
        edmundsFourSixtyMul
            (edmundsFourSixtyFinalSeparator z x)
            (if z ∈ xs then (0 : Fin 4) else
              if final = z then (1 : Fin 4) else (2 : Fin 4)) =
          if z ∈ x :: xs then (0 : Fin 4) else
            if final = z then (1 : Fin 4) else (2 : Fin 4)
      by_cases hx : x = z
      · subst x
        simp [edmundsFourSixtyFinalSeparator, edmundsFourSixtyMul]
      · by_cases hp : z ∈ xs <;>
          by_cases hf : final = z <;>
            simp [edmundsFourSixtyFinalSeparator, hx, Ne.symm hx,
              edmundsFourSixtyMul, hp, hf]

theorem edmundsFourSixtyEval_finalSeparator_eq_one_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourSixty.semigroup.eval
        (edmundsFourSixtyFinalSeparator z)
        (wordOfPrefixFinal pref final) = (1 : Fin 4) ↔
      final = z ∧ z ∉ pref := by
  rw [edmundsFourSixtyEval_finalSeparator]
  by_cases hp : z ∈ pref
  · simp [hp]
  · by_cases hf : final = z
    · simp [hp, hf]
    · simp [hp, hf]

private def edmundsFourSixtyFirstSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem edmundsFourSixtyMul_two_ne_three (b : Fin 4) :
    edmundsFourSixtyMul 2 b ≠ 3 := by
  decide +revert

theorem edmundsFourSixtyEval_firstSeparator_eq_three_iff
    (z head : Nat) (tail : List Nat) (final : Nat) :
    edmundsFourSixty.semigroup.eval
        (edmundsFourSixtyFirstSeparator z)
        (wordOfPrefixFinal (head :: tail) final) = (3 : Fin 4) ↔
      head = z := by
  rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
    Semigroup.eval_singleton]
  by_cases hhead : head = z
  · subst head
    simp [edmundsFourSixtyFirstSeparator, edmundsFourSixty,
      FiniteTable.semigroup, edmundsFourSixtyMul]
  · rw [show edmundsFourSixtyFirstSeparator z head = (2 : Fin 4) by
      simp [edmundsFourSixtyFirstSeparator, hhead]]
    simp only [edmundsFourSixty, FiniteTable.semigroup]
    change edmundsFourSixtyMul 2 _ = 3 ↔ head = z
    exact iff_of_false
      (edmundsFourSixtyMul_two_ne_three _)
      hhead

private theorem edmundsFourSixtyMul_initialGather
    (a b c : Fin 4) :
    edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a b) a) c =
      edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a a) b) c := by
  decide +revert

private theorem edmundsFourSixtyMul_finalGather
    (a b c : Fin 4) :
    edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a b) c) b =
      edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a c) b) b := by
  decide +revert

private theorem edmundsFourSixtyMul_leftContraction
    (a b : Fin 4) :
    edmundsFourSixtyMul
        (edmundsFourSixtyMul a a) b =
      edmundsFourSixtyMul a b := by
  decide +revert

private theorem edmundsFourSixtyMul_finalSwitch
    (a b c : Fin 4) :
    edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a b) c) c =
      edmundsFourSixtyMul
        (edmundsFourSixtyMul
          (edmundsFourSixtyMul a c) b) b := by
  decide +revert

theorem edmundsFourSixtyBasis_models :
    Models edmundsFourSixty.semigroup edmundsFourSixtyBasis := by
  intro e he
  simp only [edmundsFourSixtyBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    exact edmundsFourSixtyMul_initialGather
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    exact edmundsFourSixtyMul_finalGather
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    exact edmundsFourSixtyMul_leftContraction
      (valuation 0) (valuation 1)
  · intro valuation
    exact edmundsFourSixtyMul_finalSwitch
      (valuation 0) (valuation 1) (valuation 2)

private theorem edmundsFourSixtyNodupPerm
    {xs ys : List Nat} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  rw [hxs.count, hys.count]
  simp only [hmem z]

private theorem edmundsFourSixtyNormalizedDerives
    (prefix₁ prefix₂ : List Nat) (final₁ final₂ : Nat)
    (nodup₁ : prefix₁.Nodup) (nodup₂ : prefix₂.Nodup)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        edmundsFourSixty.semigroup.eval valuation
            (wordOfPrefixFinal prefix₁ final₁) =
          edmundsFourSixty.semigroup.eval valuation
            (wordOfPrefixFinal prefix₂ final₂)) :
    Derives edmundsFourSixtyBasis
      (wordOfPrefixFinal prefix₁ final₁)
      (wordOfPrefixFinal prefix₂ final₂) := by
  cases prefix₁ with
  | nil =>
      cases prefix₂ with
      | nil =>
          have finals : final₁ = final₂ := by
            apply Decidable.byContradiction
            intro hne
            have h := equalEval
              (edmundsFourSixtyFinalSeparator final₁)
            rw [edmundsFourSixtyEval_finalSeparator,
              edmundsFourSixtyEval_finalSeparator] at h
            simp [Ne.symm hne] at h
          subst final₂
          exact Derives.refl _
      | cons y ys =>
          have h := equalEval
            (edmundsFourSixtyFinalSeparator y)
          rw [edmundsFourSixtyEval_finalSeparator,
            edmundsFourSixtyEval_finalSeparator] at h
          simp only [List.not_mem_nil, if_false, List.mem_cons,
            true_or, if_true] at h
          split at h
          · exact False.elim ((by decide : (1 : Fin 4) ≠ 0) h)
          · exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
  | cons x xs =>
      cases prefix₂ with
      | nil =>
          have h := equalEval
            (edmundsFourSixtyFinalSeparator x)
          rw [edmundsFourSixtyEval_finalSeparator,
            edmundsFourSixtyEval_finalSeparator] at h
          simp only [List.mem_cons, true_or, if_true,
            List.not_mem_nil, if_false] at h
          split at h
          · exact False.elim ((by decide : (0 : Fin 4) ≠ 1) h)
          · exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
      | cons y ys =>
          let leftPrefix := x :: xs
          let rightPrefix := y :: ys
          have prefixMem :
              ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix := by
            intro z
            have h := equalEval
              (edmundsFourSixtyFinalSeparator z)
            rw [edmundsFourSixtyEval_finalSeparator,
              edmundsFourSixtyEval_finalSeparator] at h
            constructor
            · intro hz
              apply Decidable.byContradiction
              intro hnz
              rw [if_pos hz, if_neg hnz] at h
              split at h <;> contradiction
            · intro hz
              apply Decidable.byContradiction
              intro hnz
              rw [if_neg hnz, if_pos hz] at h
              split at h <;> contradiction
          have heads : x = y := by
            have h := equalEval
              (edmundsFourSixtyFirstSeparator x)
            have leftThree :
                edmundsFourSixty.semigroup.eval
                    (edmundsFourSixtyFirstSeparator x)
                    (wordOfPrefixFinal leftPrefix final₁) =
                  (3 : Fin 4) :=
              (edmundsFourSixtyEval_firstSeparator_eq_three_iff
                x x xs final₁).2 rfl
            have rightThree := h.symm.trans leftThree
            exact
              (edmundsFourSixtyEval_firstSeparator_eq_three_iff
                x y ys final₂).1 rightThree |>.symm
          subst y
          have xsNodup : xs.Nodup :=
            (List.nodup_cons.mp nodup₁).2
          have ysNodup : ys.Nodup :=
            (List.nodup_cons.mp nodup₂).2
          have tailMem : ∀ z, z ∈ xs ↔ z ∈ ys := by
            intro z
            by_cases hz : z = x
            · subst z
              exact iff_of_false
                (List.nodup_cons.mp nodup₁).1
                (List.nodup_cons.mp nodup₂).1
            · have h := prefixMem z
              simpa [leftPrefix, rightPrefix, hz] using h
          have tailPerm : xs.Perm ys :=
            edmundsFourSixtyNodupPerm xsNodup ysNodup tailMem
          have prefixDerivation (final : Nat) :
              Derives edmundsFourSixtyBasis
                (wordOfPrefixFinal leftPrefix final)
                (wordOfPrefixFinal rightPrefix final) := by
            simpa [leftPrefix, rightPrefix, wordOfPrefixFinal,
              Word.append_assoc] using
              edmundsFourSixtyDerivesPrefixPermutation
                (Word.singleton x) tailPerm final
          have simpleFinalIff :
              ∀ z,
                (final₁ = z ∧ z ∉ leftPrefix) ↔
                  (final₂ = z ∧ z ∉ rightPrefix) := by
            intro z
            have evaluated := equalEval
              (edmundsFourSixtyFinalSeparator z)
            constructor
            · intro h
              exact
                (edmundsFourSixtyEval_finalSeparator_eq_one_iff
                  z rightPrefix final₂).1 <|
                    evaluated.symm.trans <|
                      (edmundsFourSixtyEval_finalSeparator_eq_one_iff
                        z leftPrefix final₁).2 h
            · intro h
              exact
                (edmundsFourSixtyEval_finalSeparator_eq_one_iff
                  z leftPrefix final₁).1 <|
                    evaluated.trans <|
                      (edmundsFourSixtyEval_finalSeparator_eq_one_iff
                        z rightPrefix final₂).2 h
          by_cases repeated₁ : final₁ ∈ leftPrefix
          · have repeated₂ : final₂ ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro simple₂
              have leftSimple :=
                (simpleFinalIff final₂).2 ⟨rfl, simple₂⟩
              exact leftSimple.2 <| by
                simpa [leftSimple.1] using repeated₁
            have final₂InLeft : final₂ ∈ leftPrefix :=
              (prefixMem final₂).2 repeated₂
            exact Derives.trans
              (edmundsFourSixtyDerivesRepeatedFinalSwitch
                x xs final₁ final₂ repeated₁ final₂InLeft) <|
              prefixDerivation final₂
          · have final₁NotRight : final₁ ∉ rightPrefix := by
              intro hmem
              exact repeated₁ ((prefixMem final₁).2 hmem)
            have finals : final₁ = final₂ := by
              apply Decidable.byContradiction
              intro hne
              have h := equalEval
                (edmundsFourSixtyFinalSeparator final₁)
              rw [edmundsFourSixtyEval_finalSeparator,
                edmundsFourSixtyEval_finalSeparator] at h
              rw [if_neg repeated₁, if_neg final₁NotRight] at h
              simp [Ne.symm hne] at h
            subst final₂
            exact prefixDerivation final₁

/-- Unrestricted completeness over `Nat` variables. Normal forms retain the
exact first variable, the support, and a final marker exactly when the final
variable is simple. -/
theorem edmundsFourSixtyBasis_complete :
    BasisFor edmundsFourSixty.semigroup
      edmundsFourSixtyBasis := by
  refine ⟨edmundsFourSixtyBasis_models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  let lhsPrefix := edmundsFourSixtyPrefixNormal lhsSplit.1
  let rhsPrefix := edmundsFourSixtyPrefixNormal rhsSplit.1
  have lhsNormal := edmundsFourSixtyDerivesNormal e.lhs
  have rhsNormal := edmundsFourSixtyDerivesNormal e.rhs
  dsimp only at lhsNormal rhsNormal
  change
    Derives edmundsFourSixtyBasis e.lhs
      (wordOfPrefixFinal lhsPrefix lhsSplit.2) at lhsNormal
  change
    Derives edmundsFourSixtyBasis e.rhs
      (wordOfPrefixFinal rhsPrefix rhsSplit.2) at rhsNormal
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        edmundsFourSixty.semigroup.eval valuation
            (wordOfPrefixFinal lhsPrefix lhsSplit.2) =
          edmundsFourSixty.semigroup.eval valuation
            (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound edmundsFourSixtyBasis_models valuation
    have rhsSound :=
      rhsNormal.sound edmundsFourSixtyBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have normalizedDerivation :=
    edmundsFourSixtyNormalizedDerives
      lhsPrefix rhsPrefix lhsSplit.2 rhsSplit.2
      (edmundsFourSixtyPrefixNormal_nodup lhsSplit.1)
      (edmundsFourSixtyPrefixNormal_nodup rhsSplit.1)
      normalizedEval
  exact Derives.trans lhsNormal <|
    Derives.trans normalizedDerivation (Derives.symm rhsNormal)

def edmundsFourSixtyOppositeBasis : List (Identity Nat) :=
  reversedBasis edmundsFourSixtyBasis

theorem edmundsFourSixtyOppositeBasis_complete :
    BasisFor edmundsFourSixty.semigroup.opposite
      edmundsFourSixtyOppositeBasis := by
  simpa [edmundsFourSixtyOppositeBasis] using
    edmundsFourSixtyBasis_complete.oppositeReversed

end SemigroupBasis.Examples

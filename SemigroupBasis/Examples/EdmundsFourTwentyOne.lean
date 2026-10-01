import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,1,3],[1,2,3,4]]`. -/
def edmundsFourTwentyOneMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then (if b = 3 then 2 else 0) else b

/-- The root catalogue representative `S4_21`. -/
def edmundsFourTwentyOne : FiniteTable where
  order := 4
  mul := edmundsFourTwentyOneMul
  assoc := by decide

def edmundsFourTwentyOneXYZ : Word Nat := ⟨0, [1, 2]⟩
def edmundsFourTwentyOneYXZ : Word Nat := ⟨1, [0, 2]⟩
def edmundsFourTwentyOneXX : Word Nat := ⟨0, [0]⟩
def edmundsFourTwentyOneXXX : Word Nat := ⟨0, [0, 0]⟩
def edmundsFourTwentyOneXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def edmundsFourTwentyOneYYXX : Word Nat := ⟨1, [1, 0, 0]⟩

def edmundsFourTwentyOnePrefixCommutationLaw : Identity Nat :=
  ⟨edmundsFourTwentyOneXYZ, edmundsFourTwentyOneYXZ⟩

def edmundsFourTwentyOnePowerLaw : Identity Nat :=
  ⟨edmundsFourTwentyOneXX, edmundsFourTwentyOneXXX⟩

def edmundsFourTwentyOneSquareCommutationLaw : Identity Nat :=
  ⟨edmundsFourTwentyOneXXYY, edmundsFourTwentyOneYYXX⟩

/-- Edmunds' complete basis for `S4_21`:
`xyz = yxz`, `xx = xxx`, `xxyy = yyxx`. -/
def edmundsFourTwentyOneBasis : List (Identity Nat) :=
  [edmundsFourTwentyOnePrefixCommutationLaw,
    edmundsFourTwentyOnePowerLaw,
    edmundsFourTwentyOneSquareCommutationLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem edmundsFourTwentyOneDerivesPrefixSwap
    (u v q : Word Nat) :
    Derives edmundsFourTwentyOneBasis
      ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have hbase :
      Derives edmundsFourTwentyOneBasis
        edmundsFourTwentyOneXYZ edmundsFourTwentyOneYXZ :=
    Derives.fromBasis (e := edmundsFourTwentyOnePrefixCommutationLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v q)
  simpa [edmundsFourTwentyOneBasis,
    edmundsFourTwentyOnePrefixCommutationLaw,
    edmundsFourTwentyOneXYZ, edmundsFourTwentyOneYXZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourTwentyOneDerivesTripleContraction (u : Word Nat) :
    Derives edmundsFourTwentyOneBasis
      ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives edmundsFourTwentyOneBasis
        edmundsFourTwentyOneXXX edmundsFourTwentyOneXX :=
    Derives.symm <|
      Derives.fromBasis (e := edmundsFourTwentyOnePowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [edmundsFourTwentyOneBasis, edmundsFourTwentyOnePowerLaw,
    edmundsFourTwentyOneXXX, edmundsFourTwentyOneXX,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourTwentyOneDerivesSquareSwitch (u v : Word Nat) :
    Derives edmundsFourTwentyOneBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives edmundsFourTwentyOneBasis
        edmundsFourTwentyOneXXYY edmundsFourTwentyOneYYXX :=
    Derives.fromBasis (e := edmundsFourTwentyOneSquareCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [edmundsFourTwentyOneBasis,
    edmundsFourTwentyOneSquareCommutationLaw,
    edmundsFourTwentyOneXXYY, edmundsFourTwentyOneYYXX,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem edmundsFourTwentyOneDerivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat} (hperm : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction hperm with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        edmundsFourTwentyOneDerivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private theorem edmundsFourTwentyOneContractLeadingTriple
    (x final : Nat) (rest : List Nat) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal (x :: x :: x :: rest) final)
      (wordOfPrefixFinal (x :: x :: rest) final) := by
  have h :=
    Derives.appendRight
      (edmundsFourTwentyOneDerivesTripleContraction
        (Word.singleton x))
      (wordOfPrefixFinal rest final)
  simpa [wordOfPrefixFinal, Word.append_assoc] using h

private theorem edmundsFourTwentyOneContractFinalTriple
    (rest : List Nat) (x : Nat) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal (rest ++ [x, x]) x)
      (wordOfPrefixFinal (rest ++ [x]) x) := by
  induction rest with
  | nil =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        edmundsFourTwentyOneDerivesTripleContraction
          (Word.singleton x)
  | cons y ys ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton y) ih

private theorem edmundsFourTwentyOneDeleteThirdPrefixCopy
    (final x : Nat) (reduced : List Nat)
    (hcount : reduced.count x = 2) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal (x :: reduced) final)
      (wordOfPrefixFinal reduced final) := by
  let remainder := (reduced.erase x).erase x
  have sourcePerm :
      (x :: reduced).Perm (x :: x :: x :: remainder) := by
    rw [List.perm_iff_count]
    intro z
    by_cases hz : z = x
    · subst z
      have firstErase : (reduced.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((reduced.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp [remainder, hcount, secondErase]
    · simp [remainder, hz, Ne.symm hz]
  have targetPerm :
      reduced.Perm (x :: x :: remainder) := by
    rw [List.perm_iff_count]
    intro z
    by_cases hz : z = x
    · subst z
      have firstErase : (reduced.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((reduced.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp [remainder, hcount, secondErase]
    · simp [remainder, hz, Ne.symm hz]
  exact Derives.trans
    (edmundsFourTwentyOneDerivesPrefixPermutation sourcePerm final) <|
    Derives.trans
      (edmundsFourTwentyOneContractLeadingTriple x final remainder)
      (edmundsFourTwentyOneDerivesPrefixPermutation
        targetPerm.symm final)

private theorem edmundsFourTwentyOneDeleteRepeatedFinal
    (final : Nat) (reduced : List Nat)
    (hcount : reduced.count final = 1) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal (final :: reduced) final)
      (wordOfPrefixFinal reduced final) := by
  let remainder := reduced.erase final
  have sourcePerm :
      (final :: reduced).Perm (remainder ++ [final, final]) := by
    rw [List.perm_iff_count]
    intro z
    by_cases hz : z = final
    · subst z
      have eraseCount : (reduced.erase final).count final = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  have targetPerm :
      reduced.Perm (remainder ++ [final]) := by
    rw [List.perm_iff_count]
    intro z
    by_cases hz : z = final
    · subst z
      have eraseCount : (reduced.erase final).count final = 0 := by
        rw [List.count_erase_self, hcount]
      simp [remainder, hcount, eraseCount]
    · simp [remainder, hz, Ne.symm hz]
  exact Derives.trans
    (edmundsFourTwentyOneDerivesPrefixPermutation sourcePerm final) <|
    Derives.trans
      (edmundsFourTwentyOneContractFinalTriple remainder final)
      (edmundsFourTwentyOneDerivesPrefixPermutation
        targetPerm.symm final)

/-- Retain at most one prefix copy of the final variable and at most two
copies of every other variable. -/
def edmundsFourTwentyOnePrefixLimit (final x : Nat) : Nat :=
  if x = final then 1 else 2

def edmundsFourTwentyOnePrefixReduce (final : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := edmundsFourTwentyOnePrefixReduce final xs
      if reduced.count x < edmundsFourTwentyOnePrefixLimit final x then
        x :: reduced
      else
        reduced

theorem count_edmundsFourTwentyOnePrefixReduce
    (final z : Nat) (pref : List Nat) :
    (edmundsFourTwentyOnePrefixReduce final pref).count z =
      min (pref.count z) (edmundsFourTwentyOnePrefixLimit final z) := by
  induction pref with
  | nil =>
      simp [edmundsFourTwentyOnePrefixReduce,
        edmundsFourTwentyOnePrefixLimit]
  | cons x xs ih =>
      simp only [edmundsFourTwentyOnePrefixReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hx : x = final <;>
            simp [edmundsFourTwentyOnePrefixLimit, hx] at hcount ⊢ <;>
            omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hx : x = final <;>
            simp [edmundsFourTwentyOnePrefixLimit, hx] at hcount ⊢ <;>
            omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem edmundsFourTwentyOneDerivesNormalizePrefix :
    ∀ (pref : List Nat) (final : Nat),
      Derives edmundsFourTwentyOneBasis
        (wordOfPrefixFinal pref final)
        (wordOfPrefixFinal
          (edmundsFourTwentyOnePrefixReduce final pref) final)
  | [], final => Derives.refl _
  | x :: xs, final => by
      have suffixNormal :=
        edmundsFourTwentyOneDerivesNormalizePrefix xs final
      have prefixed :=
        Derives.prepend (Word.singleton x) suffixNormal
      let reduced := edmundsFourTwentyOnePrefixReduce final xs
      by_cases hcount :
          reduced.count x < edmundsFourTwentyOnePrefixLimit final x
      · have reducedEq :
            edmundsFourTwentyOnePrefixReduce final (x :: xs) =
              x :: reduced := by
          simp [edmundsFourTwentyOnePrefixReduce, reduced, hcount]
        rw [reducedEq]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have countLe :
            reduced.count x ≤
              edmundsFourTwentyOnePrefixLimit final x := by
          rw [show reduced =
            edmundsFourTwentyOnePrefixReduce final xs by rfl,
            count_edmundsFourTwentyOnePrefixReduce]
          exact Nat.min_le_right _ _
        have countEq :
            reduced.count x =
              edmundsFourTwentyOnePrefixLimit final x := by
          omega
        have reducedEq :
            edmundsFourTwentyOnePrefixReduce final (x :: xs) =
              reduced := by
          simp [edmundsFourTwentyOnePrefixReduce, reduced, hcount]
        rw [reducedEq]
        have firstStep :
            Derives edmundsFourTwentyOneBasis
              (wordOfPrefixFinal (x :: xs) final)
              (wordOfPrefixFinal (x :: reduced) final) := by
          simpa [wordOfPrefixFinal, reduced] using prefixed
        by_cases hx : x = final
        · subst x
          have finalCount : reduced.count final = 1 := by
            simpa [edmundsFourTwentyOnePrefixLimit] using countEq
          exact Derives.trans firstStep
            (edmundsFourTwentyOneDeleteRepeatedFinal
              final reduced finalCount)
        · have prefixCount : reduced.count x = 2 := by
            simpa [edmundsFourTwentyOnePrefixLimit, hx] using countEq
          exact Derives.trans firstStep
            (edmundsFourTwentyOneDeleteThirdPrefixCopy
              final x reduced prefixCount)
termination_by
  pref _ => pref.length

theorem edmundsFourTwentyOneDerivesNormal (w : Word Nat) :
    let split := splitPrefixFinal w
    Derives edmundsFourTwentyOneBasis w
      (wordOfPrefixFinal
        (edmundsFourTwentyOnePrefixReduce split.2 split.1) split.2) := by
  dsimp
  have reconstruct := wordOfPrefixFinal_split w
  have normal :=
    edmundsFourTwentyOneDerivesNormalizePrefix
      (splitPrefixFinal w).1 (splitPrefixFinal w).2
  rw [reconstruct] at normal
  exact normal

theorem edmundsFourTwentyOneNormal_count
    (pref : List Nat) (final z : Nat) :
    (wordOfPrefixFinal
        (edmundsFourTwentyOnePrefixReduce final pref) final).toList.count z =
      min ((wordOfPrefixFinal pref final).toList.count z) 2 := by
  rw [toList_wordOfPrefixFinal, toList_wordOfPrefixFinal,
    List.count_append, List.count_append,
    count_edmundsFourTwentyOnePrefixReduce]
  by_cases hz : z = final
  · subst z
    simp [edmundsFourTwentyOnePrefixLimit]
    omega
  · have singletonCount : [final].count z = 0 := by
      simp [Ne.symm hz]
    rw [singletonCount]
    simp [edmundsFourTwentyOnePrefixLimit, hz]

private def edmundsFourTwentyOneCountState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n = 1 then 2 else 0

private def edmundsFourTwentyOneCountSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem edmundsFourTwentyOneMul_countState_two (n : Nat) :
    edmundsFourTwentyOneMul 2
        (edmundsFourTwentyOneCountState n) =
      edmundsFourTwentyOneCountState (n + 1) := by
  cases n with
  | zero =>
      simp [edmundsFourTwentyOneCountState,
        edmundsFourTwentyOneMul]
  | succ n =>
      cases n with
      | zero =>
          simp [edmundsFourTwentyOneCountState,
            edmundsFourTwentyOneMul]
      | succ n =>
          simp [edmundsFourTwentyOneCountState,
            edmundsFourTwentyOneMul]

private theorem edmundsFourTwentyOneMul_countState_three (n : Nat) :
    edmundsFourTwentyOneMul 3
        (edmundsFourTwentyOneCountState n) =
      edmundsFourTwentyOneCountState n := by
  simp [edmundsFourTwentyOneMul]

theorem edmundsFourTwentyOneEval_countSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentyOne.semigroup.eval
        (edmundsFourTwentyOneCountSeparator z)
        (wordOfPrefixFinal pref final) =
      edmundsFourTwentyOneCountState
        ((pref ++ [final]).count z) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, edmundsFourTwentyOneCountSeparator,
          edmundsFourTwentyOneCountState]
      · simp [wordOfPrefixFinal, edmundsFourTwentyOneCountSeparator,
          edmundsFourTwentyOneCountState, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      by_cases hx : x = z
      · subst x
        have countEq :
            (z :: xs ++ [final]).count z =
              1 + (xs ++ [final]).count z := by
          simp [List.count_append]
          omega
        rw [countEq]
        rw [show edmundsFourTwentyOneCountSeparator z z =
          (2 : Fin 4) by
            simp [edmundsFourTwentyOneCountSeparator]]
        change
          edmundsFourTwentyOneMul 2
              (edmundsFourTwentyOneCountState
                ((xs ++ [final]).count z)) =
            edmundsFourTwentyOneCountState
              (1 + (xs ++ [final]).count z)
        simpa [Nat.add_comm] using
          edmundsFourTwentyOneMul_countState_two
            ((xs ++ [final]).count z)
      · have countEq :
            (x :: xs ++ [final]).count z =
              (xs ++ [final]).count z := by
          simp [hx]
        rw [countEq]
        rw [show edmundsFourTwentyOneCountSeparator z x =
          (3 : Fin 4) by
            simp [edmundsFourTwentyOneCountSeparator, hx]]
        exact edmundsFourTwentyOneMul_countState_three _

private theorem edmundsFourTwentyOneCountState_eq_implies_capped
    {m n : Nat}
    (h : edmundsFourTwentyOneCountState m =
      edmundsFourTwentyOneCountState n) :
    min m 2 = min n 2 := by
  cases m with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero =>
              simp [edmundsFourTwentyOneCountState] at h
          | succ n =>
              simp [edmundsFourTwentyOneCountState] at h
  | succ m =>
      cases m with
      | zero =>
          cases n with
          | zero =>
              simp [edmundsFourTwentyOneCountState] at h
          | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                  simp [edmundsFourTwentyOneCountState] at h
      | succ m =>
          cases n with
          | zero =>
              simp [edmundsFourTwentyOneCountState] at h
          | succ n =>
              cases n with
              | zero =>
                  simp [edmundsFourTwentyOneCountState] at h
              | succ n =>
                  simp

theorem edmundsFourTwentyOneValid_capped_count_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy edmundsFourTwentyOne.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 := by
  intro z
  have evaluated := valid (edmundsFourTwentyOneCountSeparator z)
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
    wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
    wordOfPrefixFinal_split e.rhs
  rw [← lhsReconstruct, ← rhsReconstruct,
    edmundsFourTwentyOneEval_countSeparator,
    edmundsFourTwentyOneEval_countSeparator] at evaluated
  have capped :=
    edmundsFourTwentyOneCountState_eq_implies_capped evaluated
  rw [← lhsReconstruct, ← rhsReconstruct,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]
  exact capped

private def edmundsFourTwentyOneFinalSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

theorem edmundsFourTwentyOneEval_finalSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentyOne.semigroup.eval
        (edmundsFourTwentyOneFinalSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 4) else
        if final = z then (1 : Fin 4) else (3 : Fin 4) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal, edmundsFourTwentyOneFinalSeparator]
      · simp [wordOfPrefixFinal, edmundsFourTwentyOneFinalSeparator,
          hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      change
        edmundsFourTwentyOneMul
            (edmundsFourTwentyOneFinalSeparator z x)
            (if z ∈ xs then (0 : Fin 4) else
              if final = z then (1 : Fin 4) else (3 : Fin 4)) =
          if z ∈ x :: xs then (0 : Fin 4) else
            if final = z then (1 : Fin 4) else (3 : Fin 4)
      by_cases hx : x = z
      · subst x
        simp [edmundsFourTwentyOneFinalSeparator,
          edmundsFourTwentyOneMul]
      · simp [edmundsFourTwentyOneFinalSeparator, hx, Ne.symm hx,
          edmundsFourTwentyOneMul]

theorem edmundsFourTwentyOneEval_finalSeparator_eq_one_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentyOne.semigroup.eval
        (edmundsFourTwentyOneFinalSeparator z)
        (wordOfPrefixFinal pref final) = (1 : Fin 4) ↔
      final = z ∧ z ∉ pref := by
  rw [edmundsFourTwentyOneEval_finalSeparator]
  by_cases hp : z ∈ pref
  · simp [hp]
  · by_cases hf : final = z
    · simp [hp, hf]
    · simp [hp, hf]

private theorem edmundsFourTwentyOneMul_prefixCommutation
    (a b c : Fin 4) :
    edmundsFourTwentyOneMul
        (edmundsFourTwentyOneMul a b) c =
      edmundsFourTwentyOneMul
        (edmundsFourTwentyOneMul b a) c := by
  decide +revert

private theorem edmundsFourTwentyOneMul_power (a : Fin 4) :
    edmundsFourTwentyOneMul a a =
      edmundsFourTwentyOneMul
        (edmundsFourTwentyOneMul a a) a := by
  decide +revert

private theorem edmundsFourTwentyOneMul_squareCommutation
    (a b : Fin 4) :
    edmundsFourTwentyOneMul
        (edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul a a) b) b =
      edmundsFourTwentyOneMul
        (edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul b b) a) a := by
  decide +revert

theorem edmundsFourTwentyOneBasis_models :
    Models edmundsFourTwentyOne.semigroup
      edmundsFourTwentyOneBasis := by
  intro e he
  simp only [edmundsFourTwentyOneBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul (valuation 0) (valuation 1))
          (valuation 2) =
        edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul (valuation 1) (valuation 0))
          (valuation 2)
    exact edmundsFourTwentyOneMul_prefixCommutation
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      edmundsFourTwentyOneMul (valuation 0) (valuation 0) =
        edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul (valuation 0) (valuation 0))
          (valuation 0)
    exact edmundsFourTwentyOneMul_power (valuation 0)
  · intro valuation
    change
      edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul
            (edmundsFourTwentyOneMul (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 1) =
        edmundsFourTwentyOneMul
          (edmundsFourTwentyOneMul
            (edmundsFourTwentyOneMul (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0)
    exact edmundsFourTwentyOneMul_squareCommutation
      (valuation 0) (valuation 1)

private theorem edmundsFourTwentyOneSquareSwitchUnderPrefix
    (rest : List Nat) (oldFinal newFinal : Nat) :
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal (rest ++ [newFinal, newFinal, oldFinal])
        oldFinal)
      (wordOfPrefixFinal (rest ++ [oldFinal, oldFinal, newFinal])
        newFinal) := by
  induction rest with
  | nil =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        edmundsFourTwentyOneDerivesSquareSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal)
  | cons x xs ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton x) ih

private theorem edmundsFourTwentyOnePerm_three_to_end
    (a b c : Nat) (rest : List Nat) :
    (a :: b :: c :: rest).Perm (rest ++ [a, b, c]) := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

private theorem edmundsFourTwentyOneSwitchRepeatedFinal
    (pref : List Nat) (oldFinal newFinal : Nat)
    (hne : oldFinal ≠ newFinal)
    (holdCount : pref.count oldFinal = 1)
    (hnewCount : pref.count newFinal = 2) :
    let remainder :=
      ((pref.erase newFinal).erase newFinal).erase oldFinal
    Derives edmundsFourTwentyOneBasis
      (wordOfPrefixFinal pref oldFinal)
      (wordOfPrefixFinal
        (remainder ++ [oldFinal, oldFinal, newFinal]) newFinal) := by
  dsimp
  have hnewMem : newFinal ∈ pref :=
    List.count_pos_iff.mp (by omega)
  have firstNewCount :
      (pref.erase newFinal).count newFinal = 1 := by
    rw [List.count_erase_self, hnewCount]
  have hnewMemAfter : newFinal ∈ pref.erase newFinal :=
    List.count_pos_iff.mp (by omega)
  have oldCountAfterNew :
      (pref.erase newFinal).count oldFinal = 1 := by
    rw [List.count_erase_of_ne hne, holdCount]
  have oldCountAfterTwoNew :
      ((pref.erase newFinal).erase newFinal).count oldFinal = 1 := by
    rw [List.count_erase_of_ne hne, oldCountAfterNew]
  have holdMemAfter :
      oldFinal ∈ (pref.erase newFinal).erase newFinal :=
    List.count_pos_iff.mp (by omega)
  have arrangeFront :
      pref.Perm
        (newFinal :: newFinal :: oldFinal ::
          ((pref.erase newFinal).erase newFinal).erase oldFinal) :=
    (List.perm_cons_erase hnewMem).trans <|
      List.Perm.cons newFinal <|
        (List.perm_cons_erase hnewMemAfter).trans <|
          List.Perm.cons newFinal <|
            List.perm_cons_erase holdMemAfter
  have arrange :
      pref.Perm
        (((pref.erase newFinal).erase newFinal).erase oldFinal ++
          [newFinal, newFinal, oldFinal]) :=
    arrangeFront.trans <|
      edmundsFourTwentyOnePerm_three_to_end
        newFinal newFinal oldFinal _
  exact Derives.trans
    (edmundsFourTwentyOneDerivesPrefixPermutation
      arrange oldFinal)
    (edmundsFourTwentyOneSquareSwitchUnderPrefix
      (((pref.erase newFinal).erase newFinal).erase oldFinal)
      oldFinal newFinal)

private theorem edmundsFourTwentyOneSquareSwitch_full_perm
    (rest : List Nat) (oldFinal newFinal : Nat) :
    (rest ++ [newFinal, newFinal, oldFinal, oldFinal]).Perm
      (rest ++ [oldFinal, oldFinal, newFinal, newFinal]) := by
  apply List.Perm.append_left
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

/-- Completeness of Edmunds' basis for the exact `S4_21` catalogue table. -/
theorem edmundsFourTwentyOneBasis_complete :
    BasisFor edmundsFourTwentyOne.semigroup
      edmundsFourTwentyOneBasis := by
  refine ⟨edmundsFourTwentyOneBasis_models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  let lhsPrefix :=
    edmundsFourTwentyOnePrefixReduce lhsSplit.2 lhsSplit.1
  let rhsPrefix :=
    edmundsFourTwentyOnePrefixReduce rhsSplit.2 rhsSplit.1
  have lhsNormal := edmundsFourTwentyOneDerivesNormal e.lhs
  have rhsNormal := edmundsFourTwentyOneDerivesNormal e.rhs
  dsimp only at lhsNormal rhsNormal
  change
    Derives edmundsFourTwentyOneBasis e.lhs
      (wordOfPrefixFinal lhsPrefix lhsSplit.2) at lhsNormal
  change
    Derives edmundsFourTwentyOneBasis e.rhs
      (wordOfPrefixFinal rhsPrefix rhsSplit.2) at rhsNormal
  have cappedEq :=
    edmundsFourTwentyOneValid_capped_count_eq e valid
  have normalCountEq :
      ∀ z,
        (wordOfPrefixFinal lhsPrefix lhsSplit.2).toList.count z =
          (wordOfPrefixFinal rhsPrefix rhsSplit.2).toList.count z := by
    intro z
    change
      (wordOfPrefixFinal
          (edmundsFourTwentyOnePrefixReduce lhsSplit.2 lhsSplit.1)
          lhsSplit.2).toList.count z =
        (wordOfPrefixFinal
          (edmundsFourTwentyOnePrefixReduce rhsSplit.2 rhsSplit.1)
          rhsSplit.2).toList.count z
    rw [edmundsFourTwentyOneNormal_count,
      edmundsFourTwentyOneNormal_count]
    have lhsReconstruct := wordOfPrefixFinal_split e.lhs
    have rhsReconstruct := wordOfPrefixFinal_split e.rhs
    rw [lhsReconstruct, rhsReconstruct]
    exact cappedEq z
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        edmundsFourTwentyOne.semigroup.eval valuation
            (wordOfPrefixFinal lhsPrefix lhsSplit.2) =
          edmundsFourTwentyOne.semigroup.eval valuation
            (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound edmundsFourTwentyOneBasis_models valuation
    have rhsSound :=
      rhsNormal.sound edmundsFourTwentyOneBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have simpleFinalIff :
      ∀ z,
        (lhsSplit.2 = z ∧ z ∉ lhsPrefix) ↔
          (rhsSplit.2 = z ∧ z ∉ rhsPrefix) := by
    intro z
    have evaluated :=
      normalizedEval (edmundsFourTwentyOneFinalSeparator z)
    constructor
    · intro h
      exact (edmundsFourTwentyOneEval_finalSeparator_eq_one_iff
        z rhsPrefix rhsSplit.2).1 <|
          evaluated.symm.trans <|
            (edmundsFourTwentyOneEval_finalSeparator_eq_one_iff
              z lhsPrefix lhsSplit.2).2 h
    · intro h
      exact (edmundsFourTwentyOneEval_finalSeparator_eq_one_iff
        z lhsPrefix lhsSplit.2).1 <|
          evaluated.trans <|
            (edmundsFourTwentyOneEval_finalSeparator_eq_one_iff
              z rhsPrefix rhsSplit.2).2 h
  by_cases lhsRepeated : lhsSplit.2 ∈ lhsPrefix
  · have rhsRepeated : rhsSplit.2 ∈ rhsPrefix := by
      apply Decidable.byContradiction
      intro rhsSimple
      have lhsSimpleAtRight :=
        (simpleFinalIff rhsSplit.2).2 ⟨rfl, rhsSimple⟩
      exact lhsSimpleAtRight.2 <| by
        simpa [lhsSimpleAtRight.1] using lhsRepeated
    by_cases finalsEq : lhsSplit.2 = rhsSplit.2
    · rw [← finalsEq] at rhsNormal normalCountEq
      have prefixPerm : lhsPrefix.Perm rhsPrefix := by
        rw [List.perm_iff_count]
        intro z
        have counts := normalCountEq z
        simp only [toList_wordOfPrefixFinal,
          List.count_append] at counts
        simpa using counts
      exact Derives.trans lhsNormal <|
        Derives.trans
          (edmundsFourTwentyOneDerivesPrefixPermutation
            prefixPerm lhsSplit.2)
          (Derives.symm rhsNormal)
    · have lhsFinalCount : lhsPrefix.count lhsSplit.2 = 1 := by
        have positive := List.count_pos_iff.mpr lhsRepeated
        change
          (edmundsFourTwentyOnePrefixReduce
            lhsSplit.2 lhsSplit.1).count lhsSplit.2 = 1
        change
          0 < (edmundsFourTwentyOnePrefixReduce
            lhsSplit.2 lhsSplit.1).count lhsSplit.2 at positive
        rw [count_edmundsFourTwentyOnePrefixReduce] at positive ⊢
        simp [edmundsFourTwentyOnePrefixLimit] at positive ⊢
        omega
      have rhsFinalCount : rhsPrefix.count rhsSplit.2 = 1 := by
        have positive := List.count_pos_iff.mpr rhsRepeated
        change
          (edmundsFourTwentyOnePrefixReduce
            rhsSplit.2 rhsSplit.1).count rhsSplit.2 = 1
        change
          0 < (edmundsFourTwentyOnePrefixReduce
            rhsSplit.2 rhsSplit.1).count rhsSplit.2 at positive
        rw [count_edmundsFourTwentyOnePrefixReduce] at positive ⊢
        simp [edmundsFourTwentyOnePrefixLimit] at positive ⊢
        omega
      have newCount : lhsPrefix.count rhsSplit.2 = 2 := by
        have counts := normalCountEq rhsSplit.2
        simp only [toList_wordOfPrefixFinal,
          List.count_append] at counts
        simp [finalsEq, rhsFinalCount] at counts
        omega
      let remainder :=
        ((lhsPrefix.erase rhsSplit.2).erase rhsSplit.2).erase lhsSplit.2
      let switchedPrefix :=
        remainder ++ [lhsSplit.2, lhsSplit.2, rhsSplit.2]
      have switch :
          Derives edmundsFourTwentyOneBasis
            (wordOfPrefixFinal lhsPrefix lhsSplit.2)
            (wordOfPrefixFinal switchedPrefix rhsSplit.2) := by
        exact edmundsFourTwentyOneSwitchRepeatedFinal
          lhsPrefix lhsSplit.2 rhsSplit.2 finalsEq
          lhsFinalCount newCount
      have arrangedSource :
          lhsPrefix.Perm
            (remainder ++ [rhsSplit.2, rhsSplit.2, lhsSplit.2]) := by
        have hnewMem : rhsSplit.2 ∈ lhsPrefix :=
          List.count_pos_iff.mp (by omega)
        have firstNewCount :
            (lhsPrefix.erase rhsSplit.2).count rhsSplit.2 = 1 := by
          rw [List.count_erase_self, newCount]
        have hnewMemAfter :
            rhsSplit.2 ∈ lhsPrefix.erase rhsSplit.2 :=
          List.count_pos_iff.mp (by omega)
        have oldCountAfterNew :
            (lhsPrefix.erase rhsSplit.2).count lhsSplit.2 = 1 := by
          rw [List.count_erase_of_ne finalsEq, lhsFinalCount]
        have oldCountAfterTwoNew :
            ((lhsPrefix.erase rhsSplit.2).erase
              rhsSplit.2).count lhsSplit.2 = 1 := by
          rw [List.count_erase_of_ne finalsEq, oldCountAfterNew]
        have holdMemAfter :
            lhsSplit.2 ∈
              (lhsPrefix.erase rhsSplit.2).erase rhsSplit.2 :=
          List.count_pos_iff.mp (by omega)
        have front :
            lhsPrefix.Perm
              (rhsSplit.2 :: rhsSplit.2 :: lhsSplit.2 ::
                ((lhsPrefix.erase rhsSplit.2).erase
                  rhsSplit.2).erase lhsSplit.2) :=
          (List.perm_cons_erase hnewMem).trans <|
            List.Perm.cons rhsSplit.2 <|
              (List.perm_cons_erase hnewMemAfter).trans <|
                List.Perm.cons rhsSplit.2 <|
                  List.perm_cons_erase holdMemAfter
        exact front.trans <|
          edmundsFourTwentyOnePerm_three_to_end
            rhsSplit.2 rhsSplit.2 lhsSplit.2 _
      have sourceToSwitchedFull :
          (lhsPrefix ++ [lhsSplit.2]).Perm
            (switchedPrefix ++ [rhsSplit.2]) := by
        have appendFinal :=
          arrangedSource.append_right [lhsSplit.2]
        have squarePerm :=
          edmundsFourTwentyOneSquareSwitch_full_perm
            remainder lhsSplit.2 rhsSplit.2
        exact appendFinal.trans <| by
          simpa [switchedPrefix, List.append_assoc] using squarePerm
      have switchedPrefixPerm : switchedPrefix.Perm rhsPrefix := by
        rw [List.perm_iff_count]
        intro z
        have fullPermCount :=
          (List.perm_iff_count.mp sourceToSwitchedFull) z
        have normalCounts := normalCountEq z
        simp only [toList_wordOfPrefixFinal] at normalCounts
        simp only [List.count_append] at fullPermCount normalCounts
        omega
      exact Derives.trans lhsNormal <|
        Derives.trans switch <|
          Derives.trans
            (edmundsFourTwentyOneDerivesPrefixPermutation
              switchedPrefixPerm rhsSplit.2)
            (Derives.symm rhsNormal)
  · have rightSimple :=
      (simpleFinalIff lhsSplit.2).1 ⟨rfl, lhsRepeated⟩
    have finalsEq : rhsSplit.2 = lhsSplit.2 := rightSimple.1
    rw [finalsEq] at rhsNormal normalCountEq
    have prefixPerm : lhsPrefix.Perm rhsPrefix := by
      rw [List.perm_iff_count]
      intro z
      have counts := normalCountEq z
      simp only [toList_wordOfPrefixFinal,
        List.count_append] at counts
      simpa using counts
    exact Derives.trans lhsNormal <|
      Derives.trans
        (edmundsFourTwentyOneDerivesPrefixPermutation
          prefixPerm lhsSplit.2)
        (Derives.symm rhsNormal)

end SemigroupBasis.Examples

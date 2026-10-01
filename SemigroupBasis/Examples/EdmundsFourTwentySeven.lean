import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,3,1],[1,1,3,1],[3,3,1,3],[1,2,3,4]]`. -/
def edmundsFourTwentySevenMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 2 then 2 else 0
  else if a = 1 then
    if b = 2 then 2 else 0
  else if a = 2 then
    if b = 2 then 0 else 2
  else
    b

/-- The root catalogue representative `S4_27`. -/
def edmundsFourTwentySeven : FiniteTable where
  order := 4
  mul := edmundsFourTwentySevenMul
  assoc := by decide

def edmundsFourTwentySevenXYZ : Word Nat := ⟨0, [1, 2]⟩
def edmundsFourTwentySevenYXZ : Word Nat := ⟨1, [0, 2]⟩
def edmundsFourTwentySevenXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def edmundsFourTwentySevenYYXX : Word Nat := ⟨1, [1, 0, 0]⟩
def edmundsFourTwentySevenXXXY : Word Nat := ⟨0, [0, 0, 1]⟩
def edmundsFourTwentySevenXY : Word Nat := ⟨0, [1]⟩
def edmundsFourTwentySevenXYYY : Word Nat := ⟨0, [1, 1, 1]⟩
def edmundsFourTwentySevenYXXX : Word Nat := ⟨1, [0, 0, 0]⟩

def edmundsFourTwentySevenPrefixCommutationLaw : Identity Nat :=
  ⟨edmundsFourTwentySevenXYZ, edmundsFourTwentySevenYXZ⟩

def edmundsFourTwentySevenSquareCommutationLaw : Identity Nat :=
  ⟨edmundsFourTwentySevenXXYY, edmundsFourTwentySevenYYXX⟩

def edmundsFourTwentySevenPrefixParityLaw : Identity Nat :=
  ⟨edmundsFourTwentySevenXXXY, edmundsFourTwentySevenXY⟩

def edmundsFourTwentySevenTerminalSwitchLaw : Identity Nat :=
  ⟨edmundsFourTwentySevenXYYY, edmundsFourTwentySevenYXXX⟩

/-- Edmunds' item 34 basis for `S4_27`:
`xyz = yxz`, `xxyy = yyxx`, `xxxy = xy`, `xyyy = yxxx`. -/
def edmundsFourTwentySevenBasis : List (Identity Nat) :=
  [edmundsFourTwentySevenPrefixCommutationLaw,
    edmundsFourTwentySevenSquareCommutationLaw,
    edmundsFourTwentySevenPrefixParityLaw,
    edmundsFourTwentySevenTerminalSwitchLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem edmundsFourTwentySevenDerivesPrefixSwap
    (u v q : Word Nat) :
    Derives edmundsFourTwentySevenBasis
      ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have hbase :
      Derives edmundsFourTwentySevenBasis
        edmundsFourTwentySevenXYZ edmundsFourTwentySevenYXZ :=
    Derives.fromBasis
      (e := edmundsFourTwentySevenPrefixCommutationLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v q)
  simpa [edmundsFourTwentySevenBasis,
    edmundsFourTwentySevenPrefixCommutationLaw,
    edmundsFourTwentySevenXYZ, edmundsFourTwentySevenYXZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourTwentySevenDerivesSquareSwitch
    (u v : Word Nat) :
    Derives edmundsFourTwentySevenBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives edmundsFourTwentySevenBasis
        edmundsFourTwentySevenXXYY edmundsFourTwentySevenYYXX :=
    Derives.fromBasis
      (e := edmundsFourTwentySevenSquareCommutationLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [edmundsFourTwentySevenBasis,
    edmundsFourTwentySevenSquareCommutationLaw,
    edmundsFourTwentySevenXXYY, edmundsFourTwentySevenYYXX,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourTwentySevenDerivesPrefixTripleContraction
    (u q : Word Nat) :
    Derives edmundsFourTwentySevenBasis
      (((u ++ u) ++ u) ++ q) (u ++ q) := by
  have hbase :
      Derives edmundsFourTwentySevenBasis
        edmundsFourTwentySevenXXXY edmundsFourTwentySevenXY :=
    Derives.fromBasis
      (e := edmundsFourTwentySevenPrefixParityLaw) <| by
        exact List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u q q)
  simpa [edmundsFourTwentySevenBasis,
    edmundsFourTwentySevenPrefixParityLaw,
    edmundsFourTwentySevenXXXY, edmundsFourTwentySevenXY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem edmundsFourTwentySevenDerivesTerminalCubeSwitch
    (u v : Word Nat) :
    Derives edmundsFourTwentySevenBasis
      (u ++ ((v ++ v) ++ v)) (v ++ ((u ++ u) ++ u)) := by
  have hbase :
      Derives edmundsFourTwentySevenBasis
        edmundsFourTwentySevenXYYY edmundsFourTwentySevenYXXX :=
    Derives.fromBasis
      (e := edmundsFourTwentySevenTerminalSwitchLaw) <| by
        exact List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [edmundsFourTwentySevenBasis,
    edmundsFourTwentySevenTerminalSwitchLaw,
    edmundsFourTwentySevenXYYY, edmundsFourTwentySevenYXXX,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem edmundsFourTwentySevenDerivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat} (hperm : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction hperm with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        edmundsFourTwentySevenDerivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private theorem edmundsFourTwentySevenContractLeadingTriple
    (x final : Nat) (rest : List Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (x :: x :: x :: rest) final)
      (wordOfPrefixFinal (x :: rest) final) := by
  simpa [wordOfPrefixFinal, Word.append_assoc] using
    edmundsFourTwentySevenDerivesPrefixTripleContraction
      (Word.singleton x) (wordOfPrefixFinal rest final)

private theorem edmundsFourTwentySevenDeleteThirdPrefixCopy
    (final x : Nat) (reduced : List Nat)
    (hcount : reduced.count x = 2) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (x :: reduced) final)
      (wordOfPrefixFinal (reduced.erase x) final) := by
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
  have firstErase : (reduced.erase x).count x = 1 := by
    rw [List.count_erase_self, hcount]
  have eraseHasX : x ∈ reduced.erase x :=
    List.count_pos_iff.mp (by omega)
  have targetPerm :
      (x :: remainder).Perm (reduced.erase x) := by
    simpa [remainder] using
      (List.perm_cons_erase eraseHasX).symm
  exact Derives.trans
    (edmundsFourTwentySevenDerivesPrefixPermutation sourcePerm final) <|
    Derives.trans
      (edmundsFourTwentySevenContractLeadingTriple x final remainder)
      (edmundsFourTwentySevenDerivesPrefixPermutation targetPerm final)

private theorem edmundsFourTwentySevenDerivesNormalizePrefix :
    ∀ (pref : List Nat) (final : Nat),
      Derives edmundsFourTwentySevenBasis
        (wordOfPrefixFinal pref final)
        (wordOfPrefixFinal (positiveParityReduce pref) final)
  | [], final => Derives.refl _
  | x :: xs, final => by
      have suffixNormal :=
        edmundsFourTwentySevenDerivesNormalizePrefix xs final
      have prefixed :=
        Derives.prepend (Word.singleton x) suffixNormal
      let reduced := positiveParityReduce xs
      by_cases hcount : reduced.count x < 2
      · have reducedEq :
            positiveParityReduce (x :: xs) = x :: reduced := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have countLe : reduced.count x ≤ 2 := by
          change (positiveParityReduce xs).count x ≤ 2
          exact positiveParityReduce_count_le_two x xs
        have countEq : reduced.count x = 2 := by omega
        have reducedEq :
            positiveParityReduce (x :: xs) = reduced.erase x := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        have firstStep :
            Derives edmundsFourTwentySevenBasis
              (wordOfPrefixFinal (x :: xs) final)
              (wordOfPrefixFinal (x :: reduced) final) := by
          simpa [wordOfPrefixFinal, reduced] using prefixed
        exact Derives.trans firstStep
          (edmundsFourTwentySevenDeleteThirdPrefixCopy
            final x reduced countEq)
termination_by
  pref _ => pref.length

theorem edmundsFourTwentySevenDerivesNormal (w : Word Nat) :
    let split := splitPrefixFinal w
    Derives edmundsFourTwentySevenBasis w
      (wordOfPrefixFinal (positiveParityReduce split.1) split.2) := by
  dsimp
  have reconstruct := wordOfPrefixFinal_split w
  have normal :=
    edmundsFourTwentySevenDerivesNormalizePrefix
      (splitPrefixFinal w).1 (splitPrefixFinal w).2
  rw [reconstruct] at normal
  exact normal

/-- The derived terminal change
`u v² = v² u³`. It is the uniform bridge between any two repeated final
letters. -/
theorem edmundsFourTwentySevenDerivesRepeatedTerminalBlockSwitch
    (u v : Word Nat) :
    Derives edmundsFourTwentySevenBasis
      ((u ++ v) ++ v)
      ((v ++ v) ++ ((u ++ u) ++ u)) := by
  have expand :=
    Derives.symm <|
      edmundsFourTwentySevenDerivesPrefixTripleContraction
        u (v ++ v)
  have commute :=
    Derives.prepend u <|
      edmundsFourTwentySevenDerivesSquareSwitch u v
  have move :=
    edmundsFourTwentySevenDerivesPrefixSwap
      u (v ++ v) (u ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using expand) <|
    Derives.trans
      (by simpa [Word.append_assoc] using commute)
      (by simpa [Word.append_assoc] using move)

private theorem edmundsFourTwentySevenRepeatedSwitchUnderPrefix
    (rest : List Nat) (oldFinal newFinal : Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (rest ++ [newFinal, oldFinal]) oldFinal)
      (wordOfPrefixFinal
        (rest ++ [oldFinal, oldFinal, newFinal, newFinal]) newFinal) := by
  induction rest with
  | nil =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        edmundsFourTwentySevenDerivesRepeatedTerminalBlockSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal)
  | cons x xs ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton x) ih

private theorem edmundsFourTwentySevenPerm_two_to_end
    (a b : Nat) :
    ∀ xs : List Nat, (a :: b :: xs).Perm (xs ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x
            (edmundsFourTwentySevenPerm_two_to_end a b xs)

private theorem edmundsFourTwentySevenSwitchRepeatedFinal
    (pref : List Nat) (oldFinal newFinal : Nat)
    (hne : oldFinal ≠ newFinal)
    (hold : oldFinal ∈ pref) (hnew : newFinal ∈ pref) :
    let remainder := (pref.erase newFinal).erase oldFinal
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal pref oldFinal)
      (wordOfPrefixFinal
        (remainder ++ [oldFinal, oldFinal, newFinal, newFinal])
        newFinal) := by
  dsimp
  have oldInErase : oldFinal ∈ pref.erase newFinal := by
    simpa [hne] using hold
  have arrangeFront :
      pref.Perm
        (newFinal :: oldFinal ::
          (pref.erase newFinal).erase oldFinal) :=
    (List.perm_cons_erase hnew).trans <|
      List.Perm.cons newFinal <|
        List.perm_cons_erase oldInErase
  have arrange :
      pref.Perm
        ((pref.erase newFinal).erase oldFinal ++
          [newFinal, oldFinal]) :=
    arrangeFront.trans <|
      edmundsFourTwentySevenPerm_two_to_end
        newFinal oldFinal _
  exact Derives.trans
    (edmundsFourTwentySevenDerivesPrefixPermutation
      arrange oldFinal)
    (edmundsFourTwentySevenRepeatedSwitchUnderPrefix
      ((pref.erase newFinal).erase oldFinal)
      oldFinal newFinal)

private def edmundsFourTwentySevenSupportState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else 0

private def edmundsFourTwentySevenSupportSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private theorem edmundsFourTwentySevenMul_supportTarget (n : Nat) :
    edmundsFourTwentySevenMul 0
        (edmundsFourTwentySevenSupportState n) =
      edmundsFourTwentySevenSupportState (n + 1) := by
  cases n <;>
    simp [edmundsFourTwentySevenMul,
      edmundsFourTwentySevenSupportState]

private theorem edmundsFourTwentySevenMul_supportOther (n : Nat) :
    edmundsFourTwentySevenMul 3
        (edmundsFourTwentySevenSupportState n) =
      edmundsFourTwentySevenSupportState n := by
  simp [edmundsFourTwentySevenMul]

theorem edmundsFourTwentySevenEval_supportSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentySeven.semigroup.eval
        (edmundsFourTwentySevenSupportSeparator z)
        (wordOfPrefixFinal pref final) =
      edmundsFourTwentySevenSupportState
        ((pref ++ [final]).count z) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal,
          edmundsFourTwentySevenSupportSeparator,
          edmundsFourTwentySevenSupportState]
      · simp [wordOfPrefixFinal,
          edmundsFourTwentySevenSupportSeparator,
          edmundsFourTwentySevenSupportState, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      by_cases hx : x = z
      · subst x
        rw [show edmundsFourTwentySevenSupportSeparator z z =
          (0 : Fin 4) by
            simp [edmundsFourTwentySevenSupportSeparator]]
        change
          edmundsFourTwentySevenMul 0
              (edmundsFourTwentySevenSupportState
                ((xs ++ [final]).count z)) =
            edmundsFourTwentySevenSupportState
              ((z :: xs ++ [final]).count z)
        rw [edmundsFourTwentySevenMul_supportTarget]
        congr 1
        simp
      · rw [show edmundsFourTwentySevenSupportSeparator z x =
          (3 : Fin 4) by
            simp [edmundsFourTwentySevenSupportSeparator, hx]]
        change
          edmundsFourTwentySevenMul 3
              (edmundsFourTwentySevenSupportState
                ((xs ++ [final]).count z)) =
            edmundsFourTwentySevenSupportState
              ((x :: xs ++ [final]).count z)
        rw [edmundsFourTwentySevenMul_supportOther]
        congr 1
        simp [hx]

theorem edmundsFourTwentySevenValid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy edmundsFourTwentySeven.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated :=
    valid (edmundsFourTwentySevenSupportSeparator z)
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
    wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
    wordOfPrefixFinal_split e.rhs
  rw [← lhsReconstruct, ← rhsReconstruct,
    edmundsFourTwentySevenEval_supportSeparator,
    edmundsFourTwentySevenEval_supportSeparator] at evaluated
  have lhsCount :
      (lhsSplit.1 ++ [lhsSplit.2]).count z =
        e.lhs.toList.count z := by
    have words := congrArg Word.toList lhsReconstruct
    simpa [toList_wordOfPrefixFinal] using congrArg (List.count z) words
  have rhsCount :
      (rhsSplit.1 ++ [rhsSplit.2]).count z =
        e.rhs.toList.count z := by
    have words := congrArg Word.toList rhsReconstruct
    simpa [toList_wordOfPrefixFinal] using congrArg (List.count z) words
  rw [lhsCount, rhsCount] at evaluated
  have zeroEq :
      e.lhs.toList.count z = 0 ↔ e.rhs.toList.count z = 0 := by
    constructor
    · intro hl
      by_cases hr : e.rhs.toList.count z = 0
      · exact hr
      · have impossible := evaluated
        simp [edmundsFourTwentySevenSupportState, hl, hr] at impossible
    · intro hr
      by_cases hl : e.lhs.toList.count z = 0
      · exact hl
      · have impossible := evaluated
        simp [edmundsFourTwentySevenSupportState, hl, hr] at impossible
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  omega

private def edmundsFourTwentySevenParityState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n % 2 = 0 then 0 else 2

private def edmundsFourTwentySevenParitySeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem edmundsFourTwentySevenMul_parityTarget (n : Nat) :
    edmundsFourTwentySevenMul 2
        (edmundsFourTwentySevenParityState n) =
      edmundsFourTwentySevenParityState (n + 1) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      by_cases hn : (n + 1) % 2 = 0
      · have next : (n + 2) % 2 = 1 := by omega
        simp [edmundsFourTwentySevenParityState,
          edmundsFourTwentySevenMul, hn, next]
      · have current : (n + 1) % 2 = 1 := by omega
        have next : (n + 2) % 2 = 0 := by omega
        simp [edmundsFourTwentySevenParityState,
          edmundsFourTwentySevenMul, current, next]

private theorem edmundsFourTwentySevenMul_parityOther (n : Nat) :
    edmundsFourTwentySevenMul 3
        (edmundsFourTwentySevenParityState n) =
      edmundsFourTwentySevenParityState n := by
  simp [edmundsFourTwentySevenMul]

theorem edmundsFourTwentySevenEval_paritySeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentySeven.semigroup.eval
        (edmundsFourTwentySevenParitySeparator z)
        (wordOfPrefixFinal pref final) =
      edmundsFourTwentySevenParityState
        ((pref ++ [final]).count z) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal,
          edmundsFourTwentySevenParitySeparator,
          edmundsFourTwentySevenParityState]
      · simp [wordOfPrefixFinal,
          edmundsFourTwentySevenParitySeparator,
          edmundsFourTwentySevenParityState, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      by_cases hx : x = z
      · subst x
        rw [show edmundsFourTwentySevenParitySeparator z z =
          (2 : Fin 4) by
            simp [edmundsFourTwentySevenParitySeparator]]
        change
          edmundsFourTwentySevenMul 2
              (edmundsFourTwentySevenParityState
                ((xs ++ [final]).count z)) =
            edmundsFourTwentySevenParityState
              ((z :: xs ++ [final]).count z)
        rw [edmundsFourTwentySevenMul_parityTarget]
        congr 1
        simp
      · rw [show edmundsFourTwentySevenParitySeparator z x =
          (3 : Fin 4) by
            simp [edmundsFourTwentySevenParitySeparator, hx]]
        change
          edmundsFourTwentySevenMul 3
              (edmundsFourTwentySevenParityState
                ((xs ++ [final]).count z)) =
            edmundsFourTwentySevenParityState
              ((x :: xs ++ [final]).count z)
        rw [edmundsFourTwentySevenMul_parityOther]
        congr 1
        simp [hx]

private theorem edmundsFourTwentySevenParityState_eq_implies_mod
    {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : edmundsFourTwentySevenParityState m =
      edmundsFourTwentySevenParityState n) :
    m % 2 = n % 2 := by
  by_cases hmEven : m % 2 = 0
  · by_cases hnEven : n % 2 = 0
    · exact hmEven.trans hnEven.symm
    · have hnOdd : n % 2 = 1 := by omega
      simp [edmundsFourTwentySevenParityState, hm, hn,
        hmEven, hnOdd] at h
  · have hmOdd : m % 2 = 1 := by omega
    by_cases hnEven : n % 2 = 0
    · simp [edmundsFourTwentySevenParityState, hm, hn,
        hmOdd, hnEven] at h
    · have hnOdd : n % 2 = 1 := by omega
      exact hmOdd.trans hnOdd.symm

theorem edmundsFourTwentySevenValid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy edmundsFourTwentySeven.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have support := edmundsFourTwentySevenValid_support e valid z
  by_cases hl : e.lhs.toList.count z = 0
  · have hr : e.rhs.toList.count z = 0 := by
      rw [List.count_eq_zero] at hl ⊢
      intro h
      exact hl (support.mpr h)
    simp [hl, hr]
  · have hr : e.rhs.toList.count z ≠ 0 := by
      intro hr
      have lhsMem : z ∈ e.lhs.toList :=
        List.count_pos_iff.mp (Nat.pos_of_ne_zero hl)
      have rhsMem := support.mp lhsMem
      exact (List.count_eq_zero.mp hr) rhsMem
    have evaluated :=
      valid (edmundsFourTwentySevenParitySeparator z)
    let lhsSplit := splitPrefixFinal e.lhs
    let rhsSplit := splitPrefixFinal e.rhs
    have lhsReconstruct :
        wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
      wordOfPrefixFinal_split e.lhs
    have rhsReconstruct :
        wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
      wordOfPrefixFinal_split e.rhs
    rw [← lhsReconstruct, ← rhsReconstruct,
      edmundsFourTwentySevenEval_paritySeparator,
      edmundsFourTwentySevenEval_paritySeparator] at evaluated
    have lhsCount :
        (lhsSplit.1 ++ [lhsSplit.2]).count z =
          e.lhs.toList.count z := by
      have words := congrArg Word.toList lhsReconstruct
      simpa [toList_wordOfPrefixFinal] using
        congrArg (List.count z) words
    have rhsCount :
        (rhsSplit.1 ++ [rhsSplit.2]).count z =
          e.rhs.toList.count z := by
      have words := congrArg Word.toList rhsReconstruct
      simpa [toList_wordOfPrefixFinal] using
        congrArg (List.count z) words
    rw [lhsCount, rhsCount] at evaluated
    apply edmundsFourTwentySevenParityState_eq_implies_mod hl hr
    exact evaluated

private def edmundsFourTwentySevenFinalSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

theorem edmundsFourTwentySevenEval_finalSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentySeven.semigroup.eval
        (edmundsFourTwentySevenFinalSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 4) else
        if final = z then (1 : Fin 4) else (3 : Fin 4) := by
  induction pref with
  | nil =>
      by_cases hfinal : final = z
      · subst final
        simp [wordOfPrefixFinal,
          edmundsFourTwentySevenFinalSeparator]
      · simp [wordOfPrefixFinal,
          edmundsFourTwentySevenFinalSeparator, hfinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons,
        Semigroup.eval_append, Semigroup.eval_singleton, ih]
      change
        edmundsFourTwentySevenMul
            (edmundsFourTwentySevenFinalSeparator z x)
            (if z ∈ xs then (0 : Fin 4) else
              if final = z then (1 : Fin 4) else (3 : Fin 4)) =
          if z ∈ x :: xs then (0 : Fin 4) else
            if final = z then (1 : Fin 4) else (3 : Fin 4)
      by_cases hx : x = z
      · subst x
        by_cases hp : z ∈ xs <;>
          by_cases hf : final = z <;>
            simp [edmundsFourTwentySevenFinalSeparator,
              edmundsFourTwentySevenMul, hp, hf]
      · simp [edmundsFourTwentySevenFinalSeparator, hx, Ne.symm hx,
          edmundsFourTwentySevenMul]

theorem edmundsFourTwentySevenEval_finalSeparator_eq_one_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    edmundsFourTwentySeven.semigroup.eval
        (edmundsFourTwentySevenFinalSeparator z)
        (wordOfPrefixFinal pref final) = (1 : Fin 4) ↔
      final = z ∧ z ∉ pref := by
  rw [edmundsFourTwentySevenEval_finalSeparator]
  by_cases hp : z ∈ pref
  · simp [hp]
  · by_cases hf : final = z
    · simp [hp, hf]
    · simp [hp, hf]

private theorem edmundsFourTwentySevenReducedPrefixPerm
    (pref₁ pref₂ : List Nat) (final : Nat)
    (leftReduced : ∀ z, pref₁.count z ≤ 2)
    (rightReduced : ∀ z, pref₂.count z ≤ 2)
    (support :
      ∀ z, z ∈ pref₁ ++ [final] ↔ z ∈ pref₂ ++ [final])
    (parity :
      ∀ z, (pref₁ ++ [final]).count z % 2 =
        (pref₂ ++ [final]).count z % 2)
    (finalMembership : final ∈ pref₁ ↔ final ∈ pref₂) :
    pref₁.Perm pref₂ := by
  rw [List.perm_iff_count]
  intro z
  have prefixSupport : z ∈ pref₁ ↔ z ∈ pref₂ := by
    by_cases hz : z = final
    · subst z
      exact finalMembership
    · have h := support z
      simpa [hz, Ne.symm hz] using h
  have prefixParity : pref₁.count z % 2 = pref₂.count z % 2 := by
    have h := parity z
    simp only [List.count_append] at h
    by_cases hz : z = final
    · subst z
      simp at h
      omega
    · simp [Ne.symm hz] at h
      exact h
  have leftLe := leftReduced z
  have rightLe := rightReduced z
  by_cases hz : z ∈ pref₁
  · have leftPos := List.count_pos_iff.mpr hz
    have rightPos := List.count_pos_iff.mpr (prefixSupport.mp hz)
    omega
  · have leftZero := List.count_eq_zero.mpr hz
    have rightZero := List.count_eq_zero.mpr <| by
      intro h
      exact hz (prefixSupport.mpr h)
    omega

private theorem edmundsFourTwentySevenMul_prefixCommutation
    (a b c : Fin 4) :
    edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul a b) c =
      edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul b a) c := by
  decide +revert

private theorem edmundsFourTwentySevenMul_squareCommutation
    (a b : Fin 4) :
    edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul a a) b) b =
      edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul b b) a) a := by
  decide +revert

private theorem edmundsFourTwentySevenMul_prefixParity
    (a b : Fin 4) :
    edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul a a) a) b =
      edmundsFourTwentySevenMul a b := by
  decide +revert

private theorem edmundsFourTwentySevenMul_terminalSwitch
    (a b : Fin 4) :
    edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul a b) b) b =
      edmundsFourTwentySevenMul
        (edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul b a) a) a := by
  decide +revert

theorem edmundsFourTwentySevenBasis_models :
    Models edmundsFourTwentySeven.semigroup
      edmundsFourTwentySevenBasis := by
  intro e he
  simp only [edmundsFourTwentySevenBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (valuation 0) (valuation 1))
          (valuation 2) =
        edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (valuation 1) (valuation 0))
          (valuation 2)
    exact edmundsFourTwentySevenMul_prefixCommutation
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (edmundsFourTwentySevenMul
              (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 1) =
        edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (edmundsFourTwentySevenMul
              (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0)
    exact edmundsFourTwentySevenMul_squareCommutation
      (valuation 0) (valuation 1)
  · intro valuation
    change
      edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (edmundsFourTwentySevenMul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 1) =
        edmundsFourTwentySevenMul
          (valuation 0) (valuation 1)
    exact edmundsFourTwentySevenMul_prefixParity
      (valuation 0) (valuation 1)
  · intro valuation
    change
      edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (edmundsFourTwentySevenMul
              (valuation 0) (valuation 1))
            (valuation 1))
          (valuation 1) =
        edmundsFourTwentySevenMul
          (edmundsFourTwentySevenMul
            (edmundsFourTwentySevenMul
              (valuation 1) (valuation 0))
            (valuation 0))
          (valuation 0)
    exact edmundsFourTwentySevenMul_terminalSwitch
      (valuation 0) (valuation 1)

/-- Complete unrestricted identity basis for the exact `S4_27` table. -/
theorem edmundsFourTwentySevenBasis_complete :
    BasisFor edmundsFourTwentySeven.semigroup
      edmundsFourTwentySevenBasis := by
  refine ⟨edmundsFourTwentySevenBasis_models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  let lhsPrefix := positiveParityReduce lhsSplit.1
  let rhsPrefix := positiveParityReduce rhsSplit.1
  have lhsNormal := edmundsFourTwentySevenDerivesNormal e.lhs
  have rhsNormal := edmundsFourTwentySevenDerivesNormal e.rhs
  dsimp only at lhsNormal rhsNormal
  change
    Derives edmundsFourTwentySevenBasis e.lhs
      (wordOfPrefixFinal lhsPrefix lhsSplit.2) at lhsNormal
  change
    Derives edmundsFourTwentySevenBasis e.rhs
      (wordOfPrefixFinal rhsPrefix rhsSplit.2) at rhsNormal
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        edmundsFourTwentySeven.semigroup.eval valuation
            (wordOfPrefixFinal lhsPrefix lhsSplit.2) =
          edmundsFourTwentySeven.semigroup.eval valuation
            (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound edmundsFourTwentySevenBasis_models valuation
    have rhsSound :=
      rhsNormal.sound edmundsFourTwentySevenBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  let normalIdentity : Identity Nat :=
    ⟨wordOfPrefixFinal lhsPrefix lhsSplit.2,
      wordOfPrefixFinal rhsPrefix rhsSplit.2⟩
  have normalValid :
      normalIdentity.SatisfiedBy
        edmundsFourTwentySeven.semigroup := normalizedEval
  have normalSupport :
      ∀ z,
        z ∈ lhsPrefix ++ [lhsSplit.2] ↔
          z ∈ rhsPrefix ++ [rhsSplit.2] := by
    intro z
    simpa [normalIdentity, toList_wordOfPrefixFinal] using
      edmundsFourTwentySevenValid_support
        normalIdentity normalValid z
  have normalParity :
      ∀ z,
        (lhsPrefix ++ [lhsSplit.2]).count z % 2 =
          (rhsPrefix ++ [rhsSplit.2]).count z % 2 := by
    intro z
    simpa [normalIdentity, toList_wordOfPrefixFinal] using
      edmundsFourTwentySevenValid_parity
        normalIdentity normalValid z
  have simpleFinalIff :
      ∀ z,
        (lhsSplit.2 = z ∧ z ∉ lhsPrefix) ↔
          (rhsSplit.2 = z ∧ z ∉ rhsPrefix) := by
    intro z
    have evaluated :=
      normalizedEval (edmundsFourTwentySevenFinalSeparator z)
    constructor
    · intro h
      exact
        (edmundsFourTwentySevenEval_finalSeparator_eq_one_iff
          z rhsPrefix rhsSplit.2).1 <|
            evaluated.symm.trans <|
              (edmundsFourTwentySevenEval_finalSeparator_eq_one_iff
                z lhsPrefix lhsSplit.2).2 h
    · intro h
      exact
        (edmundsFourTwentySevenEval_finalSeparator_eq_one_iff
          z lhsPrefix lhsSplit.2).1 <|
            evaluated.trans <|
              (edmundsFourTwentySevenEval_finalSeparator_eq_one_iff
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
    · have prefixPerm :
          lhsPrefix.Perm rhsPrefix := by
        rw [← finalsEq] at normalSupport normalParity rhsRepeated
        exact edmundsFourTwentySevenReducedPrefixPerm
          lhsPrefix rhsPrefix lhsSplit.2
          (by
            intro z
            exact positiveParityReduce_count_le_two z lhsSplit.1)
          (by
            intro z
            exact positiveParityReduce_count_le_two z rhsSplit.1)
          normalSupport normalParity
          ⟨fun _ => rhsRepeated, fun _ => lhsRepeated⟩
      rw [← finalsEq] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (edmundsFourTwentySevenDerivesPrefixPermutation
            prefixPerm lhsSplit.2)
          (Derives.symm rhsNormal)
    · have newInLeft : rhsSplit.2 ∈ lhsPrefix := by
        have rhsFull : rhsSplit.2 ∈ rhsPrefix ++ [rhsSplit.2] := by
          simp
        have lhsFull := (normalSupport rhsSplit.2).mpr rhsFull
        rcases List.mem_append.mp lhsFull with h | h
        · exact h
        · simp only [List.mem_singleton] at h
          exact False.elim (finalsEq h.symm)
      let remainder :=
        (lhsPrefix.erase rhsSplit.2).erase lhsSplit.2
      let switchedPrefix :=
        remainder ++
          [lhsSplit.2, lhsSplit.2, rhsSplit.2, rhsSplit.2]
      have switch :
          Derives edmundsFourTwentySevenBasis
            (wordOfPrefixFinal lhsPrefix lhsSplit.2)
            (wordOfPrefixFinal switchedPrefix rhsSplit.2) := by
        exact edmundsFourTwentySevenSwitchRepeatedFinal
          lhsPrefix lhsSplit.2 rhsSplit.2 finalsEq
          lhsRepeated newInLeft
      have switchedNormal :=
        edmundsFourTwentySevenDerivesNormalizePrefix
          switchedPrefix rhsSplit.2
      have switchedToRightValid :
          (Identity.mk
            (wordOfPrefixFinal
              (positiveParityReduce switchedPrefix) rhsSplit.2)
            (wordOfPrefixFinal rhsPrefix rhsSplit.2)).SatisfiedBy
              edmundsFourTwentySeven.semigroup := by
        intro valuation
        have switchSound :=
          switch.sound edmundsFourTwentySevenBasis_models valuation
        have switchedNormalSound :=
          switchedNormal.sound
            edmundsFourTwentySevenBasis_models valuation
        exact switchedNormalSound.symm.trans <|
          switchSound.symm.trans (normalizedEval valuation)
      have switchedSupport :
          ∀ z,
            z ∈ positiveParityReduce switchedPrefix ++ [rhsSplit.2] ↔
              z ∈ rhsPrefix ++ [rhsSplit.2] := by
        intro z
        simpa [toList_wordOfPrefixFinal] using
          edmundsFourTwentySevenValid_support
            (Identity.mk
              (wordOfPrefixFinal
                (positiveParityReduce switchedPrefix) rhsSplit.2)
              (wordOfPrefixFinal rhsPrefix rhsSplit.2))
            switchedToRightValid z
      have switchedParity :
          ∀ z,
            (positiveParityReduce switchedPrefix ++
                [rhsSplit.2]).count z % 2 =
              (rhsPrefix ++ [rhsSplit.2]).count z % 2 := by
        intro z
        simpa [toList_wordOfPrefixFinal] using
          edmundsFourTwentySevenValid_parity
            (Identity.mk
              (wordOfPrefixFinal
                (positiveParityReduce switchedPrefix) rhsSplit.2)
              (wordOfPrefixFinal rhsPrefix rhsSplit.2))
            switchedToRightValid z
      have switchedFinalMem :
          rhsSplit.2 ∈ positiveParityReduce switchedPrefix := by
        rw [mem_positiveParityReduce_iff]
        simp [switchedPrefix]
      have prefixPerm :
          (positiveParityReduce switchedPrefix).Perm rhsPrefix :=
        edmundsFourTwentySevenReducedPrefixPerm
          (positiveParityReduce switchedPrefix) rhsPrefix rhsSplit.2
          (by
            intro z
            exact positiveParityReduce_count_le_two z switchedPrefix)
          (by
            intro z
            exact positiveParityReduce_count_le_two z rhsSplit.1)
          switchedSupport switchedParity
          ⟨fun _ => rhsRepeated, fun _ => switchedFinalMem⟩
      exact Derives.trans lhsNormal <|
        Derives.trans switch <|
          Derives.trans switchedNormal <|
            Derives.trans
              (edmundsFourTwentySevenDerivesPrefixPermutation
                prefixPerm rhsSplit.2)
              (Derives.symm rhsNormal)
  · have rightSimple :=
      (simpleFinalIff lhsSplit.2).1 ⟨rfl, lhsRepeated⟩
    have finalsEq : rhsSplit.2 = lhsSplit.2 := rightSimple.1
    have prefixPerm : lhsPrefix.Perm rhsPrefix := by
      rw [finalsEq] at normalSupport normalParity
      exact edmundsFourTwentySevenReducedPrefixPerm
        lhsPrefix rhsPrefix lhsSplit.2
        (by
          intro z
          exact positiveParityReduce_count_le_two z lhsSplit.1)
        (by
          intro z
          exact positiveParityReduce_count_le_two z rhsSplit.1)
        normalSupport normalParity
        ⟨fun h => (lhsRepeated h).elim,
          fun h => (rightSimple.2 h).elim⟩
    rw [finalsEq] at rhsNormal
    exact Derives.trans lhsNormal <|
      Derives.trans
        (edmundsFourTwentySevenDerivesPrefixPermutation
          prefixPerm lhsSplit.2)
        (Derives.symm rhsNormal)

end SemigroupBasis.Examples

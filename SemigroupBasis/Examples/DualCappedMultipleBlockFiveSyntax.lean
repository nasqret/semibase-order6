import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def dualCappedMultipleBlockFiveXXX : Word Nat := ⟨0, [0, 0]⟩
def dualCappedMultipleBlockFiveXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def dualCappedMultipleBlockFiveXYX : Word Nat := ⟨0, [1, 0]⟩
def dualCappedMultipleBlockFiveXXY : Word Nat := ⟨0, [0, 1]⟩
def dualCappedMultipleBlockFiveXYZ : Word Nat := ⟨0, [1, 2]⟩
def dualCappedMultipleBlockFiveXZY : Word Nat := ⟨0, [2, 1]⟩
def dualCappedMultipleBlockFiveYYXX : Word Nat := ⟨1, [1, 0, 0]⟩
def dualCappedMultipleBlockFiveXYYX : Word Nat := ⟨0, [1, 1, 0]⟩

def dualCappedMultipleBlockFivePowerLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveXXX, dualCappedMultipleBlockFiveXXXX⟩

def dualCappedMultipleBlockFiveGatherLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveXYX, dualCappedMultipleBlockFiveXXY⟩

def dualCappedMultipleBlockFiveSuffixSwapLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveXYZ, dualCappedMultipleBlockFiveXZY⟩

def dualCappedMultipleBlockFiveSquareRotationLaw : Identity Nat :=
  ⟨dualCappedMultipleBlockFiveYYXX, dualCappedMultipleBlockFiveXYYX⟩

/-- The opposite-orientation `S5_209` basis
`xxx = xxxx`, `xyx = xxy`, `xyz = xzy`, `yyxx = xyyx`. -/
def dualCappedMultipleBlockFiveBasis : List (Identity Nat) :=
  [dualCappedMultipleBlockFivePowerLaw, dualCappedMultipleBlockFiveGatherLaw,
    dualCappedMultipleBlockFiveSuffixSwapLaw,
    dualCappedMultipleBlockFiveSquareRotationLaw]

private def dualCappedMultipleBlockFiveInstantiate
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract four consecutive copies of any nonempty block to three copies. -/
theorem dualCappedMultipleBlockFiveDerivesFourToThree (u : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives dualCappedMultipleBlockFiveBasis
        dualCappedMultipleBlockFiveXXXX dualCappedMultipleBlockFiveXXX :=
    Derives.symm <|
      Derives.fromBasis (e := dualCappedMultipleBlockFivePowerLaw) <|
        List.Mem.head _
  have h :=
    Derives.subst hbase (dualCappedMultipleBlockFiveInstantiate u u u)
  simpa [dualCappedMultipleBlockFiveBasis, dualCappedMultipleBlockFivePowerLaw,
    dualCappedMultipleBlockFiveXXXX, dualCappedMultipleBlockFiveXXX,
    dualCappedMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Gather the final copy of a block next to its initial copy. -/
theorem dualCappedMultipleBlockFiveDerivesGather (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives dualCappedMultipleBlockFiveBasis
        dualCappedMultipleBlockFiveXYX dualCappedMultipleBlockFiveXXY :=
    Derives.fromBasis (e := dualCappedMultipleBlockFiveGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (dualCappedMultipleBlockFiveInstantiate u v u)
  simpa [dualCappedMultipleBlockFiveBasis, dualCappedMultipleBlockFiveGatherLaw,
    dualCappedMultipleBlockFiveXYX, dualCappedMultipleBlockFiveXXY,
    dualCappedMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Swap two blocks following an arbitrary nonempty prefix block. -/
theorem dualCappedMultipleBlockFiveDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives dualCappedMultipleBlockFiveBasis
        dualCappedMultipleBlockFiveXYZ dualCappedMultipleBlockFiveXZY :=
    Derives.fromBasis (e := dualCappedMultipleBlockFiveSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h :=
    Derives.subst hbase (dualCappedMultipleBlockFiveInstantiate p u v)
  simpa [dualCappedMultipleBlockFiveBasis,
    dualCappedMultipleBlockFiveSuffixSwapLaw, dualCappedMultipleBlockFiveXYZ,
    dualCappedMultipleBlockFiveXZY, dualCappedMultipleBlockFiveInstantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private theorem dualCappedMultipleBlockFiveDerivesSquareRotation
    (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      ((u ++ (v ++ v)) ++ u) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives dualCappedMultipleBlockFiveBasis
        dualCappedMultipleBlockFiveXYYX dualCappedMultipleBlockFiveYYXX :=
    Derives.symm <|
      Derives.fromBasis
        (e := dualCappedMultipleBlockFiveSquareRotationLaw) <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (dualCappedMultipleBlockFiveInstantiate u v u)
  simpa [dualCappedMultipleBlockFiveBasis,
    dualCappedMultipleBlockFiveSquareRotationLaw,
    dualCappedMultipleBlockFiveXYYX, dualCappedMultipleBlockFiveYYXX,
    dualCappedMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Products of two square blocks commute. -/
theorem dualCappedMultipleBlockFiveDerivesSquareSquareCommutation
    (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  exact Derives.trans
    (dualCappedMultipleBlockFiveDerivesSuffixSwap u u (v ++ v))
    (dualCappedMultipleBlockFiveDerivesSquareRotation u v)

/-- A cube block commutes past a square block. -/
theorem dualCappedMultipleBlockFiveDerivesCubeSquareCommutation
    (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ (v ++ v))
      ((v ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.prepend u
      (dualCappedMultipleBlockFiveDerivesSquareSquareCommutation u v)
  have second :=
    Derives.appendRight
      (dualCappedMultipleBlockFiveDerivesSquareRotation u v) u
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- A square block commutes past a cube block. -/
theorem dualCappedMultipleBlockFiveDerivesSquareCubeCommutation
    (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      ((u ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ (u ++ u)) := by
  have first :=
    Derives.appendRight
      (dualCappedMultipleBlockFiveDerivesSquareSquareCommutation u v) v
  have second :=
    dualCappedMultipleBlockFiveDerivesSuffixSwap (v ++ v) (u ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- Products of two cube blocks commute. -/
theorem dualCappedMultipleBlockFiveDerivesCubeCubeCommutation
    (u v : Word Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.appendRight
      (dualCappedMultipleBlockFiveDerivesCubeSquareCommutation u v) v
  have second :=
    dualCappedMultipleBlockFiveDerivesSuffixSwap
      (v ++ v) ((u ++ u) ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- The head is recorded exactly when it occurs only once in the word. -/
def dualCappedMultipleBlockFiveSingletonHead (w : Word Nat) : Option Nat :=
  if w.toList.count w.head = 1 then some w.head else none

private def dualCappedMultipleBlockFiveWordOfCons
    (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def dualCappedMultipleBlockFiveAppendList
    (p : Word Nat) (xs : List Nat) : Word Nat :=
  ⟨p.head, p.tail ++ xs⟩

private theorem dualCappedMultipleBlockFiveAppendList_cons
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    dualCappedMultipleBlockFiveAppendList p (x :: xs) =
      p ++ dualCappedMultipleBlockFiveWordOfCons x xs := by
  apply Word.toList_injective
  simp [dualCappedMultipleBlockFiveAppendList,
    dualCappedMultipleBlockFiveWordOfCons, Word.toList]

private theorem dualCappedMultipleBlockFiveAppendList_cons_prefix
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    dualCappedMultipleBlockFiveAppendList p (x :: xs) =
      dualCappedMultipleBlockFiveAppendList
        (p ++ Word.singleton x) xs := by
  apply Word.toList_injective
  simp [dualCappedMultipleBlockFiveAppendList, Word.toList,
    List.append_assoc]

@[simp]
private theorem dualCappedMultipleBlockFiveAppendList_toList
    (p : Word Nat) (xs : List Nat) :
    (dualCappedMultipleBlockFiveAppendList p xs).toList =
      p.toList ++ xs := by
  cases xs <;>
    simp [dualCappedMultipleBlockFiveAppendList, Word.toList]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
private theorem dualCappedMultipleBlockFiveDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives dualCappedMultipleBlockFiveBasis
      (dualCappedMultipleBlockFiveAppendList p xs)
      (dualCappedMultipleBlockFiveAppendList p ys) := by
  induction h generalizing p with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have h := ih (p ++ Word.singleton x)
      rw [dualCappedMultipleBlockFiveAppendList_cons_prefix,
        dualCappedMultipleBlockFiveAppendList_cons_prefix]
      exact h
  | swap x y xs =>
      cases xs with
      | nil =>
          rw [dualCappedMultipleBlockFiveAppendList_cons,
            dualCappedMultipleBlockFiveAppendList_cons]
          simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using
            dualCappedMultipleBlockFiveDerivesSuffixSwap p
              (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (dualCappedMultipleBlockFiveDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (dualCappedMultipleBlockFiveWordOfCons z zs)
          rw [dualCappedMultipleBlockFiveAppendList_cons,
            dualCappedMultipleBlockFiveAppendList_cons]
          simpa [dualCappedMultipleBlockFiveWordOfCons,
            Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

def dualCappedMultipleBlockFiveExponent (n : Nat) : Nat :=
  if n < 3 then n else 3

private theorem dualCappedMultipleBlockFiveExponent_le_three (n : Nat) :
    dualCappedMultipleBlockFiveExponent n ≤ 3 := by
  unfold dualCappedMultipleBlockFiveExponent
  split <;> omega

private theorem dualCappedMultipleBlockFiveExponent_pos
    {n : Nat} (positive : 0 < n) :
    0 < dualCappedMultipleBlockFiveExponent n := by
  unfold dualCappedMultipleBlockFiveExponent
  split <;> omega

private theorem dualCappedMultipleBlockFiveExponent_eq_one_iff
    {n : Nat} (_positive : 0 < n) :
    dualCappedMultipleBlockFiveExponent n = 1 ↔ n = 1 := by
  unfold dualCappedMultipleBlockFiveExponent
  split <;> omega

private theorem dualCappedMultipleBlockFiveExponent_succ (n : Nat) :
    dualCappedMultipleBlockFiveExponent (n + 1) =
      if dualCappedMultipleBlockFiveExponent n < 3 then
        dualCappedMultipleBlockFiveExponent n + 1
      else
        dualCappedMultipleBlockFiveExponent n := by
  by_cases hn : n < 3 <;>
    by_cases hnext : n + 1 < 3 <;>
      simp [dualCappedMultipleBlockFiveExponent, hn, hnext] <;>
        omega

private theorem dualCappedMultipleBlockFiveCount_replicate_of_ne
    {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        dualCappedMultipleBlockFiveCount_replicate_of_ne hzx n]

private theorem dualCappedMultipleBlockFiveCount_filter_ne_self
    (x : Nat) (xs : List Nat) :
    (xs.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem dualCappedMultipleBlockFiveCount_filter_ne_of_ne
    {x z : Nat} (hzx : z ≠ x) (xs : List Nat) :
    (xs.filter (fun a => decide (a ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases hax : a = x
      · subst a
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm hzx)]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [ih]

/-- The unrestricted first-occurrence block list. Every variable occurs in
one block of length one, two, or three, with length determined by
`dualCappedMultipleBlockFiveExponent`. -/
def dualCappedMultipleBlockFiveNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := dualCappedMultipleBlockFiveNormalList xs
      List.replicate
          (dualCappedMultipleBlockFiveExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem dualCappedMultipleBlockFiveNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (dualCappedMultipleBlockFiveNormalList xs).count z =
        dualCappedMultipleBlockFiveExponent (xs.count z)
  | [] => by
      simp [dualCappedMultipleBlockFiveNormalList,
        dualCappedMultipleBlockFiveExponent]
  | x :: xs => by
      simp only [dualCappedMultipleBlockFiveNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self,
          dualCappedMultipleBlockFiveCount_filter_ne_self]
        omega
      · rw [dualCappedMultipleBlockFiveCount_replicate_of_ne hzx,
          dualCappedMultipleBlockFiveCount_filter_ne_of_ne hzx,
          Nat.zero_add, dualCappedMultipleBlockFiveNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem dualCappedMultipleBlockFiveNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    dualCappedMultipleBlockFiveNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    dualCappedMultipleBlockFiveNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    dualCappedMultipleBlockFiveExponent_pos (by omega)) countEq.symm

/-- Lists consisting of one first-occurrence block of length one, two, or
three for each variable. -/
inductive DualCappedMultipleBlockFiveNormal : List Nat → Prop
  | nil : DualCappedMultipleBlockFiveNormal []
  | single (x : Nat) (xs : List Nat) :
      DualCappedMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualCappedMultipleBlockFiveNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      DualCappedMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualCappedMultipleBlockFiveNormal (x :: x :: xs)
  | triple (x : Nat) (xs : List Nat) :
      DualCappedMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualCappedMultipleBlockFiveNormal (x :: x :: x :: xs)

private theorem DualCappedMultipleBlockFiveNormal.filter_ne
    {xs : List Nat} (normal : DualCappedMultipleBlockFiveNormal xs) (x : Nat) :
    DualCappedMultipleBlockFiveNormal
      (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact .nil
  | single y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          DualCappedMultipleBlockFiveNormal.single y _ ih yNotMemFilter
  | double y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          DualCappedMultipleBlockFiveNormal.double y _ ih yNotMemFilter
  | triple y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          DualCappedMultipleBlockFiveNormal.triple y _ ih yNotMemFilter

theorem dualCappedMultipleBlockFiveNormalList_normal :
    ∀ xs : List Nat,
      DualCappedMultipleBlockFiveNormal
        (dualCappedMultipleBlockFiveNormalList xs)
  | [] => .nil
  | x :: xs => by
      let rest := dualCappedMultipleBlockFiveNormalList xs
      have restNormal := dualCappedMultipleBlockFiveNormalList_normal xs
      have filteredNormal := restNormal.filter_ne x
      have xNotMem :
          x ∉ rest.filter (fun y => decide (y ≠ x)) := by
        simp
      have positive :
          0 < dualCappedMultipleBlockFiveExponent ((x :: xs).count x) :=
        dualCappedMultipleBlockFiveExponent_pos (by simp)
      have bound :=
        dualCappedMultipleBlockFiveExponent_le_three ((x :: xs).count x)
      have cases :
          dualCappedMultipleBlockFiveExponent ((x :: xs).count x) = 1 ∨
            dualCappedMultipleBlockFiveExponent ((x :: xs).count x) = 2 ∨
              dualCappedMultipleBlockFiveExponent ((x :: xs).count x) = 3 := by
        omega
      rcases cases with h | h | h
      · change DualCappedMultipleBlockFiveNormal
          (List.replicate
              (dualCappedMultipleBlockFiveExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualCappedMultipleBlockFiveNormal.single x _ filteredNormal xNotMem
      · change DualCappedMultipleBlockFiveNormal
          (List.replicate
              (dualCappedMultipleBlockFiveExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualCappedMultipleBlockFiveNormal.double x _ filteredNormal xNotMem
      · change DualCappedMultipleBlockFiveNormal
          (List.replicate
              (dualCappedMultipleBlockFiveExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualCappedMultipleBlockFiveNormal.triple x _ filteredNormal xNotMem

private theorem dualCappedMultipleBlockFivePerm_extract
    (x : Nat) (xs : List Nat) :
    xs.Perm
      (List.replicate (xs.count x) x ++
        xs.filter (fun y => decide (y ≠ x))) := by
  rw [List.perm_iff_count]
  intro z
  by_cases hzx : z = x
  · subst z
    rw [List.count_append, List.count_replicate_self,
      dualCappedMultipleBlockFiveCount_filter_ne_self]
    omega
  · rw [List.count_append,
      dualCappedMultipleBlockFiveCount_replicate_of_ne hzx,
      dualCappedMultipleBlockFiveCount_filter_ne_of_ne hzx]
    omega

private theorem dualCappedMultipleBlockFiveContractLeadingFour
    (x : Nat) (suffix : List Nat) :
    Derives dualCappedMultipleBlockFiveBasis
      (dualCappedMultipleBlockFiveWordOfCons x (x :: x :: x :: suffix))
      (dualCappedMultipleBlockFiveWordOfCons x (x :: x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using
          dualCappedMultipleBlockFiveDerivesFourToThree (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (dualCappedMultipleBlockFiveDerivesFourToThree (Word.singleton x))
          (dualCappedMultipleBlockFiveWordOfCons y ys)
      simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using h

private theorem dualCappedMultipleBlockFiveDerivesNormalizeList :
    ∀ x xs,
      match dualCappedMultipleBlockFiveNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives dualCappedMultipleBlockFiveBasis
            (dualCappedMultipleBlockFiveWordOfCons x xs)
            (dualCappedMultipleBlockFiveWordOfCons y ys)
  | x, [] => by
      have normalEq :
          dualCappedMultipleBlockFiveNormalList [x] = [x] := by
        simp [dualCappedMultipleBlockFiveNormalList,
          dualCappedMultipleBlockFiveExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        dualCappedMultipleBlockFiveDerivesNormalizeList y ys
      cases hn : dualCappedMultipleBlockFiveNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            dualCappedMultipleBlockFiveNormalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          let rest := z :: zs
          let without :=
            rest.filter (fun a => decide (a ≠ x))
          have arrangePerm :
              rest.Perm
                (List.replicate (rest.count x) x ++ without) := by
            exact dualCappedMultipleBlockFivePerm_extract x rest
          have arranged :=
            dualCappedMultipleBlockFiveDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                dualCappedMultipleBlockFiveExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              dualCappedMultipleBlockFiveNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 3 := by
            rw [restCount]
            exact dualCappedMultipleBlockFiveExponent_le_three _
          have targetExponent :
              dualCappedMultipleBlockFiveExponent ((x :: y :: ys).count x) =
                if rest.count x < 3 then rest.count x + 1
                else rest.count x := by
            rw [List.count_cons_self, dualCappedMultipleBlockFiveExponent_succ,
              ← restCount]
          have first :
              Derives dualCappedMultipleBlockFiveBasis
                (dualCappedMultipleBlockFiveWordOfCons x (y :: ys))
                (dualCappedMultipleBlockFiveWordOfCons x
                  (List.replicate (rest.count x) x ++ without)) :=
            Derives.trans
              (by
                simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
                  Word.singleton, Word.append_assoc] using prefixed)
              (by
                simpa [dualCappedMultipleBlockFiveAppendList,
                  dualCappedMultipleBlockFiveWordOfCons, Word.singleton,
                  rest, without] using
                    arranged)
          by_cases hsmall : rest.count x < 3
          · have normalEq :
                dualCappedMultipleBlockFiveNormalList (x :: y :: ys) =
                  x ::
                    List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (dualCappedMultipleBlockFiveExponent
                      ((x :: y :: ys).count x)) x ++
                    (dualCappedMultipleBlockFiveNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn]
              rw [List.replicate_succ]
            rw [normalEq]
            exact first
          · have countThree : rest.count x = 3 := by omega
            have normalEq :
                dualCappedMultipleBlockFiveNormalList (x :: y :: ys) =
                  x :: x :: x :: without := by
              change
                List.replicate
                    (dualCappedMultipleBlockFiveExponent
                      ((x :: y :: ys).count x)) x ++
                    (dualCappedMultipleBlockFiveNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: x :: without
              rw [targetExponent, if_neg hsmall, countThree]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countThree]
              simpa using
                dualCappedMultipleBlockFiveContractLeadingFour x without
termination_by
  _ xs => xs.length

theorem dualCappedMultipleBlockFiveDerivesNormal (w : Word Nat) :
    match dualCappedMultipleBlockFiveNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives dualCappedMultipleBlockFiveBasis w
          (dualCappedMultipleBlockFiveWordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact dualCappedMultipleBlockFiveDerivesNormalizeList head tail

private theorem dualCappedMultipleBlockFiveNormal_count_head
    {x : Nat} {xs : List Nat}
    (normal : DualCappedMultipleBlockFiveNormal (x :: xs)) :
    (x :: xs).count x = 1 ∨
      (x :: xs).count x = 2 ∨
      (x :: xs).count x = 3 := by
  cases normal with
  | single _ tail _ notMem =>
      simp [List.count_eq_zero.mpr notMem]
  | double _ tail _ notMem =>
      simp [List.count_eq_zero.mpr notMem]
  | triple _ tail _ notMem =>
      simp [List.count_eq_zero.mpr notMem]

private theorem dualCappedMultipleBlockFiveDerivesSwapLeadingMultiples
    (x y : Nat) (xCount yCount : Nat) (suffix : List Nat)
    (hx : xCount = 2 ∨ xCount = 3)
    (hy : yCount = 2 ∨ yCount = 3) :
    Derives dualCappedMultipleBlockFiveBasis
      (dualCappedMultipleBlockFiveWordOfCons x
        (List.replicate (xCount - 1) x ++
          List.replicate yCount y ++ suffix))
      (dualCappedMultipleBlockFiveWordOfCons y
        (List.replicate (yCount - 1) y ++
          List.replicate xCount x ++ suffix)) := by
  rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl
  · have core :=
      dualCappedMultipleBlockFiveDerivesSquareSquareCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualCappedMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualCappedMultipleBlockFiveDerivesSquareCubeCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualCappedMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualCappedMultipleBlockFiveDerivesCubeSquareCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualCappedMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualCappedMultipleBlockFiveDerivesCubeCubeCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualCappedMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualCappedMultipleBlockFiveWordOfCons z zs)

private theorem dualCappedMultipleBlockFiveNormalDerivesOfCounts
    {x y : Nat} {xs ys : List Nat}
    (normalX : DualCappedMultipleBlockFiveNormal (x :: xs))
    (normalY : DualCappedMultipleBlockFiveNormal (y :: ys))
    (counts : ∀ z, (x :: xs).count z = (y :: ys).count z)
    (head :
      (if (x :: xs).count x = 1 then some x else none) =
        (if (y :: ys).count y = 1 then some y else none)) :
    Derives dualCappedMultipleBlockFiveBasis
      (dualCappedMultipleBlockFiveWordOfCons x xs)
      (dualCappedMultipleBlockFiveWordOfCons y ys) := by
  have xCases := dualCappedMultipleBlockFiveNormal_count_head normalX
  have yCases := dualCappedMultipleBlockFiveNormal_count_head normalY
  rcases xCases with hx1 | hx
  · have rhsSingleton :
        (y :: ys).count y = 1 := by
      rcases yCases with hy1 | hy
      · exact hy1
      · rcases hy with hy2 | hy3
        · simp [hx1, hy2] at head
        · simp [hx1, hy3] at head
    have hxy : x = y := by
      simpa [hx1, rhsSingleton] using head
    subst y
    have tailCounts : ∀ z, xs.count z = ys.count z := by
      intro z
      have h := counts z
      simp only [List.count_cons] at h
      split at h <;> omega
    have tailPerm : xs.Perm ys := by
      rw [List.perm_iff_count]
      exact tailCounts
    simpa [dualCappedMultipleBlockFiveAppendList,
      dualCappedMultipleBlockFiveWordOfCons] using
        dualCappedMultipleBlockFiveDerivesTailPermutation
          (Word.singleton x) tailPerm
  · have hxMulti :
        (x :: xs).count x = 2 ∨ (x :: xs).count x = 3 := hx
    have hy : (y :: ys).count y = 2 ∨
        (y :: ys).count y = 3 := by
      rcases yCases with hy1 | hy
      · rcases hxMulti with hx2 | hx3
        · simp [hx2, hy1] at head
        · simp [hx3, hy1] at head
      · exact hy
    by_cases hxy : x = y
    · subst y
      have tailPerm : xs.Perm ys := by
        rw [List.perm_iff_count]
        intro z
        have h := counts z
        simp only [List.count_cons] at h
        split at h <;> omega
      simpa [dualCappedMultipleBlockFiveAppendList,
        dualCappedMultipleBlockFiveWordOfCons] using
          dualCappedMultipleBlockFiveDerivesTailPermutation
            (Word.singleton x) tailPerm
    · let xCount := (x :: xs).count x
      let yCount := (y :: ys).count y
      let remainder :=
        (xs.filter (fun z => decide (z ≠ x))).filter
          (fun z => decide (z ≠ y))
      have xTailCount : xs.count x = xCount - 1 := by
        simp [xCount]
      have xsCountY : xs.count y = yCount := by
        simpa [yCount, hxy] using counts y
      have remainderCountX : remainder.count x = 0 := by
        change
          (((xs.filter (fun z => decide (z ≠ x))).filter
              (fun z => decide (z ≠ y))).count x) = 0
        rw [dualCappedMultipleBlockFiveCount_filter_ne_of_ne hxy]
        exact dualCappedMultipleBlockFiveCount_filter_ne_self x xs
      have remainderCountY : remainder.count y = 0 := by
        exact dualCappedMultipleBlockFiveCount_filter_ne_self y _
      have remainderCountOther :
          ∀ z, z ≠ x → z ≠ y → remainder.count z = xs.count z := by
        intro z hzx hzy
        rw [dualCappedMultipleBlockFiveCount_filter_ne_of_ne hzy]
        exact dualCappedMultipleBlockFiveCount_filter_ne_of_ne hzx xs
      have arrangePerm :
          xs.Perm
            (List.replicate (xCount - 1) x ++
              List.replicate yCount y ++ remainder) := by
        rw [List.perm_iff_count]
        intro z
        by_cases hzx : z = x
        · subst z
          rw [List.count_append, List.count_append,
            List.count_replicate_self,
            dualCappedMultipleBlockFiveCount_replicate_of_ne hxy,
            remainderCountX, xTailCount]
          omega
        · by_cases hzy : z = y
          · subst z
            rw [List.count_append, List.count_append,
              dualCappedMultipleBlockFiveCount_replicate_of_ne
                (Ne.symm hxy),
              List.count_replicate_self, remainderCountY, xsCountY]
            omega
          · rw [List.count_append, List.count_append,
              dualCappedMultipleBlockFiveCount_replicate_of_ne hzx,
              dualCappedMultipleBlockFiveCount_replicate_of_ne hzy,
              remainderCountOther z hzx hzy]
            omega
      have first :=
        dualCappedMultipleBlockFiveDerivesTailPermutation
          (Word.singleton x) arrangePerm
      have swapped :=
        dualCappedMultipleBlockFiveDerivesSwapLeadingMultiples
          x y xCount yCount remainder
          (by simpa [xCount] using hxMulti)
          (by simpa [yCount] using hy)
      have finalTailPerm :
          (List.replicate (yCount - 1) y ++
              List.replicate xCount x ++ remainder).Perm ys := by
        rw [List.perm_iff_count]
        intro z
        have total := counts z
        by_cases hzy : z = y
        · subst z
          have yTailCount : ys.count y = yCount - 1 := by
            simp [yCount]
          rw [List.count_append, List.count_append,
            List.count_replicate_self,
            dualCappedMultipleBlockFiveCount_replicate_of_ne
              (Ne.symm hxy),
            remainderCountY, yTailCount]
          omega
        · by_cases hzx : z = x
          · subst z
            have ysCountX : ys.count x = xCount := by
              have h := counts x
              simp [Ne.symm hxy] at h
              simpa [xCount] using h.symm
            rw [List.count_append, List.count_append,
              dualCappedMultipleBlockFiveCount_replicate_of_ne hxy,
              List.count_replicate_self, remainderCountX, ysCountX]
            omega
          · rw [List.count_append, List.count_append,
              dualCappedMultipleBlockFiveCount_replicate_of_ne hzy,
              dualCappedMultipleBlockFiveCount_replicate_of_ne hzx,
              remainderCountOther z hzx hzy]
            simp [Ne.symm hzx, Ne.symm hzy] at total
            omega
      have final :=
        dualCappedMultipleBlockFiveDerivesTailPermutation
          (Word.singleton y) finalTailPerm
      exact Derives.trans
        (by simpa [dualCappedMultipleBlockFiveAppendList,
          dualCappedMultipleBlockFiveWordOfCons] using first) <|
        Derives.trans swapped <| by
          simpa [dualCappedMultipleBlockFiveAppendList,
            dualCappedMultipleBlockFiveWordOfCons] using final

private theorem dualCappedMultipleBlockFiveSingletonHead_normal
    (w : Word Nat) :
    match dualCappedMultipleBlockFiveNormalList w.toList with
    | [] => False
    | x :: xs =>
        (if (x :: xs).count x = 1 then some x else none) =
          dualCappedMultipleBlockFiveSingletonHead w := by
  cases w with
  | mk head tail =>
      change
        match dualCappedMultipleBlockFiveNormalList (head :: tail) with
        | [] => False
        | x :: xs =>
            (if (x :: xs).count x = 1 then some x else none) =
              dualCappedMultipleBlockFiveSingletonHead ⟨head, tail⟩
      have nonempty :=
        dualCappedMultipleBlockFiveNormalList_cons_ne_nil head tail
      cases hn :
          dualCappedMultipleBlockFiveNormalList (head :: tail) with
      | nil => exact False.elim (nonempty hn)
      | cons x xs =>
          have headEq : x = head := by
            have positive :
                0 <
                  dualCappedMultipleBlockFiveExponent
                    ((head :: tail).count head) :=
              dualCappedMultipleBlockFiveExponent_pos (by simp)
            cases h :
                dualCappedMultipleBlockFiveExponent
                  ((head :: tail).count head) with
            | zero => omega
            | succ n =>
                simp only [dualCappedMultipleBlockFiveNormalList, h,
                  List.replicate_succ, List.cons_append] at hn
                injection hn with hhead
                exact hhead.symm
          subst x
          simp only
          have countEq :=
            dualCappedMultipleBlockFiveNormalList_count head (head :: tail)
          rw [hn] at countEq
          have positive : 0 < (head :: tail).count head := by simp
          unfold dualCappedMultipleBlockFiveSingletonHead
          change
            (if (head :: xs).count head = 1 then some head else none) =
              if (head :: tail).count head = 1 then some head else none
          rw [countEq]
          by_cases hone : (head :: tail).count head = 1
          · have expOne :
                dualCappedMultipleBlockFiveExponent
                    ((head :: tail).count head) = 1 :=
              (dualCappedMultipleBlockFiveExponent_eq_one_iff positive).2 hone
            rw [if_pos expOne, if_pos hone]
          · have expNe :
                dualCappedMultipleBlockFiveExponent
                    ((head :: tail).count head) ≠ 1 := by
              exact fun h =>
                hone ((dualCappedMultipleBlockFiveExponent_eq_one_iff
                  positive).1 h)
            rw [if_neg expNe, if_neg hone]

/-- Unrestricted syntactic completeness for the opposite-orientation
`S5_209` basis. The normalized exponent of every variable and the optional
singleton head are the complete derivation invariants. -/
theorem dualCappedMultipleBlockFiveDerivesOfInvariantEq
    (u v : Word Nat)
    (counts :
      ∀ z,
        dualCappedMultipleBlockFiveExponent (u.toList.count z) =
          dualCappedMultipleBlockFiveExponent (v.toList.count z))
    (head :
      dualCappedMultipleBlockFiveSingletonHead u =
        dualCappedMultipleBlockFiveSingletonHead v) :
    Derives dualCappedMultipleBlockFiveBasis u v := by
  have uNormal := dualCappedMultipleBlockFiveDerivesNormal u
  have vNormal := dualCappedMultipleBlockFiveDerivesNormal v
  have uHeadNormal := dualCappedMultipleBlockFiveSingletonHead_normal u
  have vHeadNormal := dualCappedMultipleBlockFiveSingletonHead_normal v
  cases hu : dualCappedMultipleBlockFiveNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : dualCappedMultipleBlockFiveNormalList v.toList with
      | nil =>
          exact False.elim <| by
            rw [hv] at vNormal
            exact vNormal
      | cons vx vxs =>
          rw [hu] at uNormal
          rw [hv] at vNormal
          rw [hu] at uHeadNormal
          rw [hv] at vHeadNormal
          have normalCounts :
              ∀ z, (ux :: uxs).count z = (vx :: vxs).count z := by
            intro z
            have left :=
              dualCappedMultipleBlockFiveNormalList_count z u.toList
            have right :=
              dualCappedMultipleBlockFiveNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            exact left.trans ((counts z).trans right.symm)
          have normalHead :
              (if (ux :: uxs).count ux = 1 then some ux else none) =
                (if (vx :: vxs).count vx = 1 then some vx else none) := by
            exact uHeadNormal.trans (head.trans vHeadNormal.symm)
          have bridge :=
            dualCappedMultipleBlockFiveNormalDerivesOfCounts
              (by
                simpa [hu] using
                  dualCappedMultipleBlockFiveNormalList_normal u.toList)
              (by
                simpa [hv] using
                  dualCappedMultipleBlockFiveNormalList_normal v.toList)
              normalCounts normalHead
          exact Derives.trans uNormal <|
            Derives.trans bridge (Derives.symm vNormal)

end SemigroupBasis.Examples

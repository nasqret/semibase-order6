import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def dualMultipleBlockFiveXX : Word Nat := ⟨0, [0]⟩
def dualMultipleBlockFiveXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def dualMultipleBlockFiveXYX : Word Nat := ⟨0, [1, 0]⟩
def dualMultipleBlockFiveXXY : Word Nat := ⟨0, [0, 1]⟩
def dualMultipleBlockFiveXYZ : Word Nat := ⟨0, [1, 2]⟩
def dualMultipleBlockFiveXZY : Word Nat := ⟨0, [2, 1]⟩
def dualMultipleBlockFiveYYXX : Word Nat := ⟨1, [1, 0, 0]⟩
def dualMultipleBlockFiveXYYX : Word Nat := ⟨0, [1, 1, 0]⟩

def dualMultipleBlockFivePowerLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveXX, dualMultipleBlockFiveXXXX⟩

def dualMultipleBlockFiveGatherLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveXYX, dualMultipleBlockFiveXXY⟩

def dualMultipleBlockFiveSuffixSwapLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveXYZ, dualMultipleBlockFiveXZY⟩

def dualMultipleBlockFiveSquareRotationLaw : Identity Nat :=
  ⟨dualMultipleBlockFiveYYXX, dualMultipleBlockFiveXYYX⟩

/-- The opposite-orientation `S5_121` basis
`xx = xxxx`, `xyx = xxy`, `xyz = xzy`, `yyxx = xyyx`. -/
def dualMultipleBlockFiveBasis : List (Identity Nat) :=
  [dualMultipleBlockFivePowerLaw, dualMultipleBlockFiveGatherLaw,
    dualMultipleBlockFiveSuffixSwapLaw,
    dualMultipleBlockFiveSquareRotationLaw]

private def dualMultipleBlockFiveInstantiate
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract four consecutive copies of any nonempty block to two copies. -/
theorem dualMultipleBlockFiveDerivesFourToTwo (u : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives dualMultipleBlockFiveBasis
        dualMultipleBlockFiveXXXX dualMultipleBlockFiveXX :=
    Derives.symm <|
      Derives.fromBasis (e := dualMultipleBlockFivePowerLaw) <|
        List.Mem.head _
  have h :=
    Derives.subst hbase (dualMultipleBlockFiveInstantiate u u u)
  simpa [dualMultipleBlockFiveBasis, dualMultipleBlockFivePowerLaw,
    dualMultipleBlockFiveXXXX, dualMultipleBlockFiveXX,
    dualMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Gather the final copy of a block next to its initial copy. -/
theorem dualMultipleBlockFiveDerivesGather (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives dualMultipleBlockFiveBasis
        dualMultipleBlockFiveXYX dualMultipleBlockFiveXXY :=
    Derives.fromBasis (e := dualMultipleBlockFiveGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (dualMultipleBlockFiveInstantiate u v u)
  simpa [dualMultipleBlockFiveBasis, dualMultipleBlockFiveGatherLaw,
    dualMultipleBlockFiveXYX, dualMultipleBlockFiveXXY,
    dualMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Swap two blocks following an arbitrary nonempty prefix block. -/
theorem dualMultipleBlockFiveDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives dualMultipleBlockFiveBasis
        dualMultipleBlockFiveXYZ dualMultipleBlockFiveXZY :=
    Derives.fromBasis (e := dualMultipleBlockFiveSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h :=
    Derives.subst hbase (dualMultipleBlockFiveInstantiate p u v)
  simpa [dualMultipleBlockFiveBasis,
    dualMultipleBlockFiveSuffixSwapLaw, dualMultipleBlockFiveXYZ,
    dualMultipleBlockFiveXZY, dualMultipleBlockFiveInstantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private theorem dualMultipleBlockFiveDerivesSquareRotation
    (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      ((u ++ (v ++ v)) ++ u) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives dualMultipleBlockFiveBasis
        dualMultipleBlockFiveXYYX dualMultipleBlockFiveYYXX :=
    Derives.symm <|
      Derives.fromBasis
        (e := dualMultipleBlockFiveSquareRotationLaw) <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (dualMultipleBlockFiveInstantiate u v u)
  simpa [dualMultipleBlockFiveBasis,
    dualMultipleBlockFiveSquareRotationLaw,
    dualMultipleBlockFiveXYYX, dualMultipleBlockFiveYYXX,
    dualMultipleBlockFiveInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Products of two square blocks commute. -/
theorem dualMultipleBlockFiveDerivesSquareSquareCommutation
    (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  exact Derives.trans
    (dualMultipleBlockFiveDerivesSuffixSwap u u (v ++ v))
    (dualMultipleBlockFiveDerivesSquareRotation u v)

/-- A cube block commutes past a square block. -/
theorem dualMultipleBlockFiveDerivesCubeSquareCommutation
    (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ (v ++ v))
      ((v ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.prepend u
      (dualMultipleBlockFiveDerivesSquareSquareCommutation u v)
  have second :=
    Derives.appendRight
      (dualMultipleBlockFiveDerivesSquareRotation u v) u
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- A square block commutes past a cube block. -/
theorem dualMultipleBlockFiveDerivesSquareCubeCommutation
    (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      ((u ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ (u ++ u)) := by
  have first :=
    Derives.appendRight
      (dualMultipleBlockFiveDerivesSquareSquareCommutation u v) v
  have second :=
    dualMultipleBlockFiveDerivesSuffixSwap (v ++ v) (u ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- Products of two cube blocks commute. -/
theorem dualMultipleBlockFiveDerivesCubeCubeCommutation
    (u v : Word Nat) :
    Derives dualMultipleBlockFiveBasis
      (((u ++ u) ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.appendRight
      (dualMultipleBlockFiveDerivesCubeSquareCommutation u v) v
  have second :=
    dualMultipleBlockFiveDerivesSuffixSwap
      (v ++ v) ((u ++ u) ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- The head is recorded exactly when it occurs only once in the word. -/
def dualMultipleBlockFiveSingletonHead (w : Word Nat) : Option Nat :=
  if w.toList.count w.head = 1 then some w.head else none

private def dualMultipleBlockFiveWordOfCons
    (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def dualMultipleBlockFiveAppendList
    (p : Word Nat) (xs : List Nat) : Word Nat :=
  ⟨p.head, p.tail ++ xs⟩

private theorem dualMultipleBlockFiveAppendList_cons
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    dualMultipleBlockFiveAppendList p (x :: xs) =
      p ++ dualMultipleBlockFiveWordOfCons x xs := by
  apply Word.toList_injective
  simp [dualMultipleBlockFiveAppendList,
    dualMultipleBlockFiveWordOfCons, Word.toList]

private theorem dualMultipleBlockFiveAppendList_cons_prefix
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    dualMultipleBlockFiveAppendList p (x :: xs) =
      dualMultipleBlockFiveAppendList
        (p ++ Word.singleton x) xs := by
  apply Word.toList_injective
  simp [dualMultipleBlockFiveAppendList, Word.toList,
    List.append_assoc]

@[simp]
private theorem dualMultipleBlockFiveAppendList_toList
    (p : Word Nat) (xs : List Nat) :
    (dualMultipleBlockFiveAppendList p xs).toList =
      p.toList ++ xs := by
  cases xs <;>
    simp [dualMultipleBlockFiveAppendList, Word.toList]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
private theorem dualMultipleBlockFiveDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives dualMultipleBlockFiveBasis
      (dualMultipleBlockFiveAppendList p xs)
      (dualMultipleBlockFiveAppendList p ys) := by
  induction h generalizing p with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have h := ih (p ++ Word.singleton x)
      rw [dualMultipleBlockFiveAppendList_cons_prefix,
        dualMultipleBlockFiveAppendList_cons_prefix]
      exact h
  | swap x y xs =>
      cases xs with
      | nil =>
          rw [dualMultipleBlockFiveAppendList_cons,
            dualMultipleBlockFiveAppendList_cons]
          simpa [dualMultipleBlockFiveWordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using
            dualMultipleBlockFiveDerivesSuffixSwap p
              (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (dualMultipleBlockFiveDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (dualMultipleBlockFiveWordOfCons z zs)
          rw [dualMultipleBlockFiveAppendList_cons,
            dualMultipleBlockFiveAppendList_cons]
          simpa [dualMultipleBlockFiveWordOfCons,
            Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

private theorem dualMultipleBlockFiveExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem dualMultipleBlockFiveExponent_eq_one_iff
    {n : Nat} (positive : 0 < n) :
    periodTwoFromTwoExponent n = 1 ↔ n = 1 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem dualMultipleBlockFiveCount_replicate_of_ne
    {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        dualMultipleBlockFiveCount_replicate_of_ne hzx n]

private theorem dualMultipleBlockFiveCount_filter_ne_self
    (x : Nat) (xs : List Nat) :
    (xs.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem dualMultipleBlockFiveCount_filter_ne_of_ne
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
`periodTwoFromTwoExponent`. -/
def dualMultipleBlockFiveNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := dualMultipleBlockFiveNormalList xs
      List.replicate
          (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem dualMultipleBlockFiveNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (dualMultipleBlockFiveNormalList xs).count z =
        periodTwoFromTwoExponent (xs.count z)
  | [] => by
      simp [dualMultipleBlockFiveNormalList,
        periodTwoFromTwoExponent]
  | x :: xs => by
      simp only [dualMultipleBlockFiveNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self,
          dualMultipleBlockFiveCount_filter_ne_self]
        omega
      · rw [dualMultipleBlockFiveCount_replicate_of_ne hzx,
          dualMultipleBlockFiveCount_filter_ne_of_ne hzx,
          Nat.zero_add, dualMultipleBlockFiveNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem dualMultipleBlockFiveNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    dualMultipleBlockFiveNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    dualMultipleBlockFiveNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    periodTwoFromTwoExponent_pos (by omega)) countEq.symm

/-- Lists consisting of one first-occurrence block of length one, two, or
three for each variable. -/
inductive DualMultipleBlockFiveNormal : List Nat → Prop
  | nil : DualMultipleBlockFiveNormal []
  | single (x : Nat) (xs : List Nat) :
      DualMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualMultipleBlockFiveNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      DualMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualMultipleBlockFiveNormal (x :: x :: xs)
  | triple (x : Nat) (xs : List Nat) :
      DualMultipleBlockFiveNormal xs →
      x ∉ xs →
      DualMultipleBlockFiveNormal (x :: x :: x :: xs)

private theorem DualMultipleBlockFiveNormal.filter_ne
    {xs : List Nat} (normal : DualMultipleBlockFiveNormal xs) (x : Nat) :
    DualMultipleBlockFiveNormal
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
          DualMultipleBlockFiveNormal.single y _ ih yNotMemFilter
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
          DualMultipleBlockFiveNormal.double y _ ih yNotMemFilter
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
          DualMultipleBlockFiveNormal.triple y _ ih yNotMemFilter

theorem dualMultipleBlockFiveNormalList_normal :
    ∀ xs : List Nat,
      DualMultipleBlockFiveNormal
        (dualMultipleBlockFiveNormalList xs)
  | [] => .nil
  | x :: xs => by
      let rest := dualMultipleBlockFiveNormalList xs
      have restNormal := dualMultipleBlockFiveNormalList_normal xs
      have filteredNormal := restNormal.filter_ne x
      have xNotMem :
          x ∉ rest.filter (fun y => decide (y ≠ x)) := by
        simp
      have positive :
          0 < periodTwoFromTwoExponent ((x :: xs).count x) :=
        periodTwoFromTwoExponent_pos (by simp)
      have bound :=
        dualMultipleBlockFiveExponent_le_three ((x :: xs).count x)
      have cases :
          periodTwoFromTwoExponent ((x :: xs).count x) = 1 ∨
            periodTwoFromTwoExponent ((x :: xs).count x) = 2 ∨
              periodTwoFromTwoExponent ((x :: xs).count x) = 3 := by
        omega
      rcases cases with h | h | h
      · change DualMultipleBlockFiveNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualMultipleBlockFiveNormal.single x _ filteredNormal xNotMem
      · change DualMultipleBlockFiveNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualMultipleBlockFiveNormal.double x _ filteredNormal xNotMem
      · change DualMultipleBlockFiveNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          DualMultipleBlockFiveNormal.triple x _ filteredNormal xNotMem

private theorem dualMultipleBlockFivePerm_extract
    (x : Nat) (xs : List Nat) :
    xs.Perm
      (List.replicate (xs.count x) x ++
        xs.filter (fun y => decide (y ≠ x))) := by
  rw [List.perm_iff_count]
  intro z
  by_cases hzx : z = x
  · subst z
    rw [List.count_append, List.count_replicate_self,
      dualMultipleBlockFiveCount_filter_ne_self]
    omega
  · rw [List.count_append,
      dualMultipleBlockFiveCount_replicate_of_ne hzx,
      dualMultipleBlockFiveCount_filter_ne_of_ne hzx]
    omega

private theorem dualMultipleBlockFiveContractLeadingFour
    (x : Nat) (suffix : List Nat) :
    Derives dualMultipleBlockFiveBasis
      (dualMultipleBlockFiveWordOfCons x (x :: x :: x :: suffix))
      (dualMultipleBlockFiveWordOfCons x (x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [dualMultipleBlockFiveWordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using
          dualMultipleBlockFiveDerivesFourToTwo (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (dualMultipleBlockFiveDerivesFourToTwo (Word.singleton x))
          (dualMultipleBlockFiveWordOfCons y ys)
      simpa [dualMultipleBlockFiveWordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using h

private theorem dualMultipleBlockFiveDerivesNormalizeList :
    ∀ x xs,
      match dualMultipleBlockFiveNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives dualMultipleBlockFiveBasis
            (dualMultipleBlockFiveWordOfCons x xs)
            (dualMultipleBlockFiveWordOfCons y ys)
  | x, [] => by
      have normalEq :
          dualMultipleBlockFiveNormalList [x] = [x] := by
        simp [dualMultipleBlockFiveNormalList,
          periodTwoFromTwoExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        dualMultipleBlockFiveDerivesNormalizeList y ys
      cases hn : dualMultipleBlockFiveNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            dualMultipleBlockFiveNormalList_cons_ne_nil y ys hn
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
            exact dualMultipleBlockFivePerm_extract x rest
          have arranged :=
            dualMultipleBlockFiveDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                periodTwoFromTwoExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              dualMultipleBlockFiveNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 3 := by
            rw [restCount]
            exact dualMultipleBlockFiveExponent_le_three _
          have targetExponent :
              periodTwoFromTwoExponent ((x :: y :: ys).count x) =
                if rest.count x < 3 then rest.count x + 1
                else rest.count x - 1 := by
            rw [List.count_cons_self, periodTwoFromTwoExponent_succ,
              ← restCount]
          have first :
              Derives dualMultipleBlockFiveBasis
                (dualMultipleBlockFiveWordOfCons x (y :: ys))
                (dualMultipleBlockFiveWordOfCons x
                  (List.replicate (rest.count x) x ++ without)) :=
            Derives.trans
              (by
                simpa [dualMultipleBlockFiveWordOfCons, Word.append,
                  Word.singleton, Word.append_assoc] using prefixed)
              (by
                simpa [dualMultipleBlockFiveAppendList,
                  dualMultipleBlockFiveWordOfCons, Word.singleton,
                  rest, without] using
                    arranged)
          by_cases hsmall : rest.count x < 3
          · have normalEq :
                dualMultipleBlockFiveNormalList (x :: y :: ys) =
                  x ::
                    List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x)) x ++
                    (dualMultipleBlockFiveNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn]
              rw [List.replicate_succ]
            rw [normalEq]
            exact first
          · have countThree : rest.count x = 3 := by omega
            have normalEq :
                dualMultipleBlockFiveNormalList (x :: y :: ys) =
                  x :: x :: without := by
              change
                List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x)) x ++
                    (dualMultipleBlockFiveNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: without
              rw [targetExponent, if_neg hsmall, countThree]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countThree]
              simpa using
                dualMultipleBlockFiveContractLeadingFour x without
termination_by
  _ xs => xs.length

theorem dualMultipleBlockFiveDerivesNormal (w : Word Nat) :
    match dualMultipleBlockFiveNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives dualMultipleBlockFiveBasis w
          (dualMultipleBlockFiveWordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact dualMultipleBlockFiveDerivesNormalizeList head tail

private theorem dualMultipleBlockFiveNormal_count_head
    {x : Nat} {xs : List Nat}
    (normal : DualMultipleBlockFiveNormal (x :: xs)) :
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

private theorem dualMultipleBlockFiveDerivesSwapLeadingMultiples
    (x y : Nat) (xCount yCount : Nat) (suffix : List Nat)
    (hx : xCount = 2 ∨ xCount = 3)
    (hy : yCount = 2 ∨ yCount = 3) :
    Derives dualMultipleBlockFiveBasis
      (dualMultipleBlockFiveWordOfCons x
        (List.replicate (xCount - 1) x ++
          List.replicate yCount y ++ suffix))
      (dualMultipleBlockFiveWordOfCons y
        (List.replicate (yCount - 1) y ++
          List.replicate xCount x ++ suffix)) := by
  rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl
  · have core :=
      dualMultipleBlockFiveDerivesSquareSquareCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualMultipleBlockFiveDerivesSquareCubeCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualMultipleBlockFiveDerivesCubeSquareCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualMultipleBlockFiveWordOfCons z zs)
  · have core :=
      dualMultipleBlockFiveDerivesCubeCubeCommutation
        (Word.singleton x) (Word.singleton y)
    cases suffix with
    | nil =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using core
    | cons z zs =>
        simpa [dualMultipleBlockFiveWordOfCons, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.appendRight core
              (dualMultipleBlockFiveWordOfCons z zs)

private theorem dualMultipleBlockFiveNormalDerivesOfCounts
    {x y : Nat} {xs ys : List Nat}
    (normalX : DualMultipleBlockFiveNormal (x :: xs))
    (normalY : DualMultipleBlockFiveNormal (y :: ys))
    (counts : ∀ z, (x :: xs).count z = (y :: ys).count z)
    (head :
      (if (x :: xs).count x = 1 then some x else none) =
        (if (y :: ys).count y = 1 then some y else none)) :
    Derives dualMultipleBlockFiveBasis
      (dualMultipleBlockFiveWordOfCons x xs)
      (dualMultipleBlockFiveWordOfCons y ys) := by
  have xCases := dualMultipleBlockFiveNormal_count_head normalX
  have yCases := dualMultipleBlockFiveNormal_count_head normalY
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
    simpa [dualMultipleBlockFiveAppendList,
      dualMultipleBlockFiveWordOfCons] using
        dualMultipleBlockFiveDerivesTailPermutation
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
      simpa [dualMultipleBlockFiveAppendList,
        dualMultipleBlockFiveWordOfCons] using
          dualMultipleBlockFiveDerivesTailPermutation
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
        rw [dualMultipleBlockFiveCount_filter_ne_of_ne hxy]
        exact dualMultipleBlockFiveCount_filter_ne_self x xs
      have remainderCountY : remainder.count y = 0 := by
        exact dualMultipleBlockFiveCount_filter_ne_self y _
      have remainderCountOther :
          ∀ z, z ≠ x → z ≠ y → remainder.count z = xs.count z := by
        intro z hzx hzy
        rw [dualMultipleBlockFiveCount_filter_ne_of_ne hzy]
        exact dualMultipleBlockFiveCount_filter_ne_of_ne hzx xs
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
            dualMultipleBlockFiveCount_replicate_of_ne hxy,
            remainderCountX, xTailCount]
          omega
        · by_cases hzy : z = y
          · subst z
            rw [List.count_append, List.count_append,
              dualMultipleBlockFiveCount_replicate_of_ne
                (Ne.symm hxy),
              List.count_replicate_self, remainderCountY, xsCountY]
            omega
          · rw [List.count_append, List.count_append,
              dualMultipleBlockFiveCount_replicate_of_ne hzx,
              dualMultipleBlockFiveCount_replicate_of_ne hzy,
              remainderCountOther z hzx hzy]
            omega
      have first :=
        dualMultipleBlockFiveDerivesTailPermutation
          (Word.singleton x) arrangePerm
      have swapped :=
        dualMultipleBlockFiveDerivesSwapLeadingMultiples
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
            dualMultipleBlockFiveCount_replicate_of_ne
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
              dualMultipleBlockFiveCount_replicate_of_ne hxy,
              List.count_replicate_self, remainderCountX, ysCountX]
            omega
          · rw [List.count_append, List.count_append,
              dualMultipleBlockFiveCount_replicate_of_ne hzy,
              dualMultipleBlockFiveCount_replicate_of_ne hzx,
              remainderCountOther z hzx hzy]
            simp [Ne.symm hzx, Ne.symm hzy] at total
            omega
      have final :=
        dualMultipleBlockFiveDerivesTailPermutation
          (Word.singleton y) finalTailPerm
      exact Derives.trans
        (by simpa [dualMultipleBlockFiveAppendList,
          dualMultipleBlockFiveWordOfCons] using first) <|
        Derives.trans swapped <| by
          simpa [dualMultipleBlockFiveAppendList,
            dualMultipleBlockFiveWordOfCons] using final

private theorem dualMultipleBlockFiveSingletonHead_normal
    (w : Word Nat) :
    match dualMultipleBlockFiveNormalList w.toList with
    | [] => False
    | x :: xs =>
        (if (x :: xs).count x = 1 then some x else none) =
          dualMultipleBlockFiveSingletonHead w := by
  cases w with
  | mk head tail =>
      change
        match dualMultipleBlockFiveNormalList (head :: tail) with
        | [] => False
        | x :: xs =>
            (if (x :: xs).count x = 1 then some x else none) =
              dualMultipleBlockFiveSingletonHead ⟨head, tail⟩
      have nonempty :=
        dualMultipleBlockFiveNormalList_cons_ne_nil head tail
      cases hn :
          dualMultipleBlockFiveNormalList (head :: tail) with
      | nil => exact False.elim (nonempty hn)
      | cons x xs =>
          have headEq : x = head := by
            have positive :
                0 <
                  periodTwoFromTwoExponent
                    ((head :: tail).count head) :=
              periodTwoFromTwoExponent_pos (by simp)
            cases h :
                periodTwoFromTwoExponent
                  ((head :: tail).count head) with
            | zero => omega
            | succ n =>
                simp only [dualMultipleBlockFiveNormalList, h,
                  List.replicate_succ, List.cons_append] at hn
                injection hn with hhead
                exact hhead.symm
          subst x
          simp only
          have countEq :=
            dualMultipleBlockFiveNormalList_count head (head :: tail)
          rw [hn] at countEq
          have positive : 0 < (head :: tail).count head := by simp
          unfold dualMultipleBlockFiveSingletonHead
          change
            (if (head :: xs).count head = 1 then some head else none) =
              if (head :: tail).count head = 1 then some head else none
          rw [countEq]
          by_cases hone : (head :: tail).count head = 1
          · have expOne :
                periodTwoFromTwoExponent
                    ((head :: tail).count head) = 1 :=
              (dualMultipleBlockFiveExponent_eq_one_iff positive).2 hone
            rw [if_pos expOne, if_pos hone]
          · have expNe :
                periodTwoFromTwoExponent
                    ((head :: tail).count head) ≠ 1 := by
              exact fun h =>
                hone ((dualMultipleBlockFiveExponent_eq_one_iff
                  positive).1 h)
            rw [if_neg expNe, if_neg hone]

/-- Unrestricted syntactic completeness for the opposite-orientation
`S5_121` basis. The normalized exponent of every variable and the optional
singleton head are the complete derivation invariants. -/
theorem dualMultipleBlockFiveDerivesOfInvariantEq
    (u v : Word Nat)
    (counts :
      ∀ z,
        periodTwoFromTwoExponent (u.toList.count z) =
          periodTwoFromTwoExponent (v.toList.count z))
    (head :
      dualMultipleBlockFiveSingletonHead u =
        dualMultipleBlockFiveSingletonHead v) :
    Derives dualMultipleBlockFiveBasis u v := by
  have uNormal := dualMultipleBlockFiveDerivesNormal u
  have vNormal := dualMultipleBlockFiveDerivesNormal v
  have uHeadNormal := dualMultipleBlockFiveSingletonHead_normal u
  have vHeadNormal := dualMultipleBlockFiveSingletonHead_normal v
  cases hu : dualMultipleBlockFiveNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : dualMultipleBlockFiveNormalList v.toList with
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
              dualMultipleBlockFiveNormalList_count z u.toList
            have right :=
              dualMultipleBlockFiveNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            exact left.trans ((counts z).trans right.symm)
          have normalHead :
              (if (ux :: uxs).count ux = 1 then some ux else none) =
                (if (vx :: vxs).count vx = 1 then some vx else none) := by
            exact uHeadNormal.trans (head.trans vHeadNormal.symm)
          have bridge :=
            dualMultipleBlockFiveNormalDerivesOfCounts
              (by
                simpa [hu] using
                  dualMultipleBlockFiveNormalList_normal u.toList)
              (by
                simpa [hv] using
                  dualMultipleBlockFiveNormalList_normal v.toList)
              normalCounts normalHead
          exact Derives.trans uNormal <|
            Derives.trans bridge (Derives.symm vNormal)

end SemigroupBasis.Examples

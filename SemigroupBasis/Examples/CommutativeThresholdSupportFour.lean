import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based form of the stored `S4_38` table
`[[1,1,1,1],[1,1,1,1],[1,1,2,1],[1,1,1,4]]`. -/
def thresholdSupportFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0
  else if a = 1 then 0
  else if a = 2 then
    if b = 2 then 1 else 0
  else
    if b = 3 then 3 else 0

/-- The Smallsemi representative `S4_38`. -/
def thresholdSupportFour : FiniteTable where
  order := 4
  mul := thresholdSupportFourMul
  assoc := by decide

def thresholdXY : Word Nat := ⟨0, [1]⟩
def thresholdYX : Word Nat := ⟨1, [0]⟩
def thresholdXXX : Word Nat := ⟨0, [0, 0]⟩
def thresholdXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def thresholdXXY : Word Nat := ⟨0, [0, 1]⟩
def thresholdXYY : Word Nat := ⟨0, [1, 1]⟩
def thresholdXXXY : Word Nat := ⟨0, [0, 0, 1]⟩
def thresholdXYZ : Word Nat := ⟨0, [1, 2]⟩
def thresholdXXYZ : Word Nat := ⟨0, [0, 1, 2]⟩

def thresholdCommutativityLaw : Identity Nat :=
  ⟨thresholdXY, thresholdYX⟩

def thresholdPowerLaw : Identity Nat :=
  ⟨thresholdXXX, thresholdXXXX⟩

def thresholdHeavyTransferLaw : Identity Nat :=
  ⟨thresholdXXY, thresholdXYY⟩

def thresholdHeavyInsertionLaw : Identity Nat :=
  ⟨thresholdXXY, thresholdXXXY⟩

def thresholdLongInsertionLaw : Identity Nat :=
  ⟨thresholdXYZ, thresholdXXYZ⟩

/-- The established basis
`xy = yx`, `xxx = xxxx`, `xxy = xyy`, `xxy = xxxy`,
`xyz = xxyz`. -/
def commutativeThresholdSupportBasis : List (Identity Nat) :=
  [thresholdCommutativityLaw, thresholdPowerLaw,
    thresholdHeavyTransferLaw, thresholdHeavyInsertionLaw,
    thresholdLongInsertionLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem thresholdDerivesCommutativity (u v : Word Nat) :
    Derives commutativeThresholdSupportBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeThresholdSupportBasis thresholdXY thresholdYX :=
    Derives.fromBasis (e := thresholdCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [commutativeThresholdSupportBasis, thresholdCommutativityLaw,
    thresholdXY, thresholdYX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton] using h

theorem thresholdDerivesLongDuplication
    (u v w : Word Nat) :
    Derives commutativeThresholdSupportBasis
      ((u ++ v) ++ w) (((u ++ u) ++ v) ++ w) := by
  have hbase :
      Derives commutativeThresholdSupportBasis
        thresholdXYZ thresholdXXYZ :=
    Derives.fromBasis (e := thresholdLongInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [commutativeThresholdSupportBasis, thresholdLongInsertionLaw,
    thresholdXYZ, thresholdXXYZ, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeThresholdSupportBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              thresholdDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (thresholdDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem thresholdDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeThresholdSupportBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain at most three copies of every variable. -/
def capThreeReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := capThreeReduce xs
      if reduced.count x < 3 then x :: reduced else reduced

theorem count_capThreeReduce (z : Nat) (xs : List Nat) :
    (capThreeReduce xs).count z = min (xs.count z) 3 := by
  induction xs with
  | nil =>
      simp [capThreeReduce]
  | cons x xs ih =>
      simp only [capThreeReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem capThreeReduce_cons_ne_nil (x : Nat) (xs : List Nat) :
    capThreeReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_capThreeReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

private theorem three_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 3) :
    xs.Perm (x :: x :: x :: ((xs.erase x).erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x (List.perm_cons_erase hx₂)

private theorem contractLeadingFour :
    ∀ x xs,
      Derives commutativeThresholdSupportBasis
        (wordOfCons x (x :: x :: x :: xs))
        (wordOfCons x (x :: x :: xs))
  | x, [] => by
      have hbase :
          Derives commutativeThresholdSupportBasis
            thresholdXXXX thresholdXXX :=
        Derives.symm <|
          Derives.fromBasis (e := thresholdPowerLaw) <| by
            exact List.Mem.tail _ (List.Mem.head _)
      simpa [thresholdXXXX, thresholdXXX, wordOfCons] using
        Derives.subst hbase
          (instantiateThreeWords
            (Word.singleton x) (Word.singleton x) (Word.singleton x))
  | x, y :: ys => by
      have hbase :
          Derives commutativeThresholdSupportBasis
            thresholdXXXX thresholdXXX :=
        Derives.symm <|
          Derives.fromBasis (e := thresholdPowerLaw) <| by
            exact List.Mem.tail _ (List.Mem.head _)
      have base :
          Derives commutativeThresholdSupportBasis
            (wordOfCons x [x, x, x])
            (wordOfCons x [x, x]) := by
        simpa [thresholdXXXX, thresholdXXX, wordOfCons] using
          Derives.subst hbase
            (instantiateThreeWords
              (Word.singleton x) (Word.singleton x) (Word.singleton x))
      have appended :=
        Derives.appendRight base (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using appended

private theorem thresholdDerivesNormalizeList :
    ∀ x xs,
      match capThreeReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativeThresholdSupportBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := thresholdDerivesNormalizeList y ys
      cases hs : capThreeReduce (y :: ys) with
      | nil =>
          exact False.elim (capThreeReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 3
          · have reduced :
                capThreeReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (capThreeReduce (y :: ys)).count x < 3 then
                  x :: capThreeReduce (y :: ys)
                else capThreeReduce (y :: ys)) = x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 3 := by
              rw [← hs, count_capThreeReduce]
              exact Nat.min_le_right _ _
            have countEq : (z :: zs).count x = 3 := by omega
            let remainder := (((z :: zs).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm (x :: x :: x :: remainder) := by
              simpa [remainder] using
                three_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrangedToReduced :
                (x :: x :: x :: remainder).Perm (z :: zs) :=
              suffixPerm.symm
            have arrange :
                Derives commutativeThresholdSupportBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: remainder)) :=
              thresholdDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFour x remainder
            have restore :
                Derives commutativeThresholdSupportBasis
                  (wordOfCons x (x :: x :: remainder))
                  (wordOfCons z zs) :=
              thresholdDerivesPermutation _ _ arrangedToReduced
            have reduced :
                capThreeReduce (x :: y :: ys) = z :: zs := by
              change
                (if (capThreeReduce (y :: ys)).count x < 3 then
                  x :: capThreeReduce (y :: ys)
                else capThreeReduce (y :: ys)) = z :: zs
              rw [hs, if_neg hcount]
            rw [reduced]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (Derives.trans arrange (Derives.trans contract restore))
termination_by
  _ xs => xs.length

theorem thresholdDerivesCapThreeNormal (w : Word Nat) :
    match capThreeReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeThresholdSupportBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact thresholdDerivesNormalizeList head tail

/-- A word with at least three letters derives to its square. -/
theorem thresholdDerivesSquare (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    Derives commutativeThresholdSupportBasis w (w ++ w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons next rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at hlong
          | cons third more =>
              let u := Word.singleton head
              let v₁ := Word.singleton next
              let v₂ := wordOfCons third more
              let v := v₁ ++ v₂
              have duplicateU :=
                thresholdDerivesLongDuplication u v₁ v₂
              have arrangeForV :
                  Derives commutativeThresholdSupportBasis
                    (((u ++ u) ++ v₁) ++ v₂)
                    ((v ++ u) ++ u) :=
                thresholdDerivesPermutation _ _ <| by
                  rw [List.perm_iff_count]
                  intro z
                  simp only [Word.toList_append, List.count_append]
                  unfold v
                  simp only [Word.toList_append, List.count_append]
                  omega
              have duplicateV :=
                thresholdDerivesLongDuplication v u u
              have finish :
                  Derives commutativeThresholdSupportBasis
                    (((v ++ v) ++ u) ++ u)
                    ((u ++ v) ++ (u ++ v)) :=
                thresholdDerivesPermutation _ _ <| by
                  rw [List.perm_iff_count]
                  intro z
                  simp only [Word.toList_append, List.count_append]
                  omega
              exact Derives.trans
                (by
                  simpa [u, v, v₁, v₂, wordOfCons,
                    Word.append_assoc] using duplicateU) <|
                Derives.trans arrangeForV <|
                Derives.trans duplicateV <| by
                  simpa [u, v, v₁, v₂, wordOfCons,
                    Word.append_assoc] using finish

/-- A word with at least three letters derives to its cube. -/
theorem thresholdDerivesCube (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    Derives commutativeThresholdSupportBasis
      w ((w ++ w) ++ w) := by
  have square := thresholdDerivesSquare w hlong
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons next rest =>
          let u := Word.singleton head
          let v := wordOfCons next rest
          have duplicateW :=
            thresholdDerivesLongDuplication
              (wordOfCons head (next :: rest)) u v
          exact Derives.trans square <| by
            simpa [u, v, wordOfCons, Word.append_assoc] using duplicateW

/-- The long-word normal form has exactly three copies of every supported
variable. -/
def tripleSupportReduce (xs : List Nat) : List Nat :=
  capThreeReduce ((xs ++ xs) ++ xs)

theorem count_tripleSupportReduce (z : Nat) (xs : List Nat) :
    (tripleSupportReduce xs).count z =
      if z ∈ xs then 3 else 0 := by
  rw [tripleSupportReduce, count_capThreeReduce,
    List.count_append, List.count_append]
  by_cases hz : z ∈ xs
  · rw [if_pos hz]
    have hpos : 0 < xs.count z := List.count_pos_iff.mpr hz
    omega
  · rw [if_neg hz]
    have hzero : xs.count z = 0 := List.count_eq_zero.mpr hz
    omega

theorem tripleSupportReduce_perm_of_support_eq {xs ys : List Nat}
    (hsupport : ∀ z, z ∈ xs ↔ z ∈ ys) :
    (tripleSupportReduce xs).Perm (tripleSupportReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_tripleSupportReduce, count_tripleSupportReduce]
  simp only [hsupport z]

theorem thresholdDerivesLongNormal (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    match tripleSupportReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeThresholdSupportBasis
          w (wordOfCons x xs) := by
  have cube := thresholdDerivesCube w hlong
  have normalized := thresholdDerivesCapThreeNormal ((w ++ w) ++ w)
  have hsame :
      tripleSupportReduce w.toList =
        capThreeReduce (((w ++ w) ++ w).toList) := by
    simp [tripleSupportReduce, Word.toList_append, List.append_assoc]
  cases hreduce : capThreeReduce (((w ++ w) ++ w).toList) with
  | nil =>
      rw [hreduce] at normalized
      exact False.elim normalized
  | cons x xs =>
      rw [hreduce] at normalized
      rw [hsame, hreduce]
      exact Derives.trans cube normalized

private theorem thresholdSupportFourMul_commutative (a b : Fin 4) :
    thresholdSupportFourMul a b =
      thresholdSupportFourMul b a := by
  decide +revert

private theorem thresholdSupportFourMul_power (a : Fin 4) :
    thresholdSupportFourMul
        (thresholdSupportFourMul a a) a =
      thresholdSupportFourMul
        (thresholdSupportFourMul
          (thresholdSupportFourMul a a) a) a := by
  decide +revert

private theorem thresholdSupportFourMul_heavy_transfer
    (a b : Fin 4) :
    thresholdSupportFourMul
        (thresholdSupportFourMul a a) b =
      thresholdSupportFourMul
        (thresholdSupportFourMul a b) b := by
  decide +revert

private theorem thresholdSupportFourMul_heavy_insertion
    (a b : Fin 4) :
    thresholdSupportFourMul
        (thresholdSupportFourMul a a) b =
      thresholdSupportFourMul
        (thresholdSupportFourMul
          (thresholdSupportFourMul a a) a) b := by
  decide +revert

private theorem thresholdSupportFourMul_long_insertion
    (a b c : Fin 4) :
    thresholdSupportFourMul
        (thresholdSupportFourMul a b) c =
      thresholdSupportFourMul
        (thresholdSupportFourMul
          (thresholdSupportFourMul a a) b) c := by
  decide +revert

theorem thresholdSupportFourBasis_models :
    Models thresholdSupportFour.semigroup
      commutativeThresholdSupportBasis := by
  intro e he
  simp only [commutativeThresholdSupportBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · intro valuation
    exact thresholdSupportFourMul_commutative
      (valuation 0) (valuation 1)
  · intro valuation
    exact thresholdSupportFourMul_power (valuation 0)
  · intro valuation
    exact thresholdSupportFourMul_heavy_transfer
      (valuation 0) (valuation 1)
  · intro valuation
    exact thresholdSupportFourMul_heavy_insertion
      (valuation 0) (valuation 1)
  · intro valuation
    exact thresholdSupportFourMul_long_insertion
      (valuation 0) (valuation 1) (valuation 2)

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else 0

private theorem supportMul_target (n : Nat) :
    thresholdSupportFourMul (supportState n) 0 =
      supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, thresholdSupportFourMul, hn]

private theorem supportMul_other (n : Nat) :
    thresholdSupportFourMul (supportState n) 3 =
      supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, thresholdSupportFourMul, hn]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          thresholdSupportFourMul current (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (0 : Fin 4) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (3 : Fin 4) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

private theorem thresholdEval_supportSeparator
    (z : Nat) (w : Word Nat) :
    thresholdSupportFour.semigroup.eval (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              thresholdSupportFourMul current (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

theorem thresholdSupportValid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy thresholdSupportFour.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [thresholdEval_supportSeparator,
    thresholdEval_supportSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hlne : e.lhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hl)
    have hrzero : e.rhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hr
    simp [supportState, hlne, hrzero] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hrne : e.rhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hr)
    have hlzero : e.lhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hl
    simp [supportState, hlzero, hrne] at evaluated

private def constantTwo : Nat → Fin 4 := fun _ => 2

private def lengthState (n : Nat) : Fin 4 :=
  ⟨3 - min n 3, by omega⟩

private theorem lengthMul_two (n : Nat) (hn : 1 ≤ n) :
    thresholdSupportFourMul (lengthState n) 2 =
      lengthState (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              apply Fin.ext
              simp [thresholdSupportFourMul, lengthState]

private theorem lengthFold (xs : List Nat) (acc : Nat)
    (hacc : 1 ≤ acc) :
    xs.foldl
        (fun current _ => thresholdSupportFourMul current 2)
        (lengthState acc) =
      lengthState (acc + xs.length) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [lengthMul_two acc hacc, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem thresholdEval_constantTwo (w : Word Nat) :
    thresholdSupportFour.semigroup.eval constantTwo w =
      lengthState w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ => thresholdSupportFourMul current 2) 2 =
          lengthState (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold tail 1 (by omega)

theorem thresholdSupportValid_capped_length
    (e : Identity Nat)
    (valid : e.SatisfiedBy thresholdSupportFour.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 := by
  have evaluated := valid constantTwo
  rw [thresholdEval_constantTwo,
    thresholdEval_constantTwo] at evaluated
  have values := Fin.mk.inj evaluated
  change
    3 - min e.lhs.toList.length 3 =
      3 - min e.rhs.toList.length 3 at values
  have hl : min e.lhs.toList.length 3 ≤ 3 :=
    Nat.min_le_right _ _
  have hr : min e.rhs.toList.length 3 ≤ 3 :=
    Nat.min_le_right _ _
  omega

private theorem perm_of_length_two_support_eq
    {xs ys : List Nat}
    (hl : xs.length = 2) (hr : ys.length = 2)
    (hsupport : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rcases xs with _ | ⟨a, xs⟩
  · simp at hl
  rcases xs with _ | ⟨b, xs⟩
  · simp at hl
  rcases xs with _ | ⟨c, xs⟩
  · rcases ys with _ | ⟨p, ys⟩
    · simp at hr
    rcases ys with _ | ⟨q, ys⟩
    · simp at hr
    rcases ys with _ | ⟨r, ys⟩
    · by_cases hab : a = b
      · subst b
        have hp : p = a := by
          have := (hsupport p).mpr (by simp)
          simpa using this
        have hq : q = a := by
          have := (hsupport q).mpr (by simp)
          simpa using this
        subst p
        subst q
        exact List.Perm.refl _
      · have hp : p = a ∨ p = b := by
          simpa using (hsupport p).mpr (by simp)
        have hq : q = a ∨ q = b := by
          simpa using (hsupport q).mpr (by simp)
        rcases hp with hp | hp
        · have hqb : q = b := by
            rcases hq with hqa | hqb
            ·
              have hb := (hsupport b).mp (by simp)
              have hba : b = a := by
                simpa [hp, hqa] using hb
              exact False.elim (hab hba.symm)
            · exact hqb
          simp [hp, hqb]
        ·
          rcases hq with hqa | hqb
          · simpa [hp, hqa] using (List.Perm.swap a b []).symm
          ·
            have ha := (hsupport a).mp (by simp)
            have hab' : a = b := by
              simpa [hp, hqb] using ha
            exact False.elim (hab hab')
    · simp at hr
  · simp at hl

/-- Unrestricted completeness over `Nat` variables. Valid identities preserve
support and total length capped at three. Words of length at least three
normalize to three copies of each supported variable. -/
theorem commutativeThresholdSupportBasis_complete :
    BasisFor thresholdSupportFour.semigroup
      commutativeThresholdSupportBasis := by
  refine ⟨thresholdSupportFourBasis_models, ?_⟩
  intro e valid
  have hsupport := thresholdSupportValid_support e valid
  have hlength := thresholdSupportValid_capped_length e valid
  have lhsPositive : 0 < e.lhs.toList.length := by
    simp [Word.toList]
  have rhsPositive : 0 < e.rhs.toList.length := by
    simp [Word.toList]
  by_cases hlone : e.lhs.toList.length = 1
  · have hrone : e.rhs.toList.length = 1 := by
      omega
    have hlTail : e.lhs.tail = [] :=
      by
        cases htail : e.lhs.tail with
        | nil => rfl
        | cons x xs =>
            have hge : 2 ≤ e.lhs.toList.length := by
              simp [Word.toList, htail]
            omega
    have hrTail : e.rhs.tail = [] :=
      by
        cases htail : e.rhs.tail with
        | nil => rfl
        | cons x xs =>
            have hge : 2 ≤ e.rhs.toList.length := by
              simp [Word.toList, htail]
            omega
    have hheadMem : e.lhs.head ∈ e.rhs.toList :=
      (hsupport e.lhs.head).mp (List.Mem.head _)
    have hheads : e.lhs.head = e.rhs.head := by
      simpa [Word.toList, hrTail] using hheadMem
    have hwords : e.lhs = e.rhs := by
      apply Word.toList_injective
      simp [Word.toList, hlTail, hrTail, hheads]
    rw [hwords]
    exact Derives.refl _
  · by_cases hltwo : e.lhs.toList.length = 2
    · have hrtwo : e.rhs.toList.length = 2 := by
        omega
      exact thresholdDerivesPermutation e.lhs e.rhs <|
        perm_of_length_two_support_eq hltwo hrtwo hsupport
    · have hllong : 3 ≤ e.lhs.toList.length := by omega
      have hrlong : 3 ≤ e.rhs.toList.length := by omega
      have reducedPerm :
          (tripleSupportReduce e.lhs.toList).Perm
            (tripleSupportReduce e.rhs.toList) :=
        tripleSupportReduce_perm_of_support_eq hsupport
      have lhsNormal := thresholdDerivesLongNormal e.lhs hllong
      have rhsNormal := thresholdDerivesLongNormal e.rhs hrlong
      cases hl : tripleSupportReduce e.lhs.toList with
      | nil =>
          have hcount :=
            count_tripleSupportReduce e.lhs.head e.lhs.toList
          have hmem : e.lhs.head ∈ e.lhs.toList := by
            simp [Word.toList]
          rw [if_pos hmem] at hcount
          rw [hl] at hcount
          simp at hcount
      | cons x xs =>
          cases hr : tripleSupportReduce e.rhs.toList with
          | nil =>
              rw [hl, hr] at reducedPerm
              exact False.elim (List.not_perm_cons_nil reducedPerm)
          | cons y ys =>
              rw [hl] at lhsNormal
              rw [hr] at rhsNormal
              rw [hl, hr] at reducedPerm
              exact Derives.trans lhsNormal <|
                Derives.trans
                  (thresholdDerivesPermutation
                    (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
                  (Derives.symm rhsNormal)

theorem commutativeThresholdSupportOppositeBasis_complete :
    BasisFor thresholdSupportFour.semigroup.opposite
      (reversedBasis commutativeThresholdSupportBasis) :=
  commutativeThresholdSupportBasis_complete.oppositeReversed

end SemigroupBasis.Examples

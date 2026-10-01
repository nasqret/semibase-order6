import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,2,1,4]]`. -/
def firstCappedMultiplicityFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then 2 else
        if b = 0 then 0 else if b = 1 then 1 else
          if b = 2 then 0 else 3

/-- The root catalogue representative `S4_74`. -/
def firstCappedMultiplicityFour : FiniteTable where
  order := 4
  mul := firstCappedMultiplicityFourMul
  assoc := by decide

def firstCappedXX : Word Nat := ⟨0, [0]⟩
def firstCappedXXX : Word Nat := ⟨0, [0, 0]⟩
def firstCappedXXY : Word Nat := ⟨0, [0, 1]⟩
def firstCappedXYX : Word Nat := ⟨0, [1, 0]⟩
def firstCappedXYZ : Word Nat := ⟨0, [1, 2]⟩
def firstCappedXZY : Word Nat := ⟨0, [2, 1]⟩

def firstCappedPowerLaw : Identity Nat :=
  ⟨firstCappedXX, firstCappedXXX⟩

def firstCappedRepeatedFirstLaw : Identity Nat :=
  ⟨firstCappedXXY, firstCappedXYX⟩

def firstCappedSuffixCommutationLaw : Identity Nat :=
  ⟨firstCappedXYZ, firstCappedXZY⟩

/-- The exact basis `xx = xxx`, `xxy = xyx`, `xyz = xzy`. -/
def firstCappedMultiplicityFourBasis : List (Identity Nat) :=
  [firstCappedPowerLaw, firstCappedRepeatedFirstLaw,
    firstCappedSuffixCommutationLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem firstCappedDerivesTripleContraction (u : Word Nat) :
    Derives firstCappedMultiplicityFourBasis
      ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives firstCappedMultiplicityFourBasis
        firstCappedXXX firstCappedXX :=
    Derives.symm <|
      Derives.fromBasis (e := firstCappedPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [firstCappedMultiplicityFourBasis, firstCappedPowerLaw,
    firstCappedXXX, firstCappedXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Move a repeated initial block across the following nonempty block. -/
theorem firstCappedDerivesRepeatedFirstMove (u v : Word Nat) :
    Derives firstCappedMultiplicityFourBasis
      ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have hbase :
      Derives firstCappedMultiplicityFourBasis
        firstCappedXXY firstCappedXYX :=
    Derives.fromBasis (e := firstCappedRepeatedFirstLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [firstCappedMultiplicityFourBasis, firstCappedRepeatedFirstLaw,
    firstCappedXXY, firstCappedXYX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Arbitrary nonempty blocks in the suffix of a word may be swapped. -/
theorem firstCappedDerivesSuffixSwap (p u v : Word Nat) :
    Derives firstCappedMultiplicityFourBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives firstCappedMultiplicityFourBasis
        firstCappedXYZ firstCappedXZY :=
    Derives.fromBasis (e := firstCappedSuffixCommutationLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [firstCappedMultiplicityFourBasis,
    firstCappedSuffixCommutationLaw, firstCappedXYZ, firstCappedXZY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- The suffix is commutative while the first letter remains fixed. -/
theorem firstCappedDerivesTailPermutation (head : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) :
    Derives firstCappedMultiplicityFourBasis
      (wordOfCons head xs) (wordOfCons head ys) := by
  induction h generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              firstCappedDerivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (firstCappedDerivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ (head := head)) (ih₂ (head := head))

private theorem firstCappedDerivesOfHeadEqTailPerm (u v : Word Nat)
    (heads : u.head = v.head) (tails : u.tail.Perm v.tail) :
    Derives firstCappedMultiplicityFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads tails
          subst vHead
          exact firstCappedDerivesTailPermutation uHead tails

private def firstCappedLimit (head x : Nat) : Nat :=
  if x = head then 1 else 2

/-- Retain at most one suffix copy of the first variable and at most two
copies of every other variable. -/
def firstCappedSuffix (head : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := firstCappedSuffix head xs
      if reduced.count x < firstCappedLimit head x then
        x :: reduced
      else
        reduced

theorem count_firstCappedSuffix (head z : Nat) (xs : List Nat) :
    (firstCappedSuffix head xs).count z =
      min (xs.count z) (firstCappedLimit head z) := by
  induction xs with
  | nil =>
      simp [firstCappedSuffix, firstCappedLimit]
  | cons x xs ih =>
      simp only [firstCappedSuffix]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hx : x = head <;>
            simp [firstCappedLimit, hx] at hcount ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          by_cases hx : x = head <;>
            simp [firstCappedLimit, hx] at hcount ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

def firstCappedNormal (w : Word Nat) : Word Nat :=
  ⟨w.head, firstCappedSuffix w.head w.tail⟩

theorem firstCappedNormal_count (w : Word Nat) (z : Nat) :
    (firstCappedNormal w).toList.count z =
      min (w.toList.count z) 2 := by
  cases w with
  | mk head tail =>
      by_cases hz : z = head
      · subst z
        simp only [firstCappedNormal, Word.toList, List.count_cons_self,
          count_firstCappedSuffix, firstCappedLimit, if_pos]
        omega
      · simp only [firstCappedNormal, Word.toList,
          List.count_cons_of_ne (Ne.symm hz), count_firstCappedSuffix,
          firstCappedLimit, if_neg hz]

private theorem two_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 2) :
    xs.Perm (x :: x :: (xs.erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have eraseCount : (xs.erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hxErase : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans (List.Perm.cons x (List.perm_cons_erase hxErase))

private theorem contractLeadingTriple (x : Nat) (xs : List Nat) :
    Derives firstCappedMultiplicityFourBasis
      (wordOfCons x (x :: x :: xs))
      (wordOfCons x (x :: xs)) := by
  cases xs with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          firstCappedDerivesTripleContraction (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (firstCappedDerivesTripleContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem contractTailTriple (head x : Nat) (xs : List Nat) :
    Derives firstCappedMultiplicityFourBasis
      (wordOfCons head (x :: x :: x :: xs))
      (wordOfCons head (x :: x :: xs)) := by
  have h := Derives.prepend (Word.singleton head)
    (contractLeadingTriple x xs)
  simpa [wordOfCons, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem deleteRepeatedHead (head : Nat) (pre rest : List Nat)
    (hrest : head ∈ rest) :
    Derives firstCappedMultiplicityFourBasis
      (wordOfCons head (pre ++ head :: rest))
      (wordOfCons head (pre ++ rest)) := by
  let remainder := rest.erase head
  have sourcePerm :
      (pre ++ head :: rest).Perm
        (head :: head :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = head
    · subst z
      simp only [List.count_cons_self]
      have eraseCount : (rest.erase head).count head =
          rest.count head - 1 := List.count_erase_self
      simp only [remainder, eraseCount]
      have positive := List.count_pos_iff.mpr hrest
      omega
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  have targetPerm :
      (pre ++ rest).Perm (head :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = head
    · subst z
      simp only [List.count_cons_self]
      have eraseCount : (rest.erase head).count head =
          rest.count head - 1 := List.count_erase_self
      simp only [remainder, eraseCount]
      have positive := List.count_pos_iff.mpr hrest
      omega
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  exact Derives.trans
    (firstCappedDerivesTailPermutation head sourcePerm) <|
    Derives.trans (contractLeadingTriple head (pre ++ remainder)) <|
      firstCappedDerivesTailPermutation head targetPerm.symm

private theorem deleteThirdSuffixCopy (head x : Nat)
    (pre rest : List Nat) (hcount : rest.count x = 2) :
    Derives firstCappedMultiplicityFourBasis
      (wordOfCons head (pre ++ x :: rest))
      (wordOfCons head (pre ++ rest)) := by
  let remainder := (rest.erase x).erase x
  have sourcePerm :
      (pre ++ x :: rest).Perm
        (x :: x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, hcount]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  have targetPerm :
      (pre ++ rest).Perm (x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, hcount]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  exact Derives.trans
    (firstCappedDerivesTailPermutation head sourcePerm) <|
    Derives.trans (contractTailTriple head x (pre ++ remainder)) <|
      firstCappedDerivesTailPermutation head targetPerm.symm

private theorem firstCappedDerivesNormalizeSuffix :
    ∀ head pre xs,
      Derives firstCappedMultiplicityFourBasis
        (wordOfCons head (pre ++ xs))
        (wordOfCons head (pre ++ firstCappedSuffix head xs))
  | head, pre, [] => by
      exact Derives.refl _
  | head, pre, x :: xs => by
      have suffixNormal :=
        firstCappedDerivesNormalizeSuffix head (pre ++ [x]) xs
      let reduced := firstCappedSuffix head xs
      have firstStep :
          Derives firstCappedMultiplicityFourBasis
            (wordOfCons head (pre ++ x :: xs))
            (wordOfCons head (pre ++ x :: reduced)) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases hcount :
          reduced.count x < firstCappedLimit head x
      · have reducedEq :
            firstCappedSuffix head (x :: xs) = x :: reduced := by
          simp [firstCappedSuffix, reduced, hcount]
        rw [reducedEq]
        exact firstStep
      · have countLe :
            reduced.count x ≤ firstCappedLimit head x := by
          rw [show reduced = firstCappedSuffix head xs by rfl,
            count_firstCappedSuffix]
          exact Nat.min_le_right _ _
        have countEq :
            reduced.count x = firstCappedLimit head x := by
          omega
        have reducedEq :
            firstCappedSuffix head (x :: xs) = reduced := by
          simp [firstCappedSuffix, reduced, hcount]
        rw [reducedEq]
        by_cases hx : x = head
        · subst x
          have headCount : reduced.count head = 1 := by
            simpa [firstCappedLimit] using countEq
          have headMem : head ∈ reduced :=
            List.count_pos_iff.mp (by omega)
          exact Derives.trans firstStep
            (deleteRepeatedHead head pre reduced headMem)
        · have suffixCount : reduced.count x = 2 := by
            simpa [firstCappedLimit, hx] using countEq
          exact Derives.trans firstStep
            (deleteThirdSuffixCopy head x pre reduced suffixCount)
termination_by
  _ _ xs => xs.length

theorem firstCappedDerivesNormal (w : Word Nat) :
    Derives firstCappedMultiplicityFourBasis w (firstCappedNormal w) := by
  cases w with
  | mk head tail =>
      simpa [firstCappedNormal, wordOfCons] using
        firstCappedDerivesNormalizeSuffix head [] tail

private def firstHeadSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 0

private theorem firstCappedFold_from_zero
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          firstCappedMultiplicityFourMul current (valuation x))
        (0 : Fin 4) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, firstCappedMultiplicityFourMul] using ih

private theorem firstCappedFold_from_two
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          firstCappedMultiplicityFourMul current (valuation x))
        (2 : Fin 4) = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, firstCappedMultiplicityFourMul] using ih

theorem firstCappedEval_headSeparator (z : Nat) (w : Word Nat) :
    firstCappedMultiplicityFour.semigroup.eval (firstHeadSeparator z) w =
      if w.head = z then (2 : Fin 4) else (0 : Fin 4) := by
  cases w with
  | mk head tail =>
      by_cases hz : head = z
      · subst head
        simp only [if_pos]
        change
          tail.foldl
              (fun current x =>
                firstCappedMultiplicityFourMul current
                  (firstHeadSeparator z x))
              (firstHeadSeparator z z) = 2
        rw [show firstHeadSeparator z z = (2 : Fin 4) by
          simp [firstHeadSeparator]]
        exact firstCappedFold_from_two _ _
      · simp only [if_neg hz]
        change
          tail.foldl
              (fun current x =>
                firstCappedMultiplicityFourMul current
                  (firstHeadSeparator z x))
              (firstHeadSeparator z head) = 0
        rw [show firstHeadSeparator z head = (0 : Fin 4) by
          simp [firstHeadSeparator, hz]]
        exact firstCappedFold_from_zero _ _

theorem firstCappedValid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy firstCappedMultiplicityFour.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (firstHeadSeparator e.lhs.head)
  rw [firstCappedEval_headSeparator,
    firstCappedEval_headSeparator] at evaluated
  simp [Ne.symm headsNe] at evaluated

private def firstMultiplicityState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n = 1 then 1 else 0

private def firstMultiplicitySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem firstMultiplicityMul_target (n : Nat) :
    firstCappedMultiplicityFourMul (firstMultiplicityState n) 1 =
      firstMultiplicityState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [firstMultiplicityState, firstCappedMultiplicityFourMul,
        hn0, hn1]

private theorem firstMultiplicityMul_other (n : Nat) :
    firstCappedMultiplicityFourMul (firstMultiplicityState n) 3 =
      firstMultiplicityState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [firstMultiplicityState, firstCappedMultiplicityFourMul,
        hn0, hn1]

private theorem firstMultiplicityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          firstCappedMultiplicityFourMul current
            (firstMultiplicitySeparator z x))
        (firstMultiplicityState acc) =
      firstMultiplicityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show firstMultiplicitySeparator z z = (1 : Fin 4) by
          simp [firstMultiplicitySeparator]]
        rw [firstMultiplicityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show firstMultiplicitySeparator z x = (3 : Fin 4) by
          simp [firstMultiplicitySeparator, hx]]
        rw [firstMultiplicityMul_other, ih]

theorem firstCappedEval_multiplicitySeparator (z : Nat) (w : Word Nat) :
    firstCappedMultiplicityFour.semigroup.eval
        (firstMultiplicitySeparator z) w =
      firstMultiplicityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              firstCappedMultiplicityFourMul current
                (firstMultiplicitySeparator z x))
            (firstMultiplicitySeparator z head) =
          firstMultiplicityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show firstMultiplicitySeparator z z =
            firstMultiplicityState 1 by
          simp [firstMultiplicitySeparator, firstMultiplicityState]]
        rw [firstMultiplicityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show firstMultiplicitySeparator z head =
            firstMultiplicityState 0 by
          simp [firstMultiplicitySeparator, firstMultiplicityState, hhead]]
        rw [firstMultiplicityFold]
        congr 1
        omega

private theorem firstMultiplicityState_eq_capped
    (n m : Nat) (h : firstMultiplicityState n =
      firstMultiplicityState m) :
    min n 2 = min m 2 := by
  have values := congrArg Fin.val h
  by_cases hn0 : n = 0
  · subst n
    by_cases hm0 : m = 0
    · subst m
      rfl
    · by_cases hm1 : m = 1
      · subst m
        simp [firstMultiplicityState] at values
        omega
      · simp [firstMultiplicityState, hm0, hm1] at values
  · by_cases hn1 : n = 1
    · subst n
      by_cases hm0 : m = 0
      · subst m
        simp [firstMultiplicityState] at values
        omega
      · by_cases hm1 : m = 1
        · subst m
          rfl
        · simp [firstMultiplicityState, hm0, hm1] at values
    · have hn2 : 2 ≤ n := by omega
      by_cases hm0 : m = 0
      · subst m
        simp [firstMultiplicityState, hn0, hn1] at values
        omega
      · by_cases hm1 : m = 1
        · subst m
          simp [firstMultiplicityState, hn0, hn1] at values
        · have hm2 : 2 ≤ m := by omega
          omega

theorem firstCappedValid_capped_count_eq (e : Identity Nat)
    (valid : e.SatisfiedBy firstCappedMultiplicityFour.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 := by
  intro z
  have evaluated := valid (firstMultiplicitySeparator z)
  rw [firstCappedEval_multiplicitySeparator,
    firstCappedEval_multiplicitySeparator] at evaluated
  exact firstMultiplicityState_eq_capped _ _ evaluated

private theorem firstCappedMul_power (a : Fin 4) :
    firstCappedMultiplicityFourMul a a =
      firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul a a) a := by
  decide +revert

private theorem firstCappedMul_repeated_first (a b : Fin 4) :
    firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul a a) b =
      firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul a b) a := by
  decide +revert

private theorem firstCappedMul_suffix_commutative (a b c : Fin 4) :
    firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul a b) c =
      firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul a c) b := by
  decide +revert

theorem firstCappedMultiplicityFourBasis_models :
    Models firstCappedMultiplicityFour.semigroup
      firstCappedMultiplicityFourBasis := by
  intro e he
  simp only [firstCappedMultiplicityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      firstCappedMultiplicityFourMul (valuation 0) (valuation 0) =
        firstCappedMultiplicityFourMul
          (firstCappedMultiplicityFourMul (valuation 0) (valuation 0))
          (valuation 0)
    exact firstCappedMul_power (valuation 0)
  · intro valuation
    change
      firstCappedMultiplicityFourMul
          (firstCappedMultiplicityFourMul (valuation 0) (valuation 0))
          (valuation 1) =
        firstCappedMultiplicityFourMul
          (firstCappedMultiplicityFourMul (valuation 0) (valuation 1))
          (valuation 0)
    exact firstCappedMul_repeated_first (valuation 0) (valuation 1)
  · intro valuation
    change
      firstCappedMultiplicityFourMul
          (firstCappedMultiplicityFourMul (valuation 0) (valuation 1))
          (valuation 2) =
        firstCappedMultiplicityFourMul
          (firstCappedMultiplicityFourMul (valuation 0) (valuation 2))
          (valuation 1)
    exact firstCappedMul_suffix_commutative
      (valuation 0) (valuation 1) (valuation 2)

/-- Unrestricted completeness over `Nat` variables. Every word derives to a
normal form with fixed first letter, commutative suffix, and every positive
multiplicity capped at two. The exact four-element table separates the first
letter and all zero/one/two multiplicity states. -/
theorem firstCappedMultiplicityFourBasis_complete :
    BasisFor firstCappedMultiplicityFour.semigroup
      firstCappedMultiplicityFourBasis := by
  refine ⟨firstCappedMultiplicityFourBasis_models, ?_⟩
  intro e valid
  have heads := firstCappedValid_head_eq e valid
  have cappedCounts := firstCappedValid_capped_count_eq e valid
  have lhsNormal := firstCappedDerivesNormal e.lhs
  have rhsNormal := firstCappedDerivesNormal e.rhs
  have tailPerm :
      (firstCappedNormal e.lhs).tail.Perm
        (firstCappedNormal e.rhs).tail := by
    rw [List.perm_iff_count]
    intro z
    have wholeCount :
        (firstCappedNormal e.lhs).toList.count z =
          (firstCappedNormal e.rhs).toList.count z := by
      rw [firstCappedNormal_count, firstCappedNormal_count,
        cappedCounts z]
    by_cases hz : z = e.lhs.head
    · subst z
      simpa [Word.toList, firstCappedNormal, heads] using wholeCount
    · have hzRight : z ≠ e.rhs.head := by
        simpa [heads] using hz
      simpa [Word.toList, firstCappedNormal, Ne.symm hz,
        Ne.symm hzRight] using wholeCount
  have middle :
      Derives firstCappedMultiplicityFourBasis
        (firstCappedNormal e.lhs) (firstCappedNormal e.rhs) := by
    apply firstCappedDerivesOfHeadEqTailPerm
    · simpa [firstCappedNormal] using heads
    · exact tailPerm
  exact Derives.trans lhsNormal <|
    Derives.trans middle (Derives.symm rhsNormal)

def firstCappedMultiplicityFourOppositeBasis : List (Identity Nat) :=
  reversedBasis firstCappedMultiplicityFourBasis

theorem firstCappedMultiplicityFourOppositeBasis_complete :
    BasisFor firstCappedMultiplicityFour.semigroup.opposite
      firstCappedMultiplicityFourOppositeBasis := by
  simpa [firstCappedMultiplicityFourOppositeBasis] using
    firstCappedMultiplicityFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples

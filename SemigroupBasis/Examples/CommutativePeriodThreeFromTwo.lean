import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def periodThreeFromTwoXX : Word Nat := ⟨0, [0]⟩
def periodThreeFromTwoXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def periodThreeFromTwoXY : Word Nat := ⟨0, [1]⟩
def periodThreeFromTwoYX : Word Nat := ⟨1, [0]⟩

def periodThreeFromTwoPowerLaw : Identity Nat :=
  ⟨periodThreeFromTwoXX, periodThreeFromTwoXXXXX⟩

def periodThreeFromTwoCommutativityLaw : Identity Nat :=
  ⟨periodThreeFromTwoXY, periodThreeFromTwoYX⟩

/-- The commutative exponent basis `xx = xxxxx`, `xy = yx`. Exponents zero
through four are distinct normal states, and exponents at least two have
period three. -/
def commutativePeriodThreeFromTwoBasis : List (Identity Nat) :=
  [periodThreeFromTwoCommutativityLaw, periodThreeFromTwoPowerLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem periodThreeFromTwoDerivesCommutativity (u v : Word Nat) :
    Derives commutativePeriodThreeFromTwoBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePeriodThreeFromTwoBasis
        periodThreeFromTwoXY periodThreeFromTwoYX :=
    Derives.fromBasis (e := periodThreeFromTwoCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePeriodThreeFromTwoBasis,
    periodThreeFromTwoCommutativityLaw, periodThreeFromTwoXY,
    periodThreeFromTwoYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem periodThreeFromTwoDerivesFiveToTwo (u : Word Nat) :
    Derives commutativePeriodThreeFromTwoBasis
      ((((u ++ u) ++ u) ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives commutativePeriodThreeFromTwoBasis
        periodThreeFromTwoXXXXX periodThreeFromTwoXX :=
    Derives.symm <|
      Derives.fromBasis (e := periodThreeFromTwoPowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePeriodThreeFromTwoBasis,
    periodThreeFromTwoPowerLaw, periodThreeFromTwoXXXXX,
    periodThreeFromTwoXX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePeriodThreeFromTwoBasis
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
              periodThreeFromTwoDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (periodThreeFromTwoDerivesCommutativity
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

theorem periodThreeFromTwoDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePeriodThreeFromTwoBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- The exact threshold-two, period-three exponent state. Zero and one stay
fixed; exponents at least two are represented by two, three, or four. -/
def periodThreeFromTwoExponent (n : Nat) : Nat :=
  if n < 2 then n else 2 + (n + 1) % 3

theorem periodThreeFromTwoExponent_succ (n : Nat) :
    periodThreeFromTwoExponent (n + 1) =
      if periodThreeFromTwoExponent n < 4 then
        periodThreeFromTwoExponent n + 1
      else
        periodThreeFromTwoExponent n - 2 := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · have hn2 : 2 ≤ n := by omega
      have hnext2 : ¬n + 1 < 2 := by omega
      by_cases h0 : (n + 1) % 3 = 0
      · have hnext : (n + 1 + 1) % 3 = 1 := by omega
        simp [periodThreeFromTwoExponent, show ¬n < 2 by omega,
          hnext2, h0, hnext]
      · by_cases h1 : (n + 1) % 3 = 1
        · have hnext : (n + 1 + 1) % 3 = 2 := by omega
          simp [periodThreeFromTwoExponent, show ¬n < 2 by omega,
            hnext2, h0, h1, hnext]
        · have h2 : (n + 1) % 3 = 2 := by omega
          have hnext : (n + 1 + 1) % 3 = 0 := by omega
          simp [periodThreeFromTwoExponent, show ¬n < 2 by omega,
            hnext2, h0, h1, h2, hnext]

theorem periodThreeFromTwoExponent_pos {n : Nat} (h : 0 < n) :
    0 < periodThreeFromTwoExponent n := by
  unfold periodThreeFromTwoExponent
  split <;> omega

/-- Normalize each multiplicity to the exact exponent states zero through
four. A fifth occurrence contracts to two occurrences, and the three-cycle
then repeats. -/
def periodThreeFromTwoReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := periodThreeFromTwoReduce xs
      if reduced.count x < 4 then
        x :: reduced
      else
        (reduced.erase x).erase x

theorem count_periodThreeFromTwoReduce (z : Nat) (xs : List Nat) :
    (periodThreeFromTwoReduce xs).count z =
      periodThreeFromTwoExponent (xs.count z) := by
  induction xs with
  | nil =>
      simp [periodThreeFromTwoReduce, periodThreeFromTwoExponent]
  | cons x xs ih =>
      simp only [periodThreeFromTwoReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodThreeFromTwoExponent_succ, if_pos hcount]
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self, List.count_erase_self,
            List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodThreeFromTwoExponent_succ, if_neg hcount] <;> omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem periodThreeFromTwoReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    periodThreeFromTwoReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_periodThreeFromTwoReduce x (x :: xs)
  rw [hempty, List.count_nil, List.count_cons_self] at hcount
  have positive :
      0 < periodThreeFromTwoExponent (xs.count x + 1) :=
    periodThreeFromTwoExponent_pos (by omega)
  omega

theorem periodThreeFromTwoReduce_perm_of_exponent_eq
    {xs ys : List Nat}
    (hcount :
      ∀ z, periodThreeFromTwoExponent (xs.count z) =
        periodThreeFromTwoExponent (ys.count z)) :
    (periodThreeFromTwoReduce xs).Perm
      (periodThreeFromTwoReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_periodThreeFromTwoReduce,
    count_periodThreeFromTwoReduce, hcount z]

private theorem four_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 4) :
    xs.Perm
      (x :: x :: x :: x :: ((((xs.erase x).erase x).erase x).erase x)) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 3 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have hcount₃ : (((xs.erase x).erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x (List.perm_cons_erase hx₃)

private theorem contractLeadingFive :
    ∀ x xs,
      Derives commutativePeriodThreeFromTwoBasis
        (wordOfCons x (x :: x :: x :: x :: xs))
        (wordOfCons x (x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          periodThreeFromTwoDerivesFiveToTwo (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (periodThreeFromTwoDerivesFiveToTwo (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem periodThreeFromTwoDerivesNormalizeList :
    ∀ x xs,
      match periodThreeFromTwoReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePeriodThreeFromTwoBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := periodThreeFromTwoDerivesNormalizeList y ys
      cases hs : periodThreeFromTwoReduce (y :: ys) with
      | nil =>
          exact False.elim
            (periodThreeFromTwoReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                periodThreeFromTwoReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if (periodThreeFromTwoReduce (y :: ys)).count x < 4 then
                  x :: periodThreeFromTwoReduce (y :: ys)
                else
                  ((periodThreeFromTwoReduce (y :: ys)).erase x).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countEq : (z :: zs).count x = 4 := by
              have hreduce :=
                count_periodThreeFromTwoReduce x (y :: ys)
              rw [hs] at hreduce
              unfold periodThreeFromTwoExponent at hreduce
              split at hreduce <;> omega
            let remainder :=
              ((((z :: zs).erase x).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm
                  (x :: x :: x :: x :: remainder) := by
              simpa [remainder] using
                four_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have erasedOncePerm :
                ((z :: zs).erase x).Perm
                  (x :: x :: x :: remainder) := by
              simpa using suffixPerm.erase x
            have erasedTwicePerm :
                (((z :: zs).erase x).erase x).Perm
                  (x :: x :: remainder) := by
              simpa using erasedOncePerm.erase x
            have arrange :
                Derives commutativePeriodThreeFromTwoBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: x :: remainder)) :=
              periodThreeFromTwoDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFive x remainder
            have eraseOnceCount :
                ((z :: zs).erase x).count x = 3 := by
              rw [List.count_erase_self, countEq]
            have eraseTwiceCount :
                (((z :: zs).erase x).erase x).count x = 2 := by
              rw [List.count_erase_self, eraseOnceCount]
            have reduced :
                periodThreeFromTwoReduce (x :: y :: ys) =
                  ((z :: zs).erase x).erase x := by
              change
                (if (periodThreeFromTwoReduce (y :: ys)).count x < 4 then
                  x :: periodThreeFromTwoReduce (y :: ys)
                else
                  ((periodThreeFromTwoReduce (y :: ys)).erase x).erase x) =
                  ((z :: zs).erase x).erase x
              rw [hs, if_neg hcount]
            cases he : ((z :: zs).erase x).erase x with
            | nil =>
                rw [he] at eraseTwiceCount
                simp at eraseTwiceCount
            | cons r rs =>
                have restore :
                    Derives commutativePeriodThreeFromTwoBasis
                      (wordOfCons x (x :: remainder))
                      (wordOfCons r rs) :=
                  periodThreeFromTwoDerivesPermutation _ _ <| by
                    rw [he] at erasedTwicePerm
                    exact erasedTwicePerm.symm
                rw [he] at reduced
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [wordOfCons, Word.append, Word.singleton,
                      Word.append_assoc] using prefixed)
                  (Derives.trans arrange <|
                    Derives.trans contract restore)
termination_by
  _ xs => xs.length

theorem periodThreeFromTwoDerivesNormal (w : Word Nat) :
    match periodThreeFromTwoReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePeriodThreeFromTwoBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact periodThreeFromTwoDerivesNormalizeList head tail

/-- Generic unrestricted completeness theorem for `xx = xxxxx`, `xy = yx`.
A model only needs to separate the five exact threshold-two, period-three
exponent states for each variable. -/
theorem commutativePeriodThreeFromTwoBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commutativePeriodThreeFromTwoBasis)
    (separates :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          periodThreeFromTwoExponent (e.lhs.toList.count z) =
            periodThreeFromTwoExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup commutativePeriodThreeFromTwoBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :
      (periodThreeFromTwoReduce e.lhs.toList).Perm
        (periodThreeFromTwoReduce e.rhs.toList) :=
    periodThreeFromTwoReduce_perm_of_exponent_eq
      (separates e valid)
  have lhsNormal := periodThreeFromTwoDerivesNormal e.lhs
  have rhsNormal := periodThreeFromTwoDerivesNormal e.rhs
  cases hl : periodThreeFromTwoReduce e.lhs.toList with
  | nil =>
      exact False.elim
        (periodThreeFromTwoReduce_cons_ne_nil
          e.lhs.head e.lhs.tail (by
            simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : periodThreeFromTwoReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (periodThreeFromTwoDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem reverse_periodThreeFromTwoXX :
    periodThreeFromTwoXX.reverse = periodThreeFromTwoXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodThreeFromTwoXXXXX :
    periodThreeFromTwoXXXXX.reverse = periodThreeFromTwoXXXXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodThreeFromTwoXY :
    periodThreeFromTwoXY.reverse = periodThreeFromTwoYX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodThreeFromTwoYX :
    periodThreeFromTwoYX.reverse = periodThreeFromTwoXY := by
  apply Word.toList_injective
  decide

private def periodThreeFromTwoCommutativityLawSymm : Identity Nat :=
  ⟨periodThreeFromTwoYX, periodThreeFromTwoXY⟩

private theorem reversed_periodThreeFromTwoPowerLaw :
    periodThreeFromTwoPowerLaw.reversed =
      periodThreeFromTwoPowerLaw := by
  simp [periodThreeFromTwoPowerLaw, Identity.reversed,
    reverse_periodThreeFromTwoXX, reverse_periodThreeFromTwoXXXXX]

private theorem reversed_periodThreeFromTwoCommutativityLaw :
    periodThreeFromTwoCommutativityLaw.reversed =
      periodThreeFromTwoCommutativityLawSymm := by
  simp [periodThreeFromTwoCommutativityLaw,
    periodThreeFromTwoCommutativityLawSymm, Identity.reversed,
    reverse_periodThreeFromTwoXY, reverse_periodThreeFromTwoYX]

theorem commutativePeriodThreeFromTwoBasis_opposite_complete
    {G : Semigroup S}
    (complete : BasisFor G commutativePeriodThreeFromTwoBasis) :
    BasisFor G.opposite commutativePeriodThreeFromTwoBasis := by
  have reversedComplete := complete.oppositeReversed
  apply reversedComplete.replace
  · intro e he
    simp only [commutativePeriodThreeFromTwoBasis, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodThreeFromTwoCommutativityLaw]
      intro valuation
      exact
        (complete.1 periodThreeFromTwoCommutativityLaw
          (List.Mem.head _) valuation).symm
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodThreeFromTwoPowerLaw]
      exact complete.1 periodThreeFromTwoPowerLaw <|
        List.Mem.tail _ (List.Mem.head _)
  · intro e he
    simp only [reversedBasis, commutativePeriodThreeFromTwoBasis,
      List.map_cons, List.map_nil, reversed_periodThreeFromTwoPowerLaw,
      reversed_periodThreeFromTwoCommutativityLaw, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Derives.symm <|
        Derives.fromBasis (List.Mem.head _)
    · exact Derives.fromBasis <|
        List.Mem.tail _ (List.Mem.head _)

end SemigroupBasis.Examples

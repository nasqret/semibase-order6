import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def periodTwoFromTwoXX : Word Nat := ⟨0, [0]⟩
def periodTwoFromTwoXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def periodTwoFromTwoXY : Word Nat := ⟨0, [1]⟩
def periodTwoFromTwoYX : Word Nat := ⟨1, [0]⟩

def periodTwoFromTwoPowerLaw : Identity Nat :=
  ⟨periodTwoFromTwoXX, periodTwoFromTwoXXXX⟩

def periodTwoFromTwoCommutativityLaw : Identity Nat :=
  ⟨periodTwoFromTwoXY, periodTwoFromTwoYX⟩

/-- The commutative exponent basis `xx = xxxx`, `xy = yx`. Exponents one,
two, and three are distinct normal states, and exponents at least two have
period two. -/
def commutativePeriodTwoFromTwoBasis : List (Identity Nat) :=
  [periodTwoFromTwoPowerLaw, periodTwoFromTwoCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem periodTwoFromTwoDerivesCommutativity (u v : Word Nat) :
    Derives commutativePeriodTwoFromTwoBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePeriodTwoFromTwoBasis
        periodTwoFromTwoXY periodTwoFromTwoYX :=
    Derives.fromBasis (e := periodTwoFromTwoCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePeriodTwoFromTwoBasis,
    periodTwoFromTwoCommutativityLaw, periodTwoFromTwoXY,
    periodTwoFromTwoYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem periodTwoFromTwoDerivesFourToTwo (u : Word Nat) :
    Derives commutativePeriodTwoFromTwoBasis
      (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives commutativePeriodTwoFromTwoBasis
        periodTwoFromTwoXXXX periodTwoFromTwoXX :=
    Derives.symm <|
      Derives.fromBasis (e := periodTwoFromTwoPowerLaw) <| by
        exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePeriodTwoFromTwoBasis, periodTwoFromTwoPowerLaw,
    periodTwoFromTwoXXXX, periodTwoFromTwoXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePeriodTwoFromTwoBasis
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
              periodTwoFromTwoDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (periodTwoFromTwoDerivesCommutativity
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

theorem periodTwoFromTwoDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePeriodTwoFromTwoBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- The canonical exponent state: zero and one remain unchanged, while
exponents at least two are represented by two or three according to parity. -/
def periodTwoFromTwoExponent (n : Nat) : Nat :=
  if n < 2 then n else 2 + n % 2

theorem periodTwoFromTwoExponent_succ (n : Nat) :
    periodTwoFromTwoExponent (n + 1) =
      if periodTwoFromTwoExponent n < 3 then
        periodTwoFromTwoExponent n + 1
      else
        periodTwoFromTwoExponent n - 1 := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · have hn2 : 2 ≤ n := by omega
      have hnext2 : ¬n + 1 < 2 := by omega
      by_cases hp : n % 2 = 0
      · have hnext : (n + 1) % 2 = 1 := by omega
        simp [periodTwoFromTwoExponent, show ¬n < 2 by omega,
          hnext2, hp, hnext]
      · have hmod : n % 2 = 1 := by omega
        have hnext : (n + 1) % 2 = 0 := by omega
        simp [periodTwoFromTwoExponent, show ¬n < 2 by omega,
          hnext2, hmod, hnext]

theorem periodTwoFromTwoExponent_pos {n : Nat} (h : 0 < n) :
    0 < periodTwoFromTwoExponent n := by
  unfold periodTwoFromTwoExponent
  split <;> omega

/-- Normalize each multiplicity to the exponent states zero, one, two, or
three. The fourth occurrence cancels two occurrences, and the cycle repeats. -/
def periodTwoFromTwoReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := periodTwoFromTwoReduce xs
      if reduced.count x < 3 then x :: reduced else reduced.erase x

theorem count_periodTwoFromTwoReduce (z : Nat) (xs : List Nat) :
    (periodTwoFromTwoReduce xs).count z =
      periodTwoFromTwoExponent (xs.count z) := by
  induction xs with
  | nil =>
      simp [periodTwoFromTwoReduce, periodTwoFromTwoExponent]
  | cons x xs ih =>
      simp only [periodTwoFromTwoReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodTwoFromTwoExponent_succ, if_pos hcount]
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self, List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodTwoFromTwoExponent_succ, if_neg hcount]
        · rw [List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem periodTwoFromTwoReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    periodTwoFromTwoReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_periodTwoFromTwoReduce x (x :: xs)
  rw [hempty, List.count_nil, List.count_cons_self] at hcount
  have positive :
      0 < periodTwoFromTwoExponent (xs.count x + 1) :=
    periodTwoFromTwoExponent_pos (by omega)
  omega

theorem periodTwoFromTwoReduce_perm_of_exponent_eq
    {xs ys : List Nat}
    (hcount :
      ∀ z, periodTwoFromTwoExponent (xs.count z) =
        periodTwoFromTwoExponent (ys.count z)) :
    (periodTwoFromTwoReduce xs).Perm
      (periodTwoFromTwoReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_periodTwoFromTwoReduce,
    count_periodTwoFromTwoReduce, hcount z]

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
      Derives commutativePeriodTwoFromTwoBasis
        (wordOfCons x (x :: x :: x :: xs))
        (wordOfCons x (x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          periodTwoFromTwoDerivesFourToTwo (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (periodTwoFromTwoDerivesFourToTwo (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem periodTwoFromTwoDerivesNormalizeList :
    ∀ x xs,
      match periodTwoFromTwoReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePeriodTwoFromTwoBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := periodTwoFromTwoDerivesNormalizeList y ys
      cases hs : periodTwoFromTwoReduce (y :: ys) with
      | nil =>
          exact False.elim
            (periodTwoFromTwoReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 3
          · have reduced :
                periodTwoFromTwoReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if (periodTwoFromTwoReduce (y :: ys)).count x < 3 then
                  x :: periodTwoFromTwoReduce (y :: ys)
                else (periodTwoFromTwoReduce (y :: ys)).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countEq : (z :: zs).count x = 3 := by
              have hreduce :=
                count_periodTwoFromTwoReduce x (y :: ys)
              rw [hs] at hreduce
              unfold periodTwoFromTwoExponent at hreduce
              split at hreduce <;> omega
            let remainder :=
              (((z :: zs).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm (x :: x :: x :: remainder) := by
              simpa [remainder] using
                three_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have erasedPerm :
                ((z :: zs).erase x).Perm
                  (x :: x :: remainder) := by
              simpa using suffixPerm.erase x
            have arrange :
                Derives commutativePeriodTwoFromTwoBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: remainder)) :=
              periodTwoFromTwoDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFour x remainder
            have eraseCount :
                ((z :: zs).erase x).count x = 2 := by
              rw [List.count_erase_self, countEq]
            have reduced :
                periodTwoFromTwoReduce (x :: y :: ys) =
                  (z :: zs).erase x := by
              change
                (if (periodTwoFromTwoReduce (y :: ys)).count x < 3 then
                  x :: periodTwoFromTwoReduce (y :: ys)
                else (periodTwoFromTwoReduce (y :: ys)).erase x) =
                  (z :: zs).erase x
              rw [hs, if_neg hcount]
            cases he : (z :: zs).erase x with
            | nil =>
                rw [he] at eraseCount
                simp at eraseCount
            | cons r rs =>
                have restore :
                    Derives commutativePeriodTwoFromTwoBasis
                      (wordOfCons x (x :: remainder))
                      (wordOfCons r rs) :=
                  periodTwoFromTwoDerivesPermutation _ _ <| by
                    rw [he] at erasedPerm
                    exact erasedPerm.symm
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

theorem periodTwoFromTwoDerivesNormal (w : Word Nat) :
    match periodTwoFromTwoReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePeriodTwoFromTwoBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact periodTwoFromTwoDerivesNormalizeList head tail

/-- Generic unrestricted completeness theorem for the basis
`xx = xxxx`, `xy = yx`. A model only needs to separate the four normalized
exponent states for each variable. -/
theorem commutativePeriodTwoFromTwoBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commutativePeriodTwoFromTwoBasis)
    (separates :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          periodTwoFromTwoExponent (e.lhs.toList.count z) =
            periodTwoFromTwoExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup commutativePeriodTwoFromTwoBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :
      (periodTwoFromTwoReduce e.lhs.toList).Perm
        (periodTwoFromTwoReduce e.rhs.toList) :=
    periodTwoFromTwoReduce_perm_of_exponent_eq
      (separates e valid)
  have lhsNormal := periodTwoFromTwoDerivesNormal e.lhs
  have rhsNormal := periodTwoFromTwoDerivesNormal e.rhs
  cases hl : periodTwoFromTwoReduce e.lhs.toList with
  | nil =>
      exact False.elim
        (periodTwoFromTwoReduce_cons_ne_nil
          e.lhs.head e.lhs.tail (by
            simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : periodTwoFromTwoReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (periodTwoFromTwoDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem reverse_periodTwoFromTwoXX :
    periodTwoFromTwoXX.reverse = periodTwoFromTwoXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromTwoXXXX :
    periodTwoFromTwoXXXX.reverse = periodTwoFromTwoXXXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromTwoXY :
    periodTwoFromTwoXY.reverse = periodTwoFromTwoYX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromTwoYX :
    periodTwoFromTwoYX.reverse = periodTwoFromTwoXY := by
  apply Word.toList_injective
  decide

private def periodTwoFromTwoCommutativityLawSymm : Identity Nat :=
  ⟨periodTwoFromTwoYX, periodTwoFromTwoXY⟩

private theorem reversed_periodTwoFromTwoPowerLaw :
    periodTwoFromTwoPowerLaw.reversed =
      periodTwoFromTwoPowerLaw := by
  simp [periodTwoFromTwoPowerLaw, Identity.reversed,
    reverse_periodTwoFromTwoXX, reverse_periodTwoFromTwoXXXX]

private theorem reversed_periodTwoFromTwoCommutativityLaw :
    periodTwoFromTwoCommutativityLaw.reversed =
      periodTwoFromTwoCommutativityLawSymm := by
  simp [periodTwoFromTwoCommutativityLaw,
    periodTwoFromTwoCommutativityLawSymm, Identity.reversed,
    reverse_periodTwoFromTwoXY, reverse_periodTwoFromTwoYX]

theorem commutativePeriodTwoFromTwoBasis_opposite_complete
    {G : Semigroup S}
    (complete : BasisFor G commutativePeriodTwoFromTwoBasis) :
    BasisFor G.opposite commutativePeriodTwoFromTwoBasis := by
  have reversedComplete := complete.oppositeReversed
  apply reversedComplete.replace
  · intro e he
    simp only [commutativePeriodTwoFromTwoBasis, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodTwoFromTwoPowerLaw]
      exact complete.1 periodTwoFromTwoPowerLaw (List.Mem.head _)
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodTwoFromTwoCommutativityLaw]
      intro valuation
      exact
        (complete.1 periodTwoFromTwoCommutativityLaw
          (List.Mem.tail _ (List.Mem.head _)) valuation).symm
  · intro e he
    simp only [reversedBasis, commutativePeriodTwoFromTwoBasis,
      List.map_cons, List.map_nil, reversed_periodTwoFromTwoPowerLaw,
      reversed_periodTwoFromTwoCommutativityLaw, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Derives.fromBasis (List.Mem.head _)
    · exact Derives.symm <|
        Derives.fromBasis (List.Mem.tail _ (List.Mem.head _))

end SemigroupBasis.Examples

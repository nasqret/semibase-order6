import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def periodTwoFromThreeXXX : Word Nat := ⟨0, [0, 0]⟩
def periodTwoFromThreeXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def periodTwoFromThreeXY : Word Nat := ⟨0, [1]⟩
def periodTwoFromThreeYX : Word Nat := ⟨1, [0]⟩

def periodTwoFromThreePowerLaw : Identity Nat :=
  ⟨periodTwoFromThreeXXX, periodTwoFromThreeXXXXX⟩

def periodTwoFromThreeCommutativityLaw : Identity Nat :=
  ⟨periodTwoFromThreeXY, periodTwoFromThreeYX⟩

/-- The commutative exponent basis `xxx = xxxxx`, `xy = yx`. Exponents one
through four are distinct normal states, and exponents at least three have
period two. -/
def commutativePeriodTwoFromThreeBasis : List (Identity Nat) :=
  [periodTwoFromThreeCommutativityLaw, periodTwoFromThreePowerLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem periodTwoFromThreeDerivesCommutativity (u v : Word Nat) :
    Derives commutativePeriodTwoFromThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePeriodTwoFromThreeBasis
        periodTwoFromThreeXY periodTwoFromThreeYX :=
    Derives.fromBasis (e := periodTwoFromThreeCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePeriodTwoFromThreeBasis,
    periodTwoFromThreeCommutativityLaw, periodTwoFromThreeXY,
    periodTwoFromThreeYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem periodTwoFromThreeDerivesFiveToThree (u : Word Nat) :
    Derives commutativePeriodTwoFromThreeBasis
      ((((u ++ u) ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives commutativePeriodTwoFromThreeBasis
        periodTwoFromThreeXXXXX periodTwoFromThreeXXX :=
    Derives.symm <|
      Derives.fromBasis (e := periodTwoFromThreePowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePeriodTwoFromThreeBasis, periodTwoFromThreePowerLaw,
    periodTwoFromThreeXXXXX, periodTwoFromThreeXXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePeriodTwoFromThreeBasis
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
              periodTwoFromThreeDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (periodTwoFromThreeDerivesCommutativity
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

theorem periodTwoFromThreeDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePeriodTwoFromThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- The canonical exponent state: zero, one, and two remain unchanged, while
exponents at least three are represented by three or four according to
parity. -/
def periodTwoFromThreeExponent (n : Nat) : Nat :=
  if n < 3 then n else 3 + (n + 1) % 2

theorem periodTwoFromThreeExponent_succ (n : Nat) :
    periodTwoFromThreeExponent (n + 1) =
      if periodTwoFromThreeExponent n < 4 then
        periodTwoFromThreeExponent n + 1
      else
        periodTwoFromThreeExponent n - 1 := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        rfl
      · have hn3 : 3 ≤ n := by omega
        have hnext3 : ¬n + 1 < 3 := by omega
        by_cases hp : (n + 1) % 2 = 0
        · have hnext : (n + 1 + 1) % 2 = 1 := by omega
          simp [periodTwoFromThreeExponent, show ¬n < 3 by omega,
            hnext3, hp, hnext]
        · have hmod : (n + 1) % 2 = 1 := by omega
          have hnext : (n + 1 + 1) % 2 = 0 := by omega
          simp [periodTwoFromThreeExponent, show ¬n < 3 by omega,
            hnext3, hmod, hnext]

theorem periodTwoFromThreeExponent_pos {n : Nat} (h : 0 < n) :
    0 < periodTwoFromThreeExponent n := by
  unfold periodTwoFromThreeExponent
  split <;> omega

/-- Normalize each multiplicity to the exponent states zero through four.
The fifth occurrence cancels two occurrences, and the cycle repeats. -/
def periodTwoFromThreeReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := periodTwoFromThreeReduce xs
      if reduced.count x < 4 then x :: reduced else reduced.erase x

theorem count_periodTwoFromThreeReduce (z : Nat) (xs : List Nat) :
    (periodTwoFromThreeReduce xs).count z =
      periodTwoFromThreeExponent (xs.count z) := by
  induction xs with
  | nil =>
      simp [periodTwoFromThreeReduce, periodTwoFromThreeExponent]
  | cons x xs ih =>
      simp only [periodTwoFromThreeReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodTwoFromThreeExponent_succ, if_pos hcount]
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self, List.count_cons_self, ih]
          rw [ih] at hcount
          rw [periodTwoFromThreeExponent_succ, if_neg hcount]
        · rw [List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem periodTwoFromThreeReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    periodTwoFromThreeReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_periodTwoFromThreeReduce x (x :: xs)
  rw [hempty, List.count_nil, List.count_cons_self] at hcount
  have positive :
      0 < periodTwoFromThreeExponent (xs.count x + 1) :=
    periodTwoFromThreeExponent_pos (by omega)
  omega

theorem periodTwoFromThreeReduce_perm_of_exponent_eq
    {xs ys : List Nat}
    (hcount :
      ∀ z, periodTwoFromThreeExponent (xs.count z) =
        periodTwoFromThreeExponent (ys.count z)) :
    (periodTwoFromThreeReduce xs).Perm
      (periodTwoFromThreeReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_periodTwoFromThreeReduce,
    count_periodTwoFromThreeReduce, hcount z]

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
      Derives commutativePeriodTwoFromThreeBasis
        (wordOfCons x (x :: x :: x :: x :: xs))
        (wordOfCons x (x :: x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          periodTwoFromThreeDerivesFiveToThree (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (periodTwoFromThreeDerivesFiveToThree (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem periodTwoFromThreeDerivesNormalizeList :
    ∀ x xs,
      match periodTwoFromThreeReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePeriodTwoFromThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := periodTwoFromThreeDerivesNormalizeList y ys
      cases hs : periodTwoFromThreeReduce (y :: ys) with
      | nil =>
          exact False.elim
            (periodTwoFromThreeReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                periodTwoFromThreeReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if (periodTwoFromThreeReduce (y :: ys)).count x < 4 then
                  x :: periodTwoFromThreeReduce (y :: ys)
                else (periodTwoFromThreeReduce (y :: ys)).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countEq : (z :: zs).count x = 4 := by
              have hreduce :=
                count_periodTwoFromThreeReduce x (y :: ys)
              rw [hs] at hreduce
              unfold periodTwoFromThreeExponent at hreduce
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
            have erasedPerm :
                ((z :: zs).erase x).Perm
                  (x :: x :: x :: remainder) := by
              simpa using suffixPerm.erase x
            have arrange :
                Derives commutativePeriodTwoFromThreeBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: x :: remainder)) :=
              periodTwoFromThreeDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFive x remainder
            have eraseCount :
                ((z :: zs).erase x).count x = 3 := by
              rw [List.count_erase_self, countEq]
            have reduced :
                periodTwoFromThreeReduce (x :: y :: ys) =
                  (z :: zs).erase x := by
              change
                (if (periodTwoFromThreeReduce (y :: ys)).count x < 4 then
                  x :: periodTwoFromThreeReduce (y :: ys)
                else (periodTwoFromThreeReduce (y :: ys)).erase x) =
                  (z :: zs).erase x
              rw [hs, if_neg hcount]
            cases he : (z :: zs).erase x with
            | nil =>
                rw [he] at eraseCount
                simp at eraseCount
            | cons r rs =>
                have restore :
                    Derives commutativePeriodTwoFromThreeBasis
                      (wordOfCons x (x :: x :: remainder))
                      (wordOfCons r rs) :=
                  periodTwoFromThreeDerivesPermutation _ _ <| by
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

theorem periodTwoFromThreeDerivesNormal (w : Word Nat) :
    match periodTwoFromThreeReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePeriodTwoFromThreeBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact periodTwoFromThreeDerivesNormalizeList head tail

/-- Generic unrestricted completeness theorem for the basis
`xxx = xxxxx`, `xy = yx`. A model only needs to separate the five normalized
exponent states for each variable. -/
theorem commutativePeriodTwoFromThreeBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commutativePeriodTwoFromThreeBasis)
    (separates :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          periodTwoFromThreeExponent (e.lhs.toList.count z) =
            periodTwoFromThreeExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup commutativePeriodTwoFromThreeBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :
      (periodTwoFromThreeReduce e.lhs.toList).Perm
        (periodTwoFromThreeReduce e.rhs.toList) :=
    periodTwoFromThreeReduce_perm_of_exponent_eq
      (separates e valid)
  have lhsNormal := periodTwoFromThreeDerivesNormal e.lhs
  have rhsNormal := periodTwoFromThreeDerivesNormal e.rhs
  cases hl : periodTwoFromThreeReduce e.lhs.toList with
  | nil =>
      exact False.elim
        (periodTwoFromThreeReduce_cons_ne_nil
          e.lhs.head e.lhs.tail (by
            simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : periodTwoFromThreeReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (periodTwoFromThreeDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem reverse_periodTwoFromThreeXXX :
    periodTwoFromThreeXXX.reverse = periodTwoFromThreeXXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromThreeXXXXX :
    periodTwoFromThreeXXXXX.reverse = periodTwoFromThreeXXXXX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromThreeXY :
    periodTwoFromThreeXY.reverse = periodTwoFromThreeYX := by
  apply Word.toList_injective
  decide

private theorem reverse_periodTwoFromThreeYX :
    periodTwoFromThreeYX.reverse = periodTwoFromThreeXY := by
  apply Word.toList_injective
  decide

private def periodTwoFromThreeCommutativityLawSymm : Identity Nat :=
  ⟨periodTwoFromThreeYX, periodTwoFromThreeXY⟩

private theorem reversed_periodTwoFromThreePowerLaw :
    periodTwoFromThreePowerLaw.reversed =
      periodTwoFromThreePowerLaw := by
  simp [periodTwoFromThreePowerLaw, Identity.reversed,
    reverse_periodTwoFromThreeXXX, reverse_periodTwoFromThreeXXXXX]

private theorem reversed_periodTwoFromThreeCommutativityLaw :
    periodTwoFromThreeCommutativityLaw.reversed =
      periodTwoFromThreeCommutativityLawSymm := by
  simp [periodTwoFromThreeCommutativityLaw,
    periodTwoFromThreeCommutativityLawSymm, Identity.reversed,
    reverse_periodTwoFromThreeXY, reverse_periodTwoFromThreeYX]

theorem commutativePeriodTwoFromThreeBasis_opposite_complete
    {G : Semigroup S}
    (complete : BasisFor G commutativePeriodTwoFromThreeBasis) :
    BasisFor G.opposite commutativePeriodTwoFromThreeBasis := by
  have reversedComplete := complete.oppositeReversed
  apply reversedComplete.replace
  · intro e he
    simp only [commutativePeriodTwoFromThreeBasis, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodTwoFromThreeCommutativityLaw]
      intro valuation
      exact
        (complete.1 periodTwoFromThreeCommutativityLaw
          (List.Mem.head _) valuation).symm
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_periodTwoFromThreePowerLaw]
      exact complete.1 periodTwoFromThreePowerLaw <|
        List.Mem.tail _ (List.Mem.head _)
  · intro e he
    simp only [reversedBasis, commutativePeriodTwoFromThreeBasis,
      List.map_cons, List.map_nil, reversed_periodTwoFromThreePowerLaw,
      reversed_periodTwoFromThreeCommutativityLaw, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Derives.symm <|
        Derives.fromBasis (List.Mem.head _)
    · exact Derives.fromBasis <|
        List.Mem.tail _ (List.Mem.head _)

end SemigroupBasis.Examples

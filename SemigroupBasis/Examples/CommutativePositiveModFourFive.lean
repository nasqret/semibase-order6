import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def positiveModFourX : Word Nat := Word.singleton 0
def positiveModFourXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def positiveModFourXY : Word Nat := ⟨0, [1]⟩
def positiveModFourYX : Word Nat := ⟨1, [0]⟩

def positiveModFourPowerLaw : Identity Nat :=
  ⟨positiveModFourX, positiveModFourXXXXX⟩

def positiveModFourCommutativityLaw : Identity Nat :=
  ⟨positiveModFourXY, positiveModFourYX⟩

/-- The exact basis `x = xxxxx`, `xy = yx`. -/
def commutativePositiveModFourBasis : List (Identity Nat) :=
  [positiveModFourPowerLaw, positiveModFourCommutativityLaw]

/-- The complete word invariant for `x = xxxxx`, `xy = yx`: equal support
and equal positive multiplicities modulo four. -/
def SamePositiveModFour (u v : Word Nat) : Prop :=
  (∀ z, z ∈ u.toList ↔ z ∈ v.toList) ∧
    ∀ z, u.toList.count z % 4 = v.toList.count z % 4

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem positiveModFourDerivesFiveContraction (u : Word Nat) :
    Derives commutativePositiveModFourBasis
      ((((u ++ u) ++ u) ++ u) ++ u) u := by
  have hbase :
      Derives commutativePositiveModFourBasis
        positiveModFourXXXXX positiveModFourX :=
    Derives.symm <|
      Derives.fromBasis (e := positiveModFourPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePositiveModFourBasis, positiveModFourPowerLaw,
    positiveModFourXXXXX, positiveModFourX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem positiveModFourDerivesCommutativity (u v : Word Nat) :
    Derives commutativePositiveModFourBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePositiveModFourBasis
        positiveModFourXY positiveModFourYX :=
    Derives.fromBasis (e := positiveModFourCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePositiveModFourBasis,
    positiveModFourCommutativityLaw, positiveModFourXY,
    positiveModFourYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePositiveModFourBasis
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
              positiveModFourDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (positiveModFourDerivesCommutativity
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

theorem positiveModFourDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePositiveModFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain one, two, three, or four copies of every occurring variable
according to its positive multiplicity modulo four. -/
def positiveModFourReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := positiveModFourReduce xs
      if reduced.count x < 4 then
        x :: reduced
      else
        ((reduced.erase x).erase x).erase x

theorem positiveModFourReduce_count_le_four
    (z : Nat) (xs : List Nat) :
    (positiveModFourReduce xs).count z ≤ 4 := by
  induction xs with
  | nil =>
      simp [positiveModFourReduce]
  | cons x xs ih =>
      simp only [positiveModFourReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx]
          exact ih

theorem mem_positiveModFourReduce_iff (z : Nat) (xs : List Nat) :
    z ∈ positiveModFourReduce xs ↔ z ∈ xs := by
  induction xs with
  | nil =>
      simp [positiveModFourReduce]
  | cons x xs ih =>
      simp only [positiveModFourReduce]
      split <;> rename_i hcount
      · simp [ih]
      · have countLe :
            (positiveModFourReduce xs).count x ≤ 4 :=
          positiveModFourReduce_count_le_four x xs
        have countEq :
            (positiveModFourReduce xs).count x = 4 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countOnce :
              ((positiveModFourReduce xs).erase x).count x = 3 := by
            rw [List.count_erase_self, countEq]
          have countTwice :
              (((positiveModFourReduce xs).erase x).erase x).count x =
                2 := by
            rw [List.count_erase_self, countOnce]
          have remains :
              x ∈
                (((positiveModFourReduce xs).erase x).erase x).erase x := by
            rw [← List.count_pos_iff, List.count_erase_self,
              countTwice]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx]
          simp [ih, hzx]

theorem positiveModFourReduce_count_mod_four
    (z : Nat) (xs : List Nat) :
    (positiveModFourReduce xs).count z % 4 =
      xs.count z % 4 := by
  induction xs with
  | nil =>
      simp [positiveModFourReduce]
  | cons x xs ih =>
      simp only [positiveModFourReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          have countLe :
              (positiveModFourReduce xs).count x ≤ 4 :=
            positiveModFourReduce_count_le_four x xs
          have countEq :
              (positiveModFourReduce xs).count x = 4 := by
            omega
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih

theorem positiveModFourReduce_perm
    {xs ys : List Nat}
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (modFourEq :
      ∀ z, xs.count z % 4 = ys.count z % 4) :
    (positiveModFourReduce xs).Perm
      (positiveModFourReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  have leftLe := positiveModFourReduce_count_le_four z xs
  have rightLe := positiveModFourReduce_count_le_four z ys
  have reducedSupport :
      z ∈ positiveModFourReduce xs ↔
        z ∈ positiveModFourReduce ys := by
    rw [mem_positiveModFourReduce_iff,
      mem_positiveModFourReduce_iff, supportEq z]
  have reducedModFour :
      (positiveModFourReduce xs).count z % 4 =
        (positiveModFourReduce ys).count z % 4 := by
    rw [positiveModFourReduce_count_mod_four,
      positiveModFourReduce_count_mod_four, modFourEq z]
  by_cases hz : z ∈ positiveModFourReduce xs
  · have leftPos := List.count_pos_iff.mpr hz
    have rightPos :=
      List.count_pos_iff.mpr (reducedSupport.mp hz)
    omega
  · have leftZero := List.count_eq_zero.mpr hz
    have rightZero :=
      List.count_eq_zero.mpr <| by
        intro h
        exact hz (reducedSupport.mpr h)
    omega

private theorem four_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 4) :
    xs.Perm
      (x :: x :: x :: x ::
        ((((xs.erase x).erase x).erase x).erase x)) := by
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
      Derives commutativePositiveModFourBasis
        (wordOfCons x (x :: x :: x :: x :: xs))
        (wordOfCons x xs)
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          positiveModFourDerivesFiveContraction
            (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (positiveModFourDerivesFiveContraction
            (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem positiveModFourDerivesNormalizeList :
    ∀ x xs,
      match positiveModFourReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePositiveModFourBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        positiveModFourDerivesNormalizeList y ys
      cases hs : positiveModFourReduce (y :: ys) with
      | nil =>
          have present :
              y ∈ positiveModFourReduce (y :: ys) :=
            (mem_positiveModFourReduce_iff y (y :: ys)).mpr
              (by simp)
          simp [hs] at present
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                positiveModFourReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if
                    (positiveModFourReduce (y :: ys)).count x < 4
                  then x :: positiveModFourReduce (y :: ys)
                  else
                    (((positiveModFourReduce (y :: ys)).erase x).erase x).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 4 := by
              rw [← hs]
              exact
                positiveModFourReduce_count_le_four x (y :: ys)
            have countEq : (z :: zs).count x = 4 := by
              omega
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
            have arrange :
                Derives commutativePositiveModFourBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x
                    (x :: x :: x :: x :: remainder)) :=
              positiveModFourDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFive x remainder
            have eraseOnceCount :
                ((z :: zs).erase x).count x = 3 := by
              rw [List.count_erase_self, countEq]
            have eraseTwiceCount :
                (((z :: zs).erase x).erase x).count x = 2 := by
              rw [List.count_erase_self, eraseOnceCount]
            have eraseThriceCount :
                ((((z :: zs).erase x).erase x).erase x).count x =
                  1 := by
              rw [List.count_erase_self, eraseTwiceCount]
            have eraseThriceHasX :
                x ∈ (((z :: zs).erase x).erase x).erase x :=
              List.count_pos_iff.mp (by omega)
            have reducedPerm :
                (x :: remainder).Perm
                  ((((z :: zs).erase x).erase x).erase x) := by
              simpa [remainder] using
                (List.perm_cons_erase eraseThriceHasX).symm
            have reduced :
                positiveModFourReduce (x :: y :: ys) =
                  (((z :: zs).erase x).erase x).erase x := by
              change
                (if
                    (positiveModFourReduce (y :: ys)).count x < 4
                  then x :: positiveModFourReduce (y :: ys)
                  else
                    (((positiveModFourReduce (y :: ys)).erase x).erase x).erase x) =
                  (((z :: zs).erase x).erase x).erase x
              rw [hs, if_neg hcount]
            cases he : (((z :: zs).erase x).erase x).erase x with
            | nil =>
                rw [he] at eraseThriceCount
                simp at eraseThriceCount
            | cons r rs =>
                have restore :
                    Derives commutativePositiveModFourBasis
                      (wordOfCons x remainder)
                      (wordOfCons r rs) :=
                  positiveModFourDerivesPermutation _ _ <| by
                    simpa [he] using reducedPerm
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

theorem positiveModFourDerivesNormal (w : Word Nat) :
    match positiveModFourReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePositiveModFourBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact positiveModFourDerivesNormalizeList head tail

/-- Words with the same support and positive exponent residues modulo four
are derivably equal from `x = xxxxx`, `xy = yx`. -/
theorem commutativePositiveModFourDerives_of_invariant
    {u v : Word Nat} (same : SamePositiveModFour u v) :
    Derives commutativePositiveModFourBasis u v := by
  have reducedPerm :
      (positiveModFourReduce u.toList).Perm
        (positiveModFourReduce v.toList) :=
    positiveModFourReduce_perm same.1 same.2
  have lhsNormal := positiveModFourDerivesNormal u
  have rhsNormal := positiveModFourDerivesNormal v
  cases hl : positiveModFourReduce u.toList with
  | nil =>
      have present :
          u.head ∈ positiveModFourReduce u.toList :=
        (mem_positiveModFourReduce_iff _ _).mpr <| by
          simp [Word.toList]
      simp [hl] at present
  | cons x xs =>
      cases hr : positiveModFourReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (positiveModFourDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- Generic unrestricted completeness theorem for `x = xxxxx`, `xy = yx`.
A model only needs to separate support and positive multiplicity modulo four
for every variable. -/
theorem commutativePositiveModFourBasis_complete_of_separates
    (T : FiniteTable)
    (models :
      Models T.semigroup commutativePositiveModFourBasis)
    (support :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (modFour :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 4 =
          e.rhs.toList.count z % 4) :
    BasisFor T.semigroup commutativePositiveModFourBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact commutativePositiveModFourDerives_of_invariant
    ⟨support e valid, modFour e valid⟩

end SemigroupBasis.Examples

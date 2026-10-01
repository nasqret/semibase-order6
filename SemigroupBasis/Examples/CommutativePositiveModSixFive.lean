import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def positiveModSixX : Word Nat := Word.singleton 0
def positiveModSixXXXXXXX : Word Nat :=
  ⟨0, [0, 0, 0, 0, 0, 0]⟩
def positiveModSixXY : Word Nat := ⟨0, [1]⟩
def positiveModSixYX : Word Nat := ⟨1, [0]⟩

def positiveModSixPowerLaw : Identity Nat :=
  ⟨positiveModSixX, positiveModSixXXXXXXX⟩

def positiveModSixCommutativityLaw : Identity Nat :=
  ⟨positiveModSixXY, positiveModSixYX⟩

/-- The exact basis `x = xxxxxxx`, `xy = yx`. -/
def commutativePositiveModSixBasis : List (Identity Nat) :=
  [positiveModSixPowerLaw, positiveModSixCommutativityLaw]

/-- The complete word invariant for `x = xxxxxxx`, `xy = yx`: equal support
and equal positive multiplicities modulo six. -/
def SamePositiveModSix (u v : Word Nat) : Prop :=
  (∀ z, z ∈ u.toList ↔ z ∈ v.toList) ∧
    ∀ z, u.toList.count z % 6 = v.toList.count z % 6

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem positiveModSixDerivesSevenContraction (u : Word Nat) :
    Derives commutativePositiveModSixBasis
      ((((((u ++ u) ++ u) ++ u) ++ u) ++ u) ++ u) u := by
  have hbase :
      Derives commutativePositiveModSixBasis
        positiveModSixXXXXXXX positiveModSixX :=
    Derives.symm <|
      Derives.fromBasis (e := positiveModSixPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePositiveModSixBasis, positiveModSixPowerLaw,
    positiveModSixXXXXXXX, positiveModSixX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem positiveModSixDerivesCommutativity (u v : Word Nat) :
    Derives commutativePositiveModSixBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePositiveModSixBasis
        positiveModSixXY positiveModSixYX :=
    Derives.fromBasis (e := positiveModSixCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePositiveModSixBasis,
    positiveModSixCommutativityLaw, positiveModSixXY,
    positiveModSixYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePositiveModSixBasis
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
              positiveModSixDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (positiveModSixDerivesCommutativity
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

theorem positiveModSixDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePositiveModSixBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain one through six copies of every occurring variable
according to its positive multiplicity modulo six. -/
def positiveModSixReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := positiveModSixReduce xs
      if reduced.count x < 6 then
        x :: reduced
      else
        (((((reduced.erase x).erase x).erase x).erase x).erase x)

theorem positiveModSixReduce_count_le_six
    (z : Nat) (xs : List Nat) :
    (positiveModSixReduce xs).count z ≤ 6 := by
  induction xs with
  | nil =>
      simp [positiveModSixReduce]
  | cons x xs ih =>
      simp only [positiveModSixReduce]
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
            List.count_erase_self, List.count_erase_self,
            List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx]
          exact ih

theorem mem_positiveModSixReduce_iff (z : Nat) (xs : List Nat) :
    z ∈ positiveModSixReduce xs ↔ z ∈ xs := by
  induction xs with
  | nil =>
      simp [positiveModSixReduce]
  | cons x xs ih =>
      simp only [positiveModSixReduce]
      split <;> rename_i hcount
      · simp [ih]
      · have countLe :
            (positiveModSixReduce xs).count x ≤ 6 :=
          positiveModSixReduce_count_le_six x xs
        have countEq :
            (positiveModSixReduce xs).count x = 6 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countOnce :
              ((positiveModSixReduce xs).erase x).count x = 5 := by
            rw [List.count_erase_self, countEq]
          have countTwice :
              (((positiveModSixReduce xs).erase x).erase x).count x =
                4 := by
            rw [List.count_erase_self, countOnce]
          have countThrice :
              ((((positiveModSixReduce xs).erase x).erase x).erase x).count x =
                3 := by
            rw [List.count_erase_self, countTwice]
          have countFour :
              (((((positiveModSixReduce xs).erase x).erase x).erase x).erase x).count x =
                2 := by
            rw [List.count_erase_self, countThrice]
          have remains :
              x ∈
                (((((positiveModSixReduce xs).erase x).erase x).erase x).erase x).erase x := by
            rw [← List.count_pos_iff, List.count_erase_self,
              countFour]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx]
          simp [ih, hzx]

theorem positiveModSixReduce_count_mod_six
    (z : Nat) (xs : List Nat) :
    (positiveModSixReduce xs).count z % 6 =
      xs.count z % 6 := by
  induction xs with
  | nil =>
      simp [positiveModSixReduce]
  | cons x xs ih =>
      simp only [positiveModSixReduce]
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
              (positiveModSixReduce xs).count x ≤ 6 :=
            positiveModSixReduce_count_le_six x xs
          have countEq :
              (positiveModSixReduce xs).count x = 6 := by
            omega
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih

theorem positiveModSixReduce_perm
    {xs ys : List Nat}
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (modSixEq :
      ∀ z, xs.count z % 6 = ys.count z % 6) :
    (positiveModSixReduce xs).Perm
      (positiveModSixReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  have leftLe := positiveModSixReduce_count_le_six z xs
  have rightLe := positiveModSixReduce_count_le_six z ys
  have reducedSupport :
      z ∈ positiveModSixReduce xs ↔
        z ∈ positiveModSixReduce ys := by
    rw [mem_positiveModSixReduce_iff,
      mem_positiveModSixReduce_iff, supportEq z]
  have reducedModSix :
      (positiveModSixReduce xs).count z % 6 =
        (positiveModSixReduce ys).count z % 6 := by
    rw [positiveModSixReduce_count_mod_six,
      positiveModSixReduce_count_mod_six, modSixEq z]
  by_cases hz : z ∈ positiveModSixReduce xs
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

private theorem six_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 6) :
    xs.Perm
      (x :: x :: x :: x :: x :: x ::
        ((((((xs.erase x).erase x).erase x).erase x).erase x).erase x)) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 5 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 4 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have hcount₃ : (((xs.erase x).erase x).erase x).count x = 3 := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have fourth := List.perm_cons_erase hx₃
  have hcount₄ :
      ((((xs.erase x).erase x).erase x).erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₄ : x ∈ (((xs.erase x).erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have fifth := List.perm_cons_erase hx₄
  have hcount₅ :
      (((((xs.erase x).erase x).erase x).erase x).erase x).count x =
        1 := by
    rw [List.count_erase_self]
    omega
  have hx₅ : x ∈ ((((xs.erase x).erase x).erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x <|
        fourth.trans <| List.Perm.cons x <|
          fifth.trans <| List.Perm.cons x (List.perm_cons_erase hx₅)

private theorem contractLeadingSeven :
    ∀ x xs,
      Derives commutativePositiveModSixBasis
        (wordOfCons x (x :: x :: x :: x :: x :: x :: xs))
        (wordOfCons x xs)
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          positiveModSixDerivesSevenContraction
            (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (positiveModSixDerivesSevenContraction
            (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem positiveModSixDerivesNormalizeList :
    ∀ x xs,
      match positiveModSixReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePositiveModSixBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        positiveModSixDerivesNormalizeList y ys
      cases hs : positiveModSixReduce (y :: ys) with
      | nil =>
          have present :
              y ∈ positiveModSixReduce (y :: ys) :=
            (mem_positiveModSixReduce_iff y (y :: ys)).mpr
              (by simp)
          simp [hs] at present
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 6
          · have reduced :
                positiveModSixReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if
                    (positiveModSixReduce (y :: ys)).count x < 6
                  then x :: positiveModSixReduce (y :: ys)
                  else
                    (((((positiveModSixReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 6 := by
              rw [← hs]
              exact
                positiveModSixReduce_count_le_six x (y :: ys)
            have countEq : (z :: zs).count x = 6 := by
              omega
            let remainder :=
              ((((((z :: zs).erase x).erase x).erase x).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm
                  (x :: x :: x :: x :: x :: x :: remainder) := by
              simpa [remainder] using
                six_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrange :
                Derives commutativePositiveModSixBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x
                    (x :: x :: x :: x :: x :: x :: remainder)) :=
              positiveModSixDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingSeven x remainder
            have eraseOnceCount :
                ((z :: zs).erase x).count x = 5 := by
              rw [List.count_erase_self, countEq]
            have eraseTwiceCount :
                (((z :: zs).erase x).erase x).count x = 4 := by
              rw [List.count_erase_self, eraseOnceCount]
            have eraseThriceCount :
                ((((z :: zs).erase x).erase x).erase x).count x =
                  3 := by
              rw [List.count_erase_self, eraseTwiceCount]
            have eraseFourCount :
                (((((z :: zs).erase x).erase x).erase x).erase x).count x =
                  2 := by
              rw [List.count_erase_self, eraseThriceCount]
            have eraseFiveCount :
                ((((((z :: zs).erase x).erase x).erase x).erase x).erase x).count x =
                  1 := by
              rw [List.count_erase_self, eraseFourCount]
            have eraseFiveHasX :
                x ∈
                  (((((z :: zs).erase x).erase x).erase x).erase x).erase x :=
              List.count_pos_iff.mp (by omega)
            have reducedPerm :
                (x :: remainder).Perm
                  ((((((z :: zs).erase x).erase x).erase x).erase x).erase x) := by
              simpa [remainder] using
                (List.perm_cons_erase eraseFiveHasX).symm
            have reduced :
                positiveModSixReduce (x :: y :: ys) =
                  (((((z :: zs).erase x).erase x).erase x).erase x).erase x := by
              change
                (if
                    (positiveModSixReduce (y :: ys)).count x < 6
                  then x :: positiveModSixReduce (y :: ys)
                  else
                    (((((positiveModSixReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
                  (((((z :: zs).erase x).erase x).erase x).erase x).erase x
              rw [hs, if_neg hcount]
            cases he :
                (((((z :: zs).erase x).erase x).erase x).erase x).erase x with
            | nil =>
                rw [he] at eraseFiveCount
                simp at eraseFiveCount
            | cons r rs =>
                have restore :
                    Derives commutativePositiveModSixBasis
                      (wordOfCons x remainder)
                      (wordOfCons r rs) :=
                  positiveModSixDerivesPermutation _ _ <| by
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

theorem positiveModSixDerivesNormal (w : Word Nat) :
    match positiveModSixReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePositiveModSixBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact positiveModSixDerivesNormalizeList head tail

/-- Words with the same support and positive exponent residues modulo six
are derivably equal from `x = xxxxxxx`, `xy = yx`. -/
theorem commutativePositiveModSixDerives_of_invariant
    {u v : Word Nat} (same : SamePositiveModSix u v) :
    Derives commutativePositiveModSixBasis u v := by
  have reducedPerm :
      (positiveModSixReduce u.toList).Perm
        (positiveModSixReduce v.toList) :=
    positiveModSixReduce_perm same.1 same.2
  have lhsNormal := positiveModSixDerivesNormal u
  have rhsNormal := positiveModSixDerivesNormal v
  cases hl : positiveModSixReduce u.toList with
  | nil =>
      have present :
          u.head ∈ positiveModSixReduce u.toList :=
        (mem_positiveModSixReduce_iff _ _).mpr <| by
          simp [Word.toList]
      simp [hl] at present
  | cons x xs =>
      cases hr : positiveModSixReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (positiveModSixDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- Generic unrestricted completeness theorem for `x = xxxxxxx`, `xy = yx`.
A model only needs to separate support and positive multiplicity modulo six
for every variable. -/
theorem commutativePositiveModSixBasis_complete_of_separates
    (T : FiniteTable)
    (models :
      Models T.semigroup commutativePositiveModSixBasis)
    (support :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (modSix :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 6 =
          e.rhs.toList.count z % 6) :
    BasisFor T.semigroup commutativePositiveModSixBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact commutativePositiveModSixDerives_of_invariant
    ⟨support e valid, modSix e valid⟩

end SemigroupBasis.Examples

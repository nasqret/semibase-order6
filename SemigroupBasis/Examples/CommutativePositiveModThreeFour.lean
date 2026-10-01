import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def positiveModThreeX : Word Nat := Word.singleton 0
def positiveModThreeXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def positiveModThreeXY : Word Nat := ⟨0, [1]⟩
def positiveModThreeYX : Word Nat := ⟨1, [0]⟩

def positiveModThreePowerLaw : Identity Nat :=
  ⟨positiveModThreeX, positiveModThreeXXXX⟩

def positiveModThreeCommutativityLaw : Identity Nat :=
  ⟨positiveModThreeXY, positiveModThreeYX⟩

/-- The exact basis `x = xxxx`, `xy = yx`. -/
def commutativePositiveModThreeBasis : List (Identity Nat) :=
  [positiveModThreePowerLaw, positiveModThreeCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem positiveModThreeDerivesFourContraction (u : Word Nat) :
    Derives commutativePositiveModThreeBasis
      (((u ++ u) ++ u) ++ u) u := by
  have hbase :
      Derives commutativePositiveModThreeBasis
        positiveModThreeXXXX positiveModThreeX :=
    Derives.symm <|
      Derives.fromBasis (e := positiveModThreePowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativePositiveModThreeBasis, positiveModThreePowerLaw,
    positiveModThreeXXXX, positiveModThreeX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem positiveModThreeDerivesCommutativity (u v : Word Nat) :
    Derives commutativePositiveModThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativePositiveModThreeBasis
        positiveModThreeXY positiveModThreeYX :=
    Derives.fromBasis (e := positiveModThreeCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativePositiveModThreeBasis,
    positiveModThreeCommutativityLaw, positiveModThreeXY,
    positiveModThreeYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativePositiveModThreeBasis
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
              positiveModThreeDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (positiveModThreeDerivesCommutativity
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

theorem positiveModThreeDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativePositiveModThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain one, two, or three copies of every occurring variable according
to its positive multiplicity modulo three. -/
def positiveModThreeReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := positiveModThreeReduce xs
      if reduced.count x < 3 then
        x :: reduced
      else
        (reduced.erase x).erase x

theorem positiveModThreeReduce_count_le_three
    (z : Nat) (xs : List Nat) :
    (positiveModThreeReduce xs).count z ≤ 3 := by
  induction xs with
  | nil =>
      simp [positiveModThreeReduce]
  | cons x xs ih =>
      simp only [positiveModThreeReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self, List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx]
          exact ih

theorem mem_positiveModThreeReduce_iff (z : Nat) (xs : List Nat) :
    z ∈ positiveModThreeReduce xs ↔ z ∈ xs := by
  induction xs with
  | nil =>
      simp [positiveModThreeReduce]
  | cons x xs ih =>
      simp only [positiveModThreeReduce]
      split <;> rename_i hcount
      · simp [ih]
      · have countLe :
            (positiveModThreeReduce xs).count x ≤ 3 :=
          positiveModThreeReduce_count_le_three x xs
        have countEq :
            (positiveModThreeReduce xs).count x = 3 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countOnce :
              ((positiveModThreeReduce xs).erase x).count x = 2 := by
            rw [List.count_erase_self, countEq]
          have remains :
              x ∈
                ((positiveModThreeReduce xs).erase x).erase x := by
            rw [← List.count_pos_iff, List.count_erase_self,
              countOnce]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne hzx,
            List.mem_erase_of_ne hzx]
          simp [ih, hzx]

theorem positiveModThreeReduce_count_mod_three
    (z : Nat) (xs : List Nat) :
    (positiveModThreeReduce xs).count z % 3 =
      xs.count z % 3 := by
  induction xs with
  | nil =>
      simp [positiveModThreeReduce]
  | cons x xs ih =>
      simp only [positiveModThreeReduce]
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
              (positiveModThreeReduce xs).count x ≤ 3 :=
            positiveModThreeReduce_count_le_three x xs
          have countEq :
              (positiveModThreeReduce xs).count x = 3 := by
            omega
          rw [List.count_erase_self, List.count_erase_self,
            List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih

theorem positiveModThreeReduce_perm
    {xs ys : List Nat}
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (modThreeEq :
      ∀ z, xs.count z % 3 = ys.count z % 3) :
    (positiveModThreeReduce xs).Perm
      (positiveModThreeReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  have leftLe := positiveModThreeReduce_count_le_three z xs
  have rightLe := positiveModThreeReduce_count_le_three z ys
  have reducedSupport :
      z ∈ positiveModThreeReduce xs ↔
        z ∈ positiveModThreeReduce ys := by
    rw [mem_positiveModThreeReduce_iff,
      mem_positiveModThreeReduce_iff, supportEq z]
  have reducedModThree :
      (positiveModThreeReduce xs).count z % 3 =
        (positiveModThreeReduce ys).count z % 3 := by
    rw [positiveModThreeReduce_count_mod_three,
      positiveModThreeReduce_count_mod_three, modThreeEq z]
  by_cases hz : z ∈ positiveModThreeReduce xs
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

private theorem three_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 3) :
    xs.Perm
      (x :: x :: x :: ((xs.erase x).erase x).erase x) := by
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
      Derives commutativePositiveModThreeBasis
        (wordOfCons x (x :: x :: x :: xs))
        (wordOfCons x xs)
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          positiveModThreeDerivesFourContraction
            (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (positiveModThreeDerivesFourContraction
            (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem positiveModThreeDerivesNormalizeList :
    ∀ x xs,
      match positiveModThreeReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativePositiveModThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        positiveModThreeDerivesNormalizeList y ys
      cases hs : positiveModThreeReduce (y :: ys) with
      | nil =>
          have present :
              y ∈ positiveModThreeReduce (y :: ys) :=
            (mem_positiveModThreeReduce_iff y (y :: ys)).mpr
              (by simp)
          simp [hs] at present
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 3
          · have reduced :
                positiveModThreeReduce (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if
                    (positiveModThreeReduce (y :: ys)).count x < 3
                  then x :: positiveModThreeReduce (y :: ys)
                  else
                    ((positiveModThreeReduce (y :: ys)).erase x).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 3 := by
              rw [← hs]
              exact
                positiveModThreeReduce_count_le_three x (y :: ys)
            have countEq : (z :: zs).count x = 3 := by
              omega
            let remainder :=
              (((z :: zs).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm
                  (x :: x :: x :: remainder) := by
              simpa [remainder] using
                three_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrange :
                Derives commutativePositiveModThreeBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: remainder)) :=
              positiveModThreeDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFour x remainder
            have eraseOnceCount :
                ((z :: zs).erase x).count x = 2 := by
              rw [List.count_erase_self, countEq]
            have eraseTwiceCount :
                (((z :: zs).erase x).erase x).count x = 1 := by
              rw [List.count_erase_self, eraseOnceCount]
            have eraseTwiceHasX :
                x ∈ ((z :: zs).erase x).erase x :=
              List.count_pos_iff.mp (by omega)
            have reducedPerm :
                (x :: remainder).Perm
                  (((z :: zs).erase x).erase x) := by
              simpa [remainder] using
                (List.perm_cons_erase eraseTwiceHasX).symm
            have reduced :
                positiveModThreeReduce (x :: y :: ys) =
                  ((z :: zs).erase x).erase x := by
              change
                (if
                    (positiveModThreeReduce (y :: ys)).count x < 3
                  then x :: positiveModThreeReduce (y :: ys)
                  else
                    ((positiveModThreeReduce (y :: ys)).erase x).erase x) =
                  ((z :: zs).erase x).erase x
              rw [hs, if_neg hcount]
            cases he : ((z :: zs).erase x).erase x with
            | nil =>
                rw [he] at eraseTwiceCount
                simp at eraseTwiceCount
            | cons r rs =>
                have restore :
                    Derives commutativePositiveModThreeBasis
                      (wordOfCons x remainder)
                      (wordOfCons r rs) :=
                  positiveModThreeDerivesPermutation _ _ <| by
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

theorem positiveModThreeDerivesNormal (w : Word Nat) :
    match positiveModThreeReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativePositiveModThreeBasis
          w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact positiveModThreeDerivesNormalizeList head tail

/-- Generic unrestricted completeness theorem for `x = xxxx`, `xy = yx`.
A model only needs to separate support and multiplicity modulo three for
every variable. -/
theorem commutativePositiveModThreeBasis_complete_of_separates
    (T : FiniteTable)
    (models :
      Models T.semigroup commutativePositiveModThreeBasis)
    (support :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (modThree :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 3 =
          e.rhs.toList.count z % 3) :
    BasisFor T.semigroup commutativePositiveModThreeBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :
      (positiveModThreeReduce e.lhs.toList).Perm
        (positiveModThreeReduce e.rhs.toList) :=
    positiveModThreeReduce_perm
      (support e valid) (modThree e valid)
  have lhsNormal := positiveModThreeDerivesNormal e.lhs
  have rhsNormal := positiveModThreeDerivesNormal e.rhs
  cases hl : positiveModThreeReduce e.lhs.toList with
  | nil =>
      have present :
          e.lhs.head ∈
            positiveModThreeReduce e.lhs.toList :=
        (mem_positiveModThreeReduce_iff _ _).mpr <| by
          simp [Word.toList]
      simp [hl] at present
  | cons x xs =>
      cases hr : positiveModThreeReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (positiveModThreeDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- The zero-based form of the stored `S4_124` table
`[[1,1,1,1],[1,2,3,4],[1,3,4,2],[1,4,2,3]]`. -/
def commutativePositiveModThreeFourMul
    (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    0
  else if b = 0 then
    0
  else
    ⟨(a.val + b.val + 1) % 3 + 1, by omega⟩

/-- The zero-adjoined cyclic group of order three, stored as `S4_124`. -/
def commutativePositiveModThreeFour : FiniteTable where
  order := 4
  mul := commutativePositiveModThreeFourMul
  assoc := by decide

private def positiveModThreeValue (n : Nat) : Fin 4 :=
  ⟨n % 3 + 1, by omega⟩

private def positiveModThreeSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 1

private theorem positiveModThreeMul_target (n : Nat) :
    commutativePositiveModThreeFourMul
        (positiveModThreeValue n) 2 =
      positiveModThreeValue (n + 1) := by
  apply Fin.ext
  simp [commutativePositiveModThreeFourMul,
    positiveModThreeValue]
  omega

private theorem positiveModThreeMul_other (n : Nat) :
    commutativePositiveModThreeFourMul
        (positiveModThreeValue n) 1 =
      positiveModThreeValue n := by
  apply Fin.ext
  simp [commutativePositiveModThreeFourMul,
    positiveModThreeValue]
  omega

private theorem positiveModThreeFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativePositiveModThreeFourMul current
            (positiveModThreeSeparator z x))
        (positiveModThreeValue acc) =
      positiveModThreeValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show positiveModThreeSeparator z z = (2 : Fin 4) by
          simp [positiveModThreeSeparator]]
        rw [positiveModThreeMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show positiveModThreeSeparator z x = (1 : Fin 4) by
          simp [positiveModThreeSeparator, hx]]
        rw [positiveModThreeMul_other, ih]

theorem positiveModThreeEval_separator (z : Nat) (w : Word Nat) :
    commutativePositiveModThreeFour.semigroup.eval
        (positiveModThreeSeparator z) w =
      positiveModThreeValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativePositiveModThreeFourMul current
                (positiveModThreeSeparator z x))
            (positiveModThreeSeparator z head) =
          positiveModThreeValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show positiveModThreeSeparator z z =
            positiveModThreeValue 1 by
          apply Fin.ext
          simp [positiveModThreeSeparator, positiveModThreeValue]]
        rw [positiveModThreeFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show positiveModThreeSeparator z head =
            positiveModThreeValue 0 by
          apply Fin.ext
          simp [positiveModThreeSeparator, positiveModThreeValue,
            hhead]]
        rw [positiveModThreeFold]
        congr 1
        omega

private def positiveModThreeSupportState (n : Nat) : Fin 4 :=
  if n = 0 then 1 else 0

private def positiveModThreeSupportSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 1

private theorem positiveModThreeSupportMul_target (n : Nat) :
    commutativePositiveModThreeFourMul
        (positiveModThreeSupportState n) 0 =
      positiveModThreeSupportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [positiveModThreeSupportState,
      commutativePositiveModThreeFourMul, hn]

private theorem positiveModThreeSupportMul_other (n : Nat) :
    commutativePositiveModThreeFourMul
        (positiveModThreeSupportState n) 1 =
      positiveModThreeSupportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [positiveModThreeSupportState,
      commutativePositiveModThreeFourMul, hn]

private theorem positiveModThreeSupportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativePositiveModThreeFourMul current
            (positiveModThreeSupportSeparator z x))
        (positiveModThreeSupportState acc) =
      positiveModThreeSupportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show positiveModThreeSupportSeparator z z =
            (0 : Fin 4) by
          simp [positiveModThreeSupportSeparator]]
        rw [positiveModThreeSupportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show positiveModThreeSupportSeparator z x =
            (1 : Fin 4) by
          simp [positiveModThreeSupportSeparator, hx]]
        rw [positiveModThreeSupportMul_other, ih]

theorem positiveModThreeEval_supportSeparator
    (z : Nat) (w : Word Nat) :
    commutativePositiveModThreeFour.semigroup.eval
        (positiveModThreeSupportSeparator z) w =
      positiveModThreeSupportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativePositiveModThreeFourMul current
                (positiveModThreeSupportSeparator z x))
            (positiveModThreeSupportSeparator z head) =
          positiveModThreeSupportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show positiveModThreeSupportSeparator z z =
            positiveModThreeSupportState 1 by
          apply Fin.ext
          simp [positiveModThreeSupportSeparator,
            positiveModThreeSupportState]]
        rw [positiveModThreeSupportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show positiveModThreeSupportSeparator z head =
            positiveModThreeSupportState 0 by
          apply Fin.ext
          simp [positiveModThreeSupportSeparator,
            positiveModThreeSupportState, hhead]]
        rw [positiveModThreeSupportFold]
        congr 1
        omega

theorem positiveModThreeValid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy commutativePositiveModThreeFour.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (positiveModThreeSupportSeparator z)
  rw [positiveModThreeEval_supportSeparator,
    positiveModThreeEval_supportSeparator] at evaluated
  have zeroEq :
      e.lhs.toList.count z = 0 ↔
        e.rhs.toList.count z = 0 := by
    constructor
    · intro hl
      by_cases hr : e.rhs.toList.count z = 0
      · exact hr
      · have specialized := evaluated
        simp only [positiveModThreeSupportState, if_pos hl,
          if_neg hr] at specialized
        change (1 : Fin 4) = 0 at specialized
        have impossible := Fin.mk.inj specialized
        omega
    · intro hr
      by_cases hl : e.lhs.toList.count z = 0
      · exact hl
      · have specialized := evaluated
        simp only [positiveModThreeSupportState, if_neg hl,
          if_pos hr] at specialized
        change (0 : Fin 4) = 1 at specialized
        have impossible := Fin.mk.inj specialized
        omega
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor <;> intro hpos
  · have hnzero : e.lhs.toList.count z ≠ 0 := by
      omega
    have hrzero : e.rhs.toList.count z ≠ 0 :=
      fun hr => hnzero (zeroEq.mpr hr)
    omega
  · have hnzero : e.rhs.toList.count z ≠ 0 := by
      omega
    have hlzero : e.lhs.toList.count z ≠ 0 :=
      fun hl => hnzero (zeroEq.mp hl)
    omega

theorem positiveModThreeValid_count_mod_three
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy commutativePositiveModThreeFour.semigroup) :
    ∀ z, e.lhs.toList.count z % 3 =
      e.rhs.toList.count z % 3 := by
  intro z
  have evaluated := valid (positiveModThreeSeparator z)
  rw [positiveModThreeEval_separator,
    positiveModThreeEval_separator] at evaluated
  have values := Fin.mk.inj evaluated
  change
    e.lhs.toList.count z % 3 + 1 =
      e.rhs.toList.count z % 3 + 1 at values
  omega

private theorem positiveModThreeFourMul_power (a : Fin 4) :
    a =
      commutativePositiveModThreeFourMul
        (commutativePositiveModThreeFourMul
          (commutativePositiveModThreeFourMul a a) a) a := by
  decide +revert

private theorem positiveModThreeFourMul_commutative
    (a b : Fin 4) :
    commutativePositiveModThreeFourMul a b =
      commutativePositiveModThreeFourMul b a := by
  decide +revert

theorem commutativePositiveModThreeFourBasis_models :
    Models commutativePositiveModThreeFour.semigroup
      commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      commutativePositiveModThreeFourMul
        (commutativePositiveModThreeFourMul
          (commutativePositiveModThreeFourMul
            (valuation 0) (valuation 0))
          (valuation 0))
        (valuation 0)
    exact positiveModThreeFourMul_power (valuation 0)
  · intro valuation
    change
      commutativePositiveModThreeFourMul
          (valuation 0) (valuation 1) =
        commutativePositiveModThreeFourMul
          (valuation 1) (valuation 0)
    exact positiveModThreeFourMul_commutative
      (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables for the exact
`S4_124` representative. -/
theorem commutativePositiveModThreeFourBasis_complete :
    BasisFor commutativePositiveModThreeFour.semigroup
      commutativePositiveModThreeBasis :=
  commutativePositiveModThreeBasis_complete_of_separates
    commutativePositiveModThreeFour
    commutativePositiveModThreeFourBasis_models
    positiveModThreeValid_support
    positiveModThreeValid_count_mod_three

end SemigroupBasis.Examples

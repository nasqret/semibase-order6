import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def parityX : Word Nat := Word.singleton 0
def parityXXX : Word Nat := ⟨0, [0, 0]⟩
def parityXY : Word Nat := ⟨0, [1]⟩
def parityYX : Word Nat := ⟨1, [0]⟩

def parityPowerLaw : Identity Nat :=
  ⟨parityX, parityXXX⟩

def parityCommutativityLaw : Identity Nat :=
  ⟨parityXY, parityYX⟩

/-- The common basis `x = xxx`, `xy = yx` for `S3_10` and `S3_11`. -/
def commutativeParityBasis : List (Identity Nat) :=
  [parityPowerLaw, parityCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem parityDerivesCommutativity (u v : Word Nat) :
    Derives commutativeParityBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeParityBasis parityXY parityYX :=
    Derives.fromBasis (e := parityCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeParityBasis, parityCommutativityLaw,
    parityXY, parityYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem parityDerivesTripleContraction (u : Word Nat) :
    Derives commutativeParityBasis ((u ++ u) ++ u) u := by
  have hbase :
      Derives commutativeParityBasis parityXXX parityX :=
    Derives.symm <|
      Derives.fromBasis (e := parityPowerLaw) <| by
        exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativeParityBasis, parityPowerLaw, parityXXX,
    parityX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeParityBasis
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
              parityDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (parityDerivesCommutativity
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

theorem parityDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeParityBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Reduce every positive multiplicity to one copy when it is odd and two
copies when it is even. Absence remains absence. -/
def positiveParityReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := positiveParityReduce xs
      if reduced.count x < 2 then x :: reduced else reduced.erase x

theorem positiveParityReduce_count_le_two (z : Nat) (xs : List Nat) :
    (positiveParityReduce xs).count z ≤ 2 := by
  induction xs with
  | nil =>
      simp [positiveParityReduce]
  | cons x xs ih =>
      simp only [positiveParityReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne hzx]
          exact ih

theorem mem_positiveParityReduce_iff (z : Nat) (xs : List Nat) :
    z ∈ positiveParityReduce xs ↔ z ∈ xs := by
  induction xs with
  | nil =>
      simp [positiveParityReduce]
  | cons x xs ih =>
      simp only [positiveParityReduce]
      split <;> rename_i hcount
      · simp [ih]
      · have countLe :
            (positiveParityReduce xs).count x ≤ 2 :=
          positiveParityReduce_count_le_two x xs
        have countEq :
            (positiveParityReduce xs).count x = 2 := by
          omega
        by_cases hzx : z = x
        · subst z
          have remains :
              x ∈ (positiveParityReduce xs).erase x := by
            rw [← List.count_pos_iff, List.count_erase_self, countEq]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne hzx]
          simp [ih, hzx]

theorem positiveParityReduce_count_mod_two (z : Nat) (xs : List Nat) :
    (positiveParityReduce xs).count z % 2 = xs.count z % 2 := by
  induction xs with
  | nil =>
      simp [positiveParityReduce]
  | cons x xs ih =>
      simp only [positiveParityReduce]
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
              (positiveParityReduce xs).count x ≤ 2 :=
            positiveParityReduce_count_le_two x xs
          have countEq :
              (positiveParityReduce xs).count x = 2 := by
            omega
          rw [List.count_erase_self, List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih

theorem positiveParityReduce_perm
    {xs ys : List Nat}
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (parityEq : ∀ z, xs.count z % 2 = ys.count z % 2) :
    (positiveParityReduce xs).Perm (positiveParityReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  have leftLe := positiveParityReduce_count_le_two z xs
  have rightLe := positiveParityReduce_count_le_two z ys
  have reducedSupport :
      z ∈ positiveParityReduce xs ↔
        z ∈ positiveParityReduce ys := by
    rw [mem_positiveParityReduce_iff, mem_positiveParityReduce_iff,
      supportEq z]
  have reducedParity :
      (positiveParityReduce xs).count z % 2 =
        (positiveParityReduce ys).count z % 2 := by
    rw [positiveParityReduce_count_mod_two,
      positiveParityReduce_count_mod_two, parityEq z]
  by_cases hz : z ∈ positiveParityReduce xs
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

private theorem two_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 2) :
    xs.Perm (x :: x :: (xs.erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have herase : (xs.erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hxErase : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans (List.Perm.cons x (List.perm_cons_erase hxErase))

private theorem contractLeadingTriple :
    ∀ x xs,
      Derives commutativeParityBasis
        (wordOfCons x (x :: x :: xs))
        (wordOfCons x xs)
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          parityDerivesTripleContraction (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (parityDerivesTripleContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem positiveParityDerivesNormalizeList :
    ∀ x xs,
      match positiveParityReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativeParityBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := positiveParityDerivesNormalizeList y ys
      cases hs : positiveParityReduce (y :: ys) with
      | nil =>
          have present :
              y ∈ positiveParityReduce (y :: ys) :=
            (mem_positiveParityReduce_iff y (y :: ys)).mpr (by simp)
          exact False.elim (by simpa [hs] using present)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 2
          · have reduced :
                positiveParityReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (positiveParityReduce (y :: ys)).count x < 2 then
                  x :: positiveParityReduce (y :: ys)
                else (positiveParityReduce (y :: ys)).erase x) =
                  x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 2 := by
              rw [← hs]
              exact positiveParityReduce_count_le_two x (y :: ys)
            have countEq : (z :: zs).count x = 2 := by omega
            let remainder := ((z :: zs).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm (x :: x :: remainder) := by
              simpa [remainder] using
                two_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm (x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have eraseCount :
                ((z :: zs).erase x).count x = 1 := by
              rw [List.count_erase_self, countEq]
            have eraseHasX : x ∈ (z :: zs).erase x :=
              List.count_pos_iff.mp (by omega)
            have reducedPerm :
                (x :: remainder).Perm ((z :: zs).erase x) := by
              simpa [remainder] using
                (List.perm_cons_erase eraseHasX).symm
            have arrange :
                Derives commutativeParityBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: remainder)) :=
              parityDerivesPermutation _ _ expandedPerm
            have contract :=
              contractLeadingTriple x remainder
            have reduced :
                positiveParityReduce (x :: y :: ys) =
                  (z :: zs).erase x := by
              change
                (if (positiveParityReduce (y :: ys)).count x < 2 then
                  x :: positiveParityReduce (y :: ys)
                else (positiveParityReduce (y :: ys)).erase x) =
                  (z :: zs).erase x
              rw [hs, if_neg hcount]
            cases he : (z :: zs).erase x with
            | nil =>
                rw [he] at eraseCount
                simp at eraseCount
            | cons r rs =>
                have restore :
                    Derives commutativeParityBasis
                      (wordOfCons x remainder)
                      (wordOfCons r rs) :=
                  parityDerivesPermutation _ _ <| by
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

theorem positiveParityDerivesNormal (w : Word Nat) :
    match positiveParityReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeParityBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact positiveParityDerivesNormalizeList head tail

/-- Generic unrestricted completeness theorem for the common basis. A model
only needs to separate support and parity of every variable. -/
theorem commutativeParityBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commutativeParityBasis)
    (support :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (parity :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2) :
    BasisFor T.semigroup commutativeParityBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :
      (positiveParityReduce e.lhs.toList).Perm
        (positiveParityReduce e.rhs.toList) :=
    positiveParityReduce_perm (support e valid) (parity e valid)
  have lhsNormal := positiveParityDerivesNormal e.lhs
  have rhsNormal := positiveParityDerivesNormal e.rhs
  cases hl : positiveParityReduce e.lhs.toList with
  | nil =>
      have present :
          e.lhs.head ∈ positiveParityReduce e.lhs.toList :=
        (mem_positiveParityReduce_iff _ _).mpr (by
          simp [Word.toList])
      exact False.elim (by simpa [hl] using present)
  | cons x xs =>
      cases hr : positiveParityReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (parityDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- Exact zero-based multiplication table for `S3_10`,
`[[1,2,1],[2,1,2],[1,2,3]]` in one-based notation. -/
def parityIdentityThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else 0
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else 1
  else
    if b = 0 then 0 else if b = 1 then 1 else 2

def parityIdentityThree : FiniteTable where
  order := 3
  mul := parityIdentityThreeMul
  assoc := by decide

private def identityParityState (n : Nat) : Fin 3 :=
  if n = 0 then 2 else ⟨n % 2, by omega⟩

private def identityParitySeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

private theorem identityParityMul_target (n : Nat) :
    parityIdentityThreeMul (identityParityState n) 1 =
      identityParityState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hnext : (n + 1) % 2 = 1 := by omega
      simp [identityParityState, parityIdentityThreeMul, hn, hp, hnext]
    · have hmod : n % 2 = 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [identityParityState, parityIdentityThreeMul, hn, hmod, hnext]

private theorem identityParityMul_other (n : Nat) :
    parityIdentityThreeMul (identityParityState n) 2 =
      identityParityState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · simp [identityParityState, parityIdentityThreeMul, hn, hp]
    · have hmod : n % 2 = 1 := by omega
      simp [identityParityState, parityIdentityThreeMul, hn, hmod]

private theorem identityParityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          parityIdentityThreeMul current (identityParitySeparator z x))
        (identityParityState acc) =
      identityParityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show identityParitySeparator z z = (1 : Fin 3) by
          simp [identityParitySeparator]]
        rw [identityParityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show identityParitySeparator z x = (2 : Fin 3) by
          simp [identityParitySeparator, hx]]
        rw [identityParityMul_other, ih]

theorem parityIdentityEval_separator (z : Nat) (w : Word Nat) :
    parityIdentityThree.semigroup.eval (identityParitySeparator z) w =
      identityParityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              parityIdentityThreeMul current
                (identityParitySeparator z x))
            (identityParitySeparator z head) =
          identityParityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show identityParitySeparator z z =
            identityParityState 1 by
          apply Fin.ext
          simp [identityParitySeparator, identityParityState]]
        rw [identityParityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show identityParitySeparator z head =
            identityParityState 0 by
          apply Fin.ext
          simp [identityParitySeparator, identityParityState, hhead]]
        rw [identityParityFold]
        congr 1
        omega

theorem parityIdentityValid_support (e : Identity Nat)
    (valid : e.SatisfiedBy parityIdentityThree.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (identityParitySeparator z)
  rw [parityIdentityEval_separator, parityIdentityEval_separator] at evaluated
  have zeroEq :
      e.lhs.toList.count z = 0 ↔ e.rhs.toList.count z = 0 := by
    constructor
    · intro hl
      by_cases hr : e.rhs.toList.count z = 0
      · exact hr
      · have specialized := evaluated
        simp only [identityParityState, if_pos hl, if_neg hr] at specialized
        change (2 : Fin 3) =
          ⟨e.rhs.toList.count z % 2, by omega⟩ at specialized
        have impossible := congrArg Fin.val specialized
        change 2 = e.rhs.toList.count z % 2 at impossible
        have bound := Nat.mod_lt (e.rhs.toList.count z) (by decide : 0 < 2)
        omega
    · intro hr
      by_cases hl : e.lhs.toList.count z = 0
      · exact hl
      · have specialized := evaluated
        simp only [identityParityState, if_neg hl, if_pos hr] at specialized
        change
          (⟨e.lhs.toList.count z % 2, by omega⟩ : Fin 3) = 2
          at specialized
        have impossible := congrArg Fin.val specialized
        change e.lhs.toList.count z % 2 = 2 at impossible
        have bound := Nat.mod_lt (e.lhs.toList.count z) (by decide : 0 < 2)
        omega
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor <;> intro hpos
  · have hnzero : e.lhs.toList.count z ≠ 0 := by omega
    have hrzero : e.rhs.toList.count z ≠ 0 :=
      fun hr => hnzero (zeroEq.mpr hr)
    omega
  · have hnzero : e.rhs.toList.count z ≠ 0 := by omega
    have hlzero : e.lhs.toList.count z ≠ 0 :=
      fun hl => hnzero (zeroEq.mp hl)
    omega

theorem parityIdentityValid_parity (e : Identity Nat)
    (valid : e.SatisfiedBy parityIdentityThree.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (identityParitySeparator z)
  rw [parityIdentityEval_separator, parityIdentityEval_separator] at evaluated
  by_cases hl : e.lhs.toList.count z = 0
  · have supportEq := parityIdentityValid_support e valid z
    have hr : e.rhs.toList.count z = 0 := by
      rw [List.count_eq_zero]
      exact fun h => (List.count_eq_zero.mp hl) (supportEq.mpr h)
    simp [hl, hr]
  · have supportEq := parityIdentityValid_support e valid z
    have hr : e.rhs.toList.count z ≠ 0 := by
      have lhsMem : z ∈ e.lhs.toList :=
        List.count_pos_iff.mp (Nat.pos_of_ne_zero hl)
      exact Nat.ne_of_gt <| List.count_pos_iff.mpr (supportEq.mp lhsMem)
    have specialized := evaluated
    simp only [identityParityState, if_neg hl, if_neg hr] at specialized
    exact Fin.mk.inj specialized

private theorem parityIdentityMul_power (a : Fin 3) :
    a =
      parityIdentityThreeMul
        (parityIdentityThreeMul a a) a := by
  decide +revert

private theorem parityIdentityMul_commutative (a b : Fin 3) :
    parityIdentityThreeMul a b = parityIdentityThreeMul b a := by
  decide +revert

theorem parityIdentityThreeBasis_models :
    Models parityIdentityThree.semigroup commutativeParityBasis := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      parityIdentityThreeMul
        (parityIdentityThreeMul (valuation 0) (valuation 0))
        (valuation 0)
    exact parityIdentityMul_power (valuation 0)
  · intro valuation
    change
      parityIdentityThreeMul (valuation 0) (valuation 1) =
        parityIdentityThreeMul (valuation 1) (valuation 0)
    exact parityIdentityMul_commutative (valuation 0) (valuation 1)

theorem parityIdentityThreeBasis_complete :
    BasisFor parityIdentityThree.semigroup commutativeParityBasis :=
  commutativeParityBasis_complete_of_separates parityIdentityThree
    parityIdentityThreeBasis_models parityIdentityValid_support
    parityIdentityValid_parity

/-- Exact zero-based multiplication table for `S3_11`,
`[[1,2,3],[2,1,3],[3,3,3]]` in one-based notation. -/
def parityZeroThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else 2
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else 2
  else
    2

def parityZeroThree : FiniteTable where
  order := 3
  mul := parityZeroThreeMul
  assoc := by decide

private def zeroParityValue (n : Nat) : Fin 3 :=
  ⟨n % 2, by omega⟩

private def zeroParitySeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 0

private theorem zeroParityMul_target (n : Nat) :
    parityZeroThreeMul (zeroParityValue n) 1 =
      zeroParityValue (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [zeroParityValue, parityZeroThreeMul, hp, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [zeroParityValue, parityZeroThreeMul, hmod, hnext]

private theorem zeroParityMul_other (n : Nat) :
    parityZeroThreeMul (zeroParityValue n) 0 =
      zeroParityValue n := by
  by_cases hp : n % 2 = 0
  · simp [zeroParityValue, parityZeroThreeMul, hp]
  · have hmod : n % 2 = 1 := by omega
    simp [zeroParityValue, parityZeroThreeMul, hmod]

private theorem zeroParityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          parityZeroThreeMul current (zeroParitySeparator z x))
        (zeroParityValue acc) =
      zeroParityValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show zeroParitySeparator z z = (1 : Fin 3) by
          simp [zeroParitySeparator]]
        rw [zeroParityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show zeroParitySeparator z x = (0 : Fin 3) by
          simp [zeroParitySeparator, hx]]
        rw [zeroParityMul_other, ih]

theorem parityZeroEval_paritySeparator (z : Nat) (w : Word Nat) :
    parityZeroThree.semigroup.eval (zeroParitySeparator z) w =
      zeroParityValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              parityZeroThreeMul current (zeroParitySeparator z x))
            (zeroParitySeparator z head) =
          zeroParityValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show zeroParitySeparator z z = zeroParityValue 1 by
          apply Fin.ext
          simp [zeroParitySeparator, zeroParityValue]]
        rw [zeroParityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show zeroParitySeparator z head = zeroParityValue 0 by
          apply Fin.ext
          simp [zeroParitySeparator, zeroParityValue, hhead]]
        rw [zeroParityFold]
        congr 1
        omega

private def zeroSupportState (n : Nat) : Fin 3 :=
  if n = 0 then 0 else 2

private def zeroSupportSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 2 else 0

private theorem zeroSupportMul_target (n : Nat) :
    parityZeroThreeMul (zeroSupportState n) 2 =
      zeroSupportState (n + 1) := by
  apply Fin.ext
  simp [parityZeroThreeMul, zeroSupportState]

private theorem zeroSupportMul_other (n : Nat) :
    parityZeroThreeMul (zeroSupportState n) 0 =
      zeroSupportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [zeroSupportState, parityZeroThreeMul, hn]

private theorem zeroSupportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          parityZeroThreeMul current (zeroSupportSeparator z x))
        (zeroSupportState acc) =
      zeroSupportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show zeroSupportSeparator z z = (2 : Fin 3) by
          simp [zeroSupportSeparator]]
        rw [zeroSupportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show zeroSupportSeparator z x = (0 : Fin 3) by
          simp [zeroSupportSeparator, hx]]
        rw [zeroSupportMul_other, ih]

theorem parityZeroEval_supportSeparator (z : Nat) (w : Word Nat) :
    parityZeroThree.semigroup.eval (zeroSupportSeparator z) w =
      zeroSupportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              parityZeroThreeMul current (zeroSupportSeparator z x))
            (zeroSupportSeparator z head) =
          zeroSupportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show zeroSupportSeparator z z = zeroSupportState 1 by
          apply Fin.ext
          simp [zeroSupportSeparator, zeroSupportState]]
        rw [zeroSupportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show zeroSupportSeparator z head = zeroSupportState 0 by
          apply Fin.ext
          simp [zeroSupportSeparator, zeroSupportState, hhead]]
        rw [zeroSupportFold]
        congr 1
        omega

theorem parityZeroValid_support (e : Identity Nat)
    (valid : e.SatisfiedBy parityZeroThree.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (zeroSupportSeparator z)
  rw [parityZeroEval_supportSeparator,
    parityZeroEval_supportSeparator] at evaluated
  have zeroEq :
      e.lhs.toList.count z = 0 ↔ e.rhs.toList.count z = 0 := by
    constructor
    · intro hl
      by_cases hr : e.rhs.toList.count z = 0
      · exact hr
      · have specialized := evaluated
        simp only [zeroSupportState, if_pos hl, if_neg hr] at specialized
        change (0 : Fin 3) = 2 at specialized
        have impossible := Fin.mk.inj specialized
        omega
    · intro hr
      by_cases hl : e.lhs.toList.count z = 0
      · exact hl
      · have specialized := evaluated
        simp only [zeroSupportState, if_neg hl, if_pos hr] at specialized
        change (2 : Fin 3) = 0 at specialized
        have impossible := Fin.mk.inj specialized
        omega
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor <;> intro hpos
  · have hnzero : e.lhs.toList.count z ≠ 0 := by omega
    have hrzero : e.rhs.toList.count z ≠ 0 :=
      fun hr => hnzero (zeroEq.mpr hr)
    omega
  · have hnzero : e.rhs.toList.count z ≠ 0 := by omega
    have hlzero : e.lhs.toList.count z ≠ 0 :=
      fun hl => hnzero (zeroEq.mp hl)
    omega

theorem parityZeroValid_parity (e : Identity Nat)
    (valid : e.SatisfiedBy parityZeroThree.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (zeroParitySeparator z)
  rw [parityZeroEval_paritySeparator,
    parityZeroEval_paritySeparator] at evaluated
  exact Fin.mk.inj evaluated

private theorem parityZeroMul_power (a : Fin 3) :
    a =
      parityZeroThreeMul
        (parityZeroThreeMul a a) a := by
  decide +revert

private theorem parityZeroMul_commutative (a b : Fin 3) :
    parityZeroThreeMul a b = parityZeroThreeMul b a := by
  decide +revert

theorem parityZeroThreeBasis_models :
    Models parityZeroThree.semigroup commutativeParityBasis := by
  intro e he
  simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      parityZeroThreeMul
        (parityZeroThreeMul (valuation 0) (valuation 0))
        (valuation 0)
    exact parityZeroMul_power (valuation 0)
  · intro valuation
    change
      parityZeroThreeMul (valuation 0) (valuation 1) =
        parityZeroThreeMul (valuation 1) (valuation 0)
    exact parityZeroMul_commutative (valuation 0) (valuation 1)

theorem parityZeroThreeBasis_complete :
    BasisFor parityZeroThree.semigroup commutativeParityBasis :=
  commutativeParityBasis_complete_of_separates parityZeroThree
    parityZeroThreeBasis_models parityZeroValid_support
    parityZeroValid_parity

private theorem reverse_parityX : parityX.reverse = parityX := by
  apply Word.toList_injective
  simp [parityX]

private theorem reverse_parityXXX : parityXXX.reverse = parityXXX := by
  apply Word.toList_injective
  decide

private theorem reverse_parityXY : parityXY.reverse = parityYX := by
  apply Word.toList_injective
  decide

private theorem reverse_parityYX : parityYX.reverse = parityXY := by
  apply Word.toList_injective
  decide

private def parityCommutativityLawSymm : Identity Nat :=
  ⟨parityYX, parityXY⟩

private theorem reversed_parityPowerLaw :
    parityPowerLaw.reversed = parityPowerLaw := by
  simp [parityPowerLaw, Identity.reversed, reverse_parityX,
    reverse_parityXXX]

private theorem reversed_parityCommutativityLaw :
    parityCommutativityLaw.reversed =
      parityCommutativityLawSymm := by
  simp [parityCommutativityLaw, parityCommutativityLawSymm,
    Identity.reversed, reverse_parityXY, reverse_parityYX]

/-- The basis is unchanged, up to derivable symmetry, by word reversal. -/
theorem commutativeParityBasis_opposite_complete
    {G : Semigroup S}
    (complete : BasisFor G commutativeParityBasis) :
    BasisFor G.opposite commutativeParityBasis := by
  have reversedComplete := complete.oppositeReversed
  apply reversedComplete.replace
  · intro e he
    simp only [commutativeParityBasis, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_parityPowerLaw]
      exact complete.1 parityPowerLaw (List.Mem.head _)
    · rw [Identity.satisfiedBy_opposite_iff_reversed,
        reversed_parityCommutativityLaw]
      intro valuation
      exact
        (complete.1 parityCommutativityLaw
          (List.Mem.tail _ (List.Mem.head _)) valuation).symm
  · intro e he
    simp only [reversedBasis, commutativeParityBasis, List.map_cons,
      List.map_nil, reversed_parityPowerLaw,
      reversed_parityCommutativityLaw, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Derives.fromBasis (List.Mem.head _)
    · exact Derives.symm <|
        Derives.fromBasis (List.Mem.tail _ (List.Mem.head _))

theorem parityIdentityThreeOppositeBasis_complete :
    BasisFor parityIdentityThree.semigroup.opposite
      commutativeParityBasis :=
  commutativeParityBasis_opposite_complete
    parityIdentityThreeBasis_complete

theorem parityZeroThreeOppositeBasis_complete :
    BasisFor parityZeroThree.semigroup.opposite commutativeParityBasis :=
  commutativeParityBasis_opposite_complete parityZeroThreeBasis_complete

end SemigroupBasis.Examples

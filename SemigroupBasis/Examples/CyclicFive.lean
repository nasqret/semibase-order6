import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The catalogue numbering of the additive residues modulo five. -/
def cyclicFiveEncode (a : Fin 5) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 4
  else 3

/-- The inverse residue numbering for the catalogue table. -/
def cyclicFiveDecode (a : Fin 5) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 4
  else 3

theorem cyclicFiveDecode_encode (a : Fin 5) :
    cyclicFiveDecode (cyclicFiveEncode a) = a := by
  decide +revert

/-- Addition modulo five transported to the exact catalogue numbering. -/
def cyclicFiveMul (a b : Fin 5) : Fin 5 :=
  cyclicFiveEncode
    ⟨((cyclicFiveDecode a).val + (cyclicFiveDecode b).val) % 5,
      Nat.mod_lt _ (by decide)⟩

/-- The cyclic group of order five, viewed as a semigroup. -/
def cyclicFive : FiniteTable where
  order := 5
  mul := cyclicFiveMul
  assoc := by decide

def cyclicFiveX : Word Nat := Word.singleton 0
def cyclicFiveY : Word Nat := Word.singleton 1
def cyclicFiveXY : Word Nat := ⟨0, [1]⟩
def cyclicFiveYX : Word Nat := ⟨1, [0]⟩
def cyclicFiveXXXXXY : Word Nat := ⟨0, [0, 0, 0, 0, 1]⟩

def cyclicFiveCommutativityLaw : Identity Nat :=
  ⟨cyclicFiveXY, cyclicFiveYX⟩

def cyclicFiveCancellationLaw : Identity Nat :=
  ⟨cyclicFiveXXXXXY, cyclicFiveY⟩

/-- The semigroup basis `xy = yx`, `xxxxxy = y` for `C5`. -/
def cyclicFiveBasis : List (Identity Nat) :=
  [cyclicFiveCommutativityLaw, cyclicFiveCancellationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem cyclicFiveDerivesCommutativity (u v : Word Nat) :
    Derives cyclicFiveBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicFiveBasis cyclicFiveXY cyclicFiveYX :=
    Derives.fromBasis (e := cyclicFiveCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicFiveBasis, cyclicFiveCommutativityLaw,
    cyclicFiveXY, cyclicFiveYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicFiveDerivesCancelFifth (u v : Word Nat) :
    Derives cyclicFiveBasis
      (((((u ++ u) ++ u) ++ u) ++ u) ++ v) v := by
  have hbase :
      Derives cyclicFiveBasis cyclicFiveXXXXXY cyclicFiveY :=
    Derives.fromBasis (e := cyclicFiveCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicFiveBasis, cyclicFiveCancellationLaw,
    cyclicFiveXXXXXY, cyclicFiveY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Every fifth power represents the unique nonempty zero exponent vector. -/
theorem cyclicFiveDerivesCommonFifth (u v : Word Nat) :
    Derives cyclicFiveBasis
      ((((u ++ u) ++ u) ++ u) ++ u)
      ((((v ++ v) ++ v) ++ v) ++ v) := by
  have addV :
      Derives cyclicFiveBasis
        ((((u ++ u) ++ u) ++ u) ++ u)
        (((((v ++ v) ++ v) ++ v) ++ v) ++
          ((((u ++ u) ++ u) ++ u) ++ u)) :=
    Derives.symm
      (cyclicFiveDerivesCancelFifth v
        ((((u ++ u) ++ u) ++ u) ++ u))
  have commute :
      Derives cyclicFiveBasis
        (((((v ++ v) ++ v) ++ v) ++ v) ++
          ((((u ++ u) ++ u) ++ u) ++ u))
        (((((u ++ u) ++ u) ++ u) ++ u) ++
          ((((v ++ v) ++ v) ++ v) ++ v)) :=
    cyclicFiveDerivesCommutativity
      ((((v ++ v) ++ v) ++ v) ++ v)
      ((((u ++ u) ++ u) ++ u) ++ u)
  exact Derives.trans addV <|
    Derives.trans commute
      (cyclicFiveDerivesCancelFifth u
        ((((v ++ v) ++ v) ++ v) ++ v))

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicFiveBasis
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
              cyclicFiveDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicFiveDerivesCommutativity
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

theorem cyclicFiveDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicFiveBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain zero through four copies according to multiplicity modulo five. -/
def quinternaryReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := quinternaryReduce xs
      if reduced.count x < 4 then x :: reduced
      else (((reduced.erase x).erase x).erase x).erase x

theorem count_quinternaryReduce (z : Nat) (xs : List Nat) :
    (quinternaryReduce xs).count z = xs.count z % 5 := by
  induction xs generalizing z with
  | nil =>
      simp [quinternaryReduce]
  | cons x xs ih =>
      simp only [quinternaryReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · have reducedLe :
            (quinternaryReduce xs).count x < 5 := by
          rw [ih x]
          exact Nat.mod_lt _ (by decide)
        have reducedEq : (quinternaryReduce xs).count x = 4 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countMod : xs.count x % 5 = 4 := by
            rw [← ih x]
            exact reducedEq
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_erase_self,
            List.count_cons_self, reducedEq]
          simp [Nat.add_mod, countMod]
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

theorem quinternaryReduce_perm_of_mod_eq {xs ys : List Nat}
    (hmod : ∀ z, xs.count z % 5 = ys.count z % 5) :
    (quinternaryReduce xs).Perm (quinternaryReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_quinternaryReduce, count_quinternaryReduce, hmod z]

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

private theorem cyclicFiveDerivesNormalizeList :
    ∀ x xs,
      match quinternaryReduce (x :: xs) with
      | [] =>
          Derives cyclicFiveBasis (wordOfCons x xs)
            ((((Word.singleton x ++ Word.singleton x) ++
                Word.singleton x) ++ Word.singleton x) ++
              Word.singleton x)
      | y :: ys =>
          Derives cyclicFiveBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := cyclicFiveDerivesNormalizeList y ys
      cases hs : quinternaryReduce (y :: ys) with
      | nil =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have commute :=
            cyclicFiveDerivesCommutativity
              (Word.singleton x)
              ((((Word.singleton y ++ Word.singleton y) ++
                  Word.singleton y) ++ Word.singleton y) ++
                Word.singleton y)
          have cancel :=
            cyclicFiveDerivesCancelFifth
              (Word.singleton y) (Word.singleton x)
          have reduced : quinternaryReduce (x :: y :: ys) = [x] := by
            change
              (if (quinternaryReduce (y :: ys)).count x < 4 then
                x :: quinternaryReduce (y :: ys)
              else
                ((((quinternaryReduce (y :: ys)).erase x).erase x).erase x).erase x) =
                [x]
            rw [hs]
            rfl
          rw [reduced]
          exact Derives.trans
            (by
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc] using prefixed)
            (Derives.trans
              (by simpa [Word.append_assoc] using commute)
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using cancel))
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          let normal : Word Nat := wordOfCons z zs
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                quinternaryReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (quinternaryReduce (y :: ys)).count x < 4 then
                  x :: quinternaryReduce (y :: ys)
                else
                  ((((quinternaryReduce (y :: ys)).erase x).erase x).erase x).erase x) =
                    x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [normal, wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have reducedLe :
                (z :: zs).count x < 5 := by
              have h := count_quinternaryReduce x (y :: ys)
              rw [hs] at h
              rw [h]
              exact Nat.mod_lt _ (by decide)
            have countEq : (z :: zs).count x = 4 := by
              omega
            have hperm :=
              four_copies_perm x (z :: zs) countEq
            have reorder :
                Derives cyclicFiveBasis normal
                  (wordOfCons x
                    (x :: x :: x ::
                      ((((z :: zs).erase x).erase x).erase x).erase x)) :=
              cyclicFiveDerivesPermutation normal
                (wordOfCons x
                  (x :: x :: x ::
                    ((((z :: zs).erase x).erase x).erase x).erase x))
                hperm
            have withPrefix :=
              Derives.prepend (Word.singleton x) reorder
            cases he : ((((z :: zs).erase x).erase x).erase x).erase x with
            | nil =>
                have reduced :
                    quinternaryReduce (x :: y :: ys) = [] := by
                  change
                    (if (quinternaryReduce (y :: ys)).count x < 4 then
                      x :: quinternaryReduce (y :: ys)
                    else
                      ((((quinternaryReduce (y :: ys)).erase x).erase x).erase x).erase x) =
                      []
                  rw [hs, if_neg hcount, he]
                rw [he] at withPrefix
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using prefixed)
                  (by
                    simpa [normal, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using withPrefix)
            | cons r rs =>
                let remainder : Word Nat := wordOfCons r rs
                have cancel :=
                  cyclicFiveDerivesCancelFifth
                    (Word.singleton x) remainder
                have reduced :
                    quinternaryReduce (x :: y :: ys) = r :: rs := by
                  change
                    (if (quinternaryReduce (y :: ys)).count x < 4 then
                      x :: quinternaryReduce (y :: ys)
                    else
                      ((((quinternaryReduce (y :: ys)).erase x).erase x).erase x).erase x) =
                        r :: rs
                  rw [hs, if_neg hcount, he]
                rw [he] at withPrefix
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append, Word.singleton,
                      Word.append_assoc] using prefixed)
                  (Derives.trans
                    (by
                      simpa [normal, remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using withPrefix)
                    (by
                      simpa [remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using cancel))
termination_by
  _ xs => xs.length

theorem cyclicFiveDerivesNormal (w : Word Nat) :
    match quinternaryReduce w.toList with
    | [] =>
        Derives cyclicFiveBasis w
          ((((Word.singleton w.head ++ Word.singleton w.head) ++
              Word.singleton w.head) ++ Word.singleton w.head) ++
            Word.singleton w.head)
    | x :: xs =>
        Derives cyclicFiveBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact cyclicFiveDerivesNormalizeList head tail

private def quinternaryValue (n : Nat) : Fin 5 :=
  cyclicFiveEncode ⟨n % 5, Nat.mod_lt _ (by decide)⟩

private theorem cyclicFiveMul_quinternaryValue (m n : Nat) :
    cyclicFiveMul (quinternaryValue m) (quinternaryValue n) =
      quinternaryValue (m + n) := by
  unfold cyclicFiveMul quinternaryValue
  apply congrArg cyclicFiveEncode
  apply Fin.ext
  simp [cyclicFiveDecode_encode, Nat.add_mod]

private def quinternarySeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 1 else 0

private theorem cyclicFiveFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          cyclicFiveMul current (quinternarySeparator z x))
        (quinternaryValue acc) =
      quinternaryValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show quinternarySeparator z z = quinternaryValue 1 by
          simp [quinternarySeparator, quinternaryValue,
            cyclicFiveEncode]]
        rw [cyclicFiveMul_quinternaryValue, ih]
        unfold quinternaryValue
        apply congrArg cyclicFiveEncode
        apply Fin.ext
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · rw [List.count_cons_of_ne hx]
        rw [show quinternarySeparator z x = quinternaryValue 0 by
          simp [quinternarySeparator, hx, quinternaryValue,
            cyclicFiveEncode]]
        rw [cyclicFiveMul_quinternaryValue, ih]
        unfold quinternaryValue
        apply congrArg cyclicFiveEncode
        apply Fin.ext
        simp

theorem cyclicFiveEval_separator (z : Nat) (w : Word Nat) :
    cyclicFive.semigroup.eval (quinternarySeparator z) w =
      quinternaryValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicFiveMul current (quinternarySeparator z x))
            (quinternarySeparator z head) =
          quinternaryValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show quinternarySeparator z z = quinternaryValue 1 by
          simp [quinternarySeparator, quinternaryValue,
            cyclicFiveEncode]]
        rw [cyclicFiveFold_separator]
        unfold quinternaryValue
        apply congrArg cyclicFiveEncode
        apply Fin.ext
        simp [Nat.add_comm]
      · rw [List.count_cons_of_ne hhead]
        rw [show quinternarySeparator z head = quinternaryValue 0 by
          simp [quinternarySeparator, hhead, quinternaryValue,
            cyclicFiveEncode]]
        rw [cyclicFiveFold_separator]
        unfold quinternaryValue
        apply congrArg cyclicFiveEncode
        apply Fin.ext
        simp

theorem cyclicFiveValid_mod_eq (e : Identity Nat)
    (valid : e.SatisfiedBy cyclicFive.semigroup) :
    ∀ z, e.lhs.toList.count z % 5 =
      e.rhs.toList.count z % 5 := by
  intro z
  have evaluated := valid (quinternarySeparator z)
  rw [cyclicFiveEval_separator, cyclicFiveEval_separator] at evaluated
  have decoded := congrArg cyclicFiveDecode evaluated
  simp only [quinternaryValue, cyclicFiveDecode_encode] at decoded
  exact Fin.mk.inj decoded

theorem cyclicFiveBasis_models :
    Models cyclicFive.semigroup cyclicFiveBasis := by
  intro e he
  simp only [cyclicFiveBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change cyclicFiveMul (valuation 0) (valuation 1) =
      cyclicFiveMul (valuation 1) (valuation 0)
    unfold cyclicFiveMul
    congr 1
    apply Fin.ext
    simp [Nat.add_comm]
  · intro valuation
    change
      cyclicFiveMul
          (cyclicFiveMul
            (cyclicFiveMul
              (cyclicFiveMul
                (cyclicFiveMul (valuation 0) (valuation 0))
                (valuation 0))
              (valuation 0))
            (valuation 0))
          (valuation 1) =
        valuation 1
    have cancellation (a b : Fin 5) :
        cyclicFiveMul
            (cyclicFiveMul
              (cyclicFiveMul
                (cyclicFiveMul (cyclicFiveMul a a) a) a) a) b = b := by
      decide +revert
    exact cancellation (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Equal exponent vectors
modulo five normalize to the same one-to-four-copy support; the zero vector
uses the common fifth-power class. -/
theorem cyclicFiveBasis_complete :
    BasisFor cyclicFive.semigroup cyclicFiveBasis := by
  refine ⟨cyclicFiveBasis_models, ?_⟩
  intro e valid
  have modEq := cyclicFiveValid_mod_eq e valid
  have reducedPerm :
      (quinternaryReduce e.lhs.toList).Perm
        (quinternaryReduce e.rhs.toList) :=
    quinternaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicFiveDerivesNormal e.lhs
  have rhsNormal := cyclicFiveDerivesNormal e.rhs
  cases hl : quinternaryReduce e.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : quinternaryReduce e.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicFiveDerivesCommonFifth
            (Word.singleton e.lhs.head)
            (Word.singleton e.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : quinternaryReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (cyclicFiveDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

theorem cyclicFive_selfDual :
    cyclicFive.semigroup.opposite = cyclicFive.semigroup := by
  unfold cyclicFive FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  unfold cyclicFiveMul
  congr 1
  apply Fin.ext
  simp [Nat.add_comm]

theorem cyclicFiveOppositeBasis_complete :
    BasisFor cyclicFive.semigroup.opposite cyclicFiveBasis := by
  rw [cyclicFive_selfDual]
  exact cyclicFiveBasis_complete

end SemigroupBasis.Examples

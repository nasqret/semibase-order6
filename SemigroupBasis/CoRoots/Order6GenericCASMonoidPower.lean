import SemigroupBasis.FiniteNilpotent
import SemigroupBasis.Generated.Order6GenericCASRootData

namespace SemigroupBasis.CoRoots.Order6GenericCASMonoidPower

open SemigroupBasis

/-!
# Generic commutative-monoid power endpoints

The normalizer in this file is the parameterized version of the
commutative power normal forms used throughout `SemigroupBasis.Examples`.
For positive `index` and `period`, it treats

`xy = yx`, `x^index = x^(index + period)`

as a basis and reduces every variable multiplicity to a state in
`0, ..., index + period - 1`.  The finite-table layer below separates those
states by evaluating one variable at every table element and every other
variable at the table identity.
-/

def monoidPowerXY : Word Nat := ⟨0, [1]⟩
def monoidPowerYX : Word Nat := ⟨1, [0]⟩

def monoidPowerUnaryWord (copies : Nat) : Word Nat :=
  ⟨0, List.replicate (copies - 1) 0⟩

def monoidPowerCommutativityLaw : Identity Nat :=
  ⟨monoidPowerXY, monoidPowerYX⟩

def monoidPowerLaw (index period : Nat) : Identity Nat :=
  ⟨monoidPowerUnaryWord index,
    monoidPowerUnaryWord (index + period)⟩

def monoidPowerBasis (index period : Nat) : List (Identity Nat) :=
  [monoidPowerCommutativityLaw, monoidPowerLaw index period]

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem monoidPowerDerivesCommutativity
    (index period : Nat) (u v : Word Nat) :
    Derives (monoidPowerBasis index period) (u ++ v) (v ++ u) := by
  have base :
      Derives (monoidPowerBasis index period)
        monoidPowerXY monoidPowerYX :=
    Derives.fromBasis (e := monoidPowerCommutativityLaw) <|
      List.Mem.head _
  have substituted := Derives.subst base (instantiateTwoWords u v)
  simpa [monoidPowerBasis, monoidPowerCommutativityLaw,
    monoidPowerXY, monoidPowerYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using substituted

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private inductive ListDerives (index period : Nat) :
    List Nat → List Nat → Prop
  | empty : ListDerives index period [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives (monoidPowerBasis index period)
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives index period (x :: xs) (y :: ys)

private theorem listDerives_of_perm (index period : Nat)
    {xs ys : List Nat} (permutation : xs.Perm ys) :
    ListDerives index period xs ys := by
  induction permutation with
  | nil =>
      exact ListDerives.empty
  | cons x _ induction =>
      cases induction with
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
              monoidPowerDerivesCommutativity index period
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (monoidPowerDerivesCommutativity index period
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ first second =>
      cases first with
      | empty =>
          cases second
          exact ListDerives.empty
      | words firstDerivation =>
          cases second with
          | words secondDerivation =>
              exact ListDerives.words <|
                Derives.trans firstDerivation secondDerivation

theorem monoidPowerDerivesPermutation
    (index period : Nat) (u v : Word Nat)
    (permutation : u.toList.Perm v.toList) :
    Derives (monoidPowerBasis index period) u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm index period permutation with
          | words derivation => exact derivation

theorem monoidPowerDerivesContraction
    (index period : Nat) (x : Nat) :
    Derives (monoidPowerBasis index period)
      (wordOfCons x (List.replicate (index + period - 1) x))
      (wordOfCons x (List.replicate (index - 1) x)) := by
  have base :
      Derives (monoidPowerBasis index period)
        (monoidPowerUnaryWord (index + period))
        (monoidPowerUnaryWord index) :=
    Derives.symm <|
      Derives.fromBasis (e := monoidPowerLaw index period) <|
        List.Mem.tail _ (List.Mem.head _)
  have renamed := base.rename (fun _ => x)
  simpa [monoidPowerUnaryWord, wordOfCons, Word.map] using renamed

private theorem monoidPowerDerivesContractionWithSuffix
    (index period : Nat) (x : Nat) :
    ∀ suffix : List Nat,
      Derives (monoidPowerBasis index period)
        (wordOfCons x
          (List.replicate (index + period - 1) x ++ suffix))
        (wordOfCons x (List.replicate (index - 1) x ++ suffix))
  | [] => by
      simpa using monoidPowerDerivesContraction index period x
  | y :: ys => by
      have appended :=
        Derives.appendRight
          (monoidPowerDerivesContraction index period x)
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append] using appended

/-- One transition in the canonical exponent automaton. -/
def monoidPowerAdvance (index period state : Nat) : Nat :=
  if state < index + period - 1 then state + 1 else index

/-- The canonical exponent represented by a multiplicity. -/
def monoidPowerExponent (index period : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      monoidPowerAdvance index period
        (monoidPowerExponent index period n)

theorem monoidPowerExponent_le
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) (n : Nat) :
    monoidPowerExponent index period n ≤ index + period - 1 := by
  induction n with
  | zero =>
      simp [monoidPowerExponent]
  | succ n induction =>
      simp only [monoidPowerExponent, monoidPowerAdvance]
      split <;> omega

theorem monoidPowerExponent_pos
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) {n : Nat} (nPos : 0 < n) :
    0 < monoidPowerExponent index period n := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [monoidPowerExponent, monoidPowerAdvance]
      split <;> omega

def monoidPowerExponentState
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) (n : Nat) : Fin (index + period) :=
  ⟨monoidPowerExponent index period n, by
    have bound :=
      monoidPowerExponent_le index period indexPos periodPos n
    omega⟩

private def eraseCopies (x : Nat) : Nat → List Nat → List Nat
  | 0, letters => letters
  | n + 1, letters => eraseCopies x n (letters.erase x)

private theorem count_eraseCopies_self
    (x : Nat) (n : Nat) (letters : List Nat) :
    (eraseCopies x n letters).count x = letters.count x - n := by
  induction n generalizing letters with
  | zero => rfl
  | succ n induction =>
      rw [eraseCopies, induction, List.count_erase_self]
      omega

private theorem count_eraseCopies_of_ne
    (x z : Nat) (n : Nat) (letters : List Nat) (different : z ≠ x) :
    (eraseCopies x n letters).count z = letters.count z := by
  induction n generalizing letters with
  | zero => rfl
  | succ n induction =>
      rw [eraseCopies, induction, List.count_erase_of_ne different]

private theorem count_replicate_of_ne
    {x z : Nat} (different : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different n]

/-- Normalize every multiplicity with the power automaton. -/
def monoidPowerReduce (index period : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := monoidPowerReduce index period xs
      if reduced.count x < index + period - 1 then
        x :: reduced
      else
        eraseCopies x period (x :: reduced)

theorem count_monoidPowerReduce
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) (z : Nat) (letters : List Nat) :
    (monoidPowerReduce index period letters).count z =
      monoidPowerExponent index period (letters.count z) := by
  induction letters with
  | nil =>
      simp [monoidPowerReduce, monoidPowerExponent]
  | cons x xs induction =>
      simp only [monoidPowerReduce]
      split <;> rename_i countSmall
      · by_cases same : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, induction]
          rw [induction] at countSmall
          simp [monoidPowerExponent, monoidPowerAdvance, countSmall]
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same), induction]
      · by_cases same : z = x
        · subst z
          rw [count_eraseCopies_self, List.count_cons_self,
            List.count_cons_self, induction]
          have bound :=
            monoidPowerExponent_le index period indexPos periodPos
              (xs.count x)
          rw [induction] at countSmall
          simp [monoidPowerExponent, monoidPowerAdvance, countSmall]
          omega
        · rw [count_eraseCopies_of_ne x z period _ same,
            List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same), induction]

private theorem monoidPowerReduce_cons_ne_nil
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) (x : Nat) (xs : List Nat) :
    monoidPowerReduce index period (x :: xs) ≠ [] := by
  intro empty
  have countIdentity :=
    count_monoidPowerReduce index period indexPos periodPos x (x :: xs)
  rw [empty, List.count_nil, List.count_cons_self] at countIdentity
  have positive :=
    monoidPowerExponent_pos index period indexPos periodPos
      (n := xs.count x + 1) (by omega)
  omega

private theorem monoidPowerReduce_perm_of_exponent_eq
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) {left right : List Nat}
    (same :
      ∀ z, monoidPowerExponent index period (left.count z) =
        monoidPowerExponent index period (right.count z)) :
    (monoidPowerReduce index period left).Perm
      (monoidPowerReduce index period right) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_monoidPowerReduce index period indexPos periodPos,
    count_monoidPowerReduce index period indexPos periodPos, same z]

private theorem monoidPowerDerivesNormalizeList
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) :
    ∀ x xs,
      match monoidPowerReduce index period (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives (monoidPowerBasis index period)
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have maximumPos : 0 < index + period - 1 := by omega
      simpa [monoidPowerReduce, maximumPos] using
        (Derives.refl (wordOfCons x []))
  | x, y :: ys => by
      have suffixNormal :=
        monoidPowerDerivesNormalizeList index period indexPos periodPos y ys
      cases suffixShape : monoidPowerReduce index period (y :: ys) with
      | nil =>
          exact False.elim <|
            monoidPowerReduce_cons_ne_nil
              index period indexPos periodPos y ys suffixShape
      | cons z zs =>
          rw [suffixShape] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases countSmall : (z :: zs).count x < index + period - 1
          · have reduced :
                monoidPowerReduce index period (x :: y :: ys) =
                  x :: z :: zs := by
              change
                (if
                    (monoidPowerReduce index period (y :: ys)).count x <
                      index + period - 1
                  then x :: monoidPowerReduce index period (y :: ys)
                  else
                    eraseCopies x period
                      (x :: monoidPowerReduce index period (y :: ys))) =
                  x :: z :: zs
              rw [suffixShape, if_pos countSmall]
            rw [reduced]
            simpa [wordOfCons, Word.singleton, Word.append] using prefixed
          · have countLe :
                (z :: zs).count x ≤ index + period - 1 := by
              rw [← suffixShape,
                count_monoidPowerReduce
                  index period indexPos periodPos]
              exact monoidPowerExponent_le
                index period indexPos periodPos _
            have countEq :
                (z :: zs).count x = index + period - 1 := by
              omega
            let full : List Nat := x :: z :: zs
            let remainder : List Nat :=
              eraseCopies x (index + period) full
            have fullCount : full.count x = index + period := by
              simp [full, countEq]
              omega
            have arrangePermutation :
                full.Perm
                  (x ::
                    (List.replicate (index + period - 1) x ++
                      remainder)) := by
              rw [List.perm_iff_count]
              intro tested
              by_cases same : tested = x
              · subst tested
                simp [full, remainder, List.count_append,
                  count_eraseCopies_self, fullCount]
                omega
              · rw [List.count_cons_of_ne (Ne.symm same),
                  List.count_cons_of_ne (Ne.symm same)]
                dsimp [remainder]
                rw [List.count_append]
                rw [count_eraseCopies_of_ne
                  x tested (index + period) full same]
                simp [full, same, Ne.symm same]
                exact count_replicate_of_ne same _
            have arrange :
                Derives (monoidPowerBasis index period)
                  (wordOfCons x (z :: zs))
                  (wordOfCons x
                    (List.replicate (index + period - 1) x ++
                      remainder)) :=
              monoidPowerDerivesPermutation index period _ _ <| by
                simpa [full, wordOfCons, Word.toList] using
                  arrangePermutation
            have contract :=
              monoidPowerDerivesContractionWithSuffix
                index period x remainder
            let reduced : List Nat := eraseCopies x period full
            have reducedCount : reduced.count x = index := by
              simp [reduced, count_eraseCopies_self, fullCount]
            have restorePermutation :
                (x ::
                    (List.replicate (index - 1) x ++ remainder)).Perm
                  reduced := by
              rw [List.perm_iff_count]
              intro tested
              by_cases same : tested = x
              · subst tested
                simp [reduced, remainder, List.count_append,
                  count_eraseCopies_self, fullCount]
                omega
              · rw [List.count_cons_of_ne (Ne.symm same)]
                rw [count_eraseCopies_of_ne
                  x tested period full same]
                rw [List.count_append]
                dsimp [remainder]
                rw [count_eraseCopies_of_ne
                  x tested (index + period) full same]
                simp [same, Ne.symm same]
                exact count_replicate_of_ne same _
            have reducedIdentity :
                monoidPowerReduce index period (x :: y :: ys) =
                  reduced := by
              change
                (if
                    (monoidPowerReduce index period (y :: ys)).count x <
                      index + period - 1
                  then x :: monoidPowerReduce index period (y :: ys)
                  else
                    eraseCopies x period
                      (x :: monoidPowerReduce index period (y :: ys))) =
                  reduced
              rw [suffixShape, if_neg countSmall]
            cases reducedShape : reduced with
            | nil =>
                rw [reducedShape, List.count_nil] at reducedCount
                omega
            | cons r rs =>
                have restore :
                    Derives (monoidPowerBasis index period)
                      (wordOfCons x
                        (List.replicate (index - 1) x ++ remainder))
                      (wordOfCons r rs) :=
                  monoidPowerDerivesPermutation index period _ _ <| by
                    rw [reducedShape] at restorePermutation
                    simpa [wordOfCons, Word.toList] using
                      restorePermutation
                rw [reducedShape] at reducedIdentity
                rw [reducedIdentity]
                exact Derives.trans
                  (by
                    simpa [full, wordOfCons, Word.singleton,
                      Word.append] using prefixed)
                  (Derives.trans arrange <|
                    Derives.trans contract restore)
termination_by
  _ xs => xs.length

theorem monoidPowerDerivesNormal
    (index period : Nat) (indexPos : 0 < index)
    (periodPos : 0 < period) (word : Word Nat) :
    match monoidPowerReduce index period word.toList with
    | [] => False
    | x :: xs =>
        Derives (monoidPowerBasis index period)
          word (wordOfCons x xs) := by
  cases word with
  | mk head tail =>
      exact monoidPowerDerivesNormalizeList
        index period indexPos periodPos head tail

/-- Generic completeness for a positive commutative power law. -/
theorem monoidPowerBasis_complete_of_separates
    {A : Type u} {G : Semigroup A} {index period : Nat}
    (indexPos : 0 < index) (periodPos : 0 < period)
    (models : Models G (monoidPowerBasis index period))
    (separates :
      ∀ identity : Identity Nat, identity.SatisfiedBy G →
        ∀ z,
          monoidPowerExponent index period
              (identity.lhs.toList.count z) =
            monoidPowerExponent index period
              (identity.rhs.toList.count z)) :
    BasisFor G (monoidPowerBasis index period) := by
  refine ⟨models, ?_⟩
  intro identity valid
  have reducedPermutation :
      (monoidPowerReduce index period identity.lhs.toList).Perm
        (monoidPowerReduce index period identity.rhs.toList) :=
    monoidPowerReduce_perm_of_exponent_eq
      index period indexPos periodPos (separates identity valid)
  have leftNormal :=
    monoidPowerDerivesNormal
      index period indexPos periodPos identity.lhs
  have rightNormal :=
    monoidPowerDerivesNormal
      index period indexPos periodPos identity.rhs
  cases leftShape : monoidPowerReduce index period identity.lhs.toList with
  | nil =>
      exact False.elim <|
        monoidPowerReduce_cons_ne_nil
          index period indexPos periodPos
          identity.lhs.head identity.lhs.tail <| by
            simpa [Word.toList] using leftShape
  | cons x xs =>
      cases rightShape :
          monoidPowerReduce index period identity.rhs.toList with
      | nil =>
          rw [leftShape, rightShape] at reducedPermutation
          exact False.elim (List.not_perm_cons_nil reducedPermutation)
      | cons y ys =>
          rw [leftShape] at leftNormal
          rw [rightShape] at rightNormal
          rw [leftShape, rightShape] at reducedPermutation
          exact Derives.trans leftNormal <|
            Derives.trans
              (monoidPowerDerivesPermutation index period
                (wordOfCons x xs) (wordOfCons y ys)
                reducedPermutation)
              (Derives.symm rightNormal)

/-! ## Finite monoid separation -/

def semigroupPower (G : Semigroup A) (one value : A) : Nat → A
  | 0 => one
  | n + 1 => G.mul (semigroupPower G one value n) value

def countValuation (one value : Fin 6) (selected : Nat) : Nat → Fin 6 :=
  fun letter => if letter = selected then value else one

def sixProfile (profile : Fin 6 → Fin 6) :
    Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6 :=
  (profile 0, profile 1, profile 2,
    profile 3, profile 4, profile 5)

structure FinSixPowerProfileWitness
    (G : Semigroup (Fin 6)) (index period : Nat)
    (indexPos : 0 < index) (periodPos : 0 < period) where
  one : Fin 6
  one_mul : ∀ value, G.mul one value = value
  mul_one : ∀ value, G.mul value one = value
  power_step :
    ∀ value (state : Fin (index + period)),
      G.mul (semigroupPower G one value state.val) value =
        semigroupPower G one value
          (monoidPowerAdvance index period state.val)
  profile_injective :
    Function.Injective
      (fun state : Fin (index + period) =>
        sixProfile
          (fun value => semigroupPower G one value state.val))

namespace FinSixPowerProfileWitness

private theorem fold_countValuation
    {G : Semigroup (Fin 6)} {index period : Nat}
    {indexPos : 0 < index} {periodPos : 0 < period}
    (witness :
      FinSixPowerProfileWitness G index period indexPos periodPos)
    (value : Fin 6) (selected : Nat) :
    ∀ (letters : List Nat) (n : Nat),
      letters.foldl
          (fun current letter =>
            G.mul current
              (countValuation witness.one value selected letter))
          (semigroupPower G witness.one value n) =
        semigroupPower G witness.one value
          (n + letters.count selected)
  | [], _ => by simp
  | letter :: letters, n => by
      simp only [List.foldl_cons]
      by_cases same : letter = selected
      · subst letter
        rw [show countValuation witness.one value selected selected = value by
          simp [countValuation]]
        rw [show
          G.mul (semigroupPower G witness.one value n) value =
              semigroupPower G witness.one value (n + 1) by rfl]
        rw [fold_countValuation, List.count_cons_self]
        congr 1
        omega
      · rw [show
          countValuation witness.one value selected letter = witness.one by
            simp [countValuation, same]]
        rw [witness.mul_one, fold_countValuation,
          List.count_cons_of_ne same]

theorem eval_countValuation
    {G : Semigroup (Fin 6)} {index period : Nat}
    {indexPos : 0 < index} {periodPos : 0 < period}
    (witness :
      FinSixPowerProfileWitness G index period indexPos periodPos)
    (value : Fin 6) (selected : Nat) (word : Word Nat) :
    G.eval (countValuation witness.one value selected) word =
      semigroupPower G witness.one value
        (word.toList.count selected) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              G.mul current
                (countValuation witness.one value selected letter))
            (countValuation witness.one value selected head) =
          semigroupPower G witness.one value
            ((head :: tail).count selected)
      by_cases same : head = selected
      · subst head
        rw [show
          countValuation witness.one value selected selected = value by
            simp [countValuation]]
        have folded :=
          fold_countValuation witness value selected tail 1
        have onePower :
            semigroupPower G witness.one value 1 = value := by
          simp [semigroupPower, witness.one_mul]
        rw [onePower] at folded
        simpa [Nat.add_comm] using folded
      · rw [show
          countValuation witness.one value selected head = witness.one by
            simp [countValuation, same]]
        have folded :=
          fold_countValuation witness value selected tail 0
        simpa [semigroupPower, List.count_cons_of_ne same] using folded

private theorem power_eq_normalExponent
    {G : Semigroup (Fin 6)} {index period : Nat}
    {indexPos : 0 < index} {periodPos : 0 < period}
    (witness :
      FinSixPowerProfileWitness G index period indexPos periodPos)
    (value : Fin 6) :
    ∀ n,
      semigroupPower G witness.one value n =
        semigroupPower G witness.one value
          (monoidPowerExponent index period n)
  | 0 => rfl
  | n + 1 => by
      calc
        semigroupPower G witness.one value (n + 1) =
            G.mul (semigroupPower G witness.one value n) value := rfl
        _ = G.mul
              (semigroupPower G witness.one value
                (monoidPowerExponent index period n)) value := by
              rw [power_eq_normalExponent witness value n]
        _ = semigroupPower G witness.one value
              (monoidPowerAdvance index period
                (monoidPowerExponent index period n)) :=
              witness.power_step value
                (monoidPowerExponentState
                  index period indexPos periodPos n)
        _ = semigroupPower G witness.one value
              (monoidPowerExponent index period (n + 1)) := rfl

theorem valid_exponentState_eq
    {G : Semigroup (Fin 6)} {index period : Nat}
    {indexPos : 0 < index} {periodPos : 0 < period}
    (witness :
      FinSixPowerProfileWitness G index period indexPos periodPos)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) (z : Nat) :
    monoidPowerExponentState index period indexPos periodPos
        (identity.lhs.toList.count z) =
      monoidPowerExponentState index period indexPos periodPos
        (identity.rhs.toList.count z) := by
  apply witness.profile_injective
  apply congrArg sixProfile
  funext value
  have evaluated := valid (countValuation witness.one value z)
  rw [witness.eval_countValuation, witness.eval_countValuation] at evaluated
  change
    semigroupPower G witness.one value
          (monoidPowerExponent index period
            (identity.lhs.toList.count z)) =
      semigroupPower G witness.one value
        (monoidPowerExponent index period
          (identity.rhs.toList.count z))
  calc
    _ = semigroupPower G witness.one value
          (identity.lhs.toList.count z) :=
      (power_eq_normalExponent witness value
        (identity.lhs.toList.count z)).symm
    _ = semigroupPower G witness.one value
          (identity.rhs.toList.count z) := evaluated
    _ = _ := power_eq_normalExponent witness value
      (identity.rhs.toList.count z)

theorem basisFor
    {G : Semigroup (Fin 6)} {index period : Nat}
    {indexPos : 0 < index} {periodPos : 0 < period}
    (witness :
      FinSixPowerProfileWitness G index period indexPos periodPos)
    (models : Models G (monoidPowerBasis index period)) :
    BasisFor G (monoidPowerBasis index period) := by
  apply monoidPowerBasis_complete_of_separates indexPos periodPos models
  intro identity valid z
  exact congrArg Fin.val <|
    witness.valid_exponentState_eq identity valid z

end FinSixPowerProfileWitness

/-! ## Exact generated roots -/

theorem S6_2863_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_2863.basis =
      monoidPowerBasis 4 2 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_2863_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_2863.oppositeTable.semigroup
      4 2 (by decide) (by decide) where
  one := 5
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_2863_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_2863.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_2863.basis := by
  rw [S6_2863_basis_eq_monoidPowerBasis]
  apply S6_2863_powerWitness.basisFor
  simpa only [S6_2863_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_2863.models

theorem S6_5326_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_5326.basis =
      monoidPowerBasis 2 4 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_5326_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup
      2 4 (by decide) (by decide) where
  one := 5
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_5326_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_5326.basis := by
  rw [S6_5326_basis_eq_monoidPowerBasis]
  apply S6_5326_powerWitness.basisFor
  simpa only [S6_5326_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_5326.models

theorem S6_5370_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_5370.basis =
      monoidPowerBasis 5 1 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_5370_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_5370.oppositeTable.semigroup
      5 1 (by decide) (by decide) where
  one := 5
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_5370_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_5370.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_5370.basis := by
  rw [S6_5370_basis_eq_monoidPowerBasis]
  apply S6_5370_powerWitness.basisFor
  simpa only [S6_5370_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_5370.models

theorem S6_9114_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_9114.basis =
      monoidPowerBasis 2 6 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_9114_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_9114.oppositeTable.semigroup
      2 6 (by decide) (by decide) where
  one := 3
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_9114_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_9114.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_9114.basis := by
  rw [S6_9114_basis_eq_monoidPowerBasis]
  apply S6_9114_powerWitness.basisFor
  simpa only [S6_9114_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_9114.models

theorem S6_9118_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_9118.basis =
      monoidPowerBasis 2 6 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_9118_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_9118.oppositeTable.semigroup
      2 6 (by decide) (by decide) where
  one := 3
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_9118_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_9118.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_9118.basis := by
  rw [S6_9118_basis_eq_monoidPowerBasis]
  apply S6_9118_powerWitness.basisFor
  simpa only [S6_9118_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_9118.models

theorem S6_9801_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_9801.basis =
      monoidPowerBasis 3 3 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_9801_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup
      3 3 (by decide) (by decide) where
  one := 3
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_9801_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_9801.basis := by
  rw [S6_9801_basis_eq_monoidPowerBasis]
  apply S6_9801_powerWitness.basisFor
  simpa only [S6_9801_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_9801.models

theorem S6_11935_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_11935.basis =
      monoidPowerBasis 2 6 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_11935_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_11935.oppositeTable.semigroup
      2 6 (by decide) (by decide) where
  one := 2
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_11935_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_11935.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_11935.basis := by
  rw [S6_11935_basis_eq_monoidPowerBasis]
  apply S6_11935_powerWitness.basisFor
  simpa only [S6_11935_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_11935.models

theorem S6_14989_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_14989.basis =
      monoidPowerBasis 2 6 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_14989_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_14989.oppositeTable.semigroup
      2 6 (by decide) (by decide) where
  one := 0
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_14989_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_14989.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_14989.basis := by
  rw [S6_14989_basis_eq_monoidPowerBasis]
  apply S6_14989_powerWitness.basisFor
  simpa only [S6_14989_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_14989.models

theorem S6_15960_basis_eq_monoidPowerBasis :
    Generated.Order6GenericCASRootData.S6_15960.basis =
      monoidPowerBasis 1 5 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private def S6_15960_powerWitness :
    FinSixPowerProfileWitness
      Generated.Order6GenericCASRootData.S6_15960.oppositeTable.semigroup
      1 5 (by decide) (by decide) where
  one := 1
  one_mul := by
    intro value
    apply Fin.ext
    revert value
    decide
  mul_one := by
    intro value
    apply Fin.ext
    revert value
    decide
  power_step := by
    intro value state
    apply Fin.ext
    revert value state
    decide
  profile_injective := by
    intro left right
    revert left right
    decide

theorem S6_15960_oppositeBasisFor :
    BasisFor
      Generated.Order6GenericCASRootData.S6_15960.oppositeTable.semigroup
      Generated.Order6GenericCASRootData.S6_15960.basis := by
  rw [S6_15960_basis_eq_monoidPowerBasis]
  apply S6_15960_powerWitness.basisFor
  simpa only [S6_15960_basis_eq_monoidPowerBasis] using
    Generated.Order6GenericCASRootData.S6_15960.models

end SemigroupBasis.CoRoots.Order6GenericCASMonoidPower

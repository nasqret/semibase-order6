import SemigroupBasis.Examples.EdmundsFiveTwoFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for Edmunds' `S(4,25)`, the catalogue
representative `S4_73` with table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,1,3,4]]`. -/
def edmundsFourSeventyThreeMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then 2 else
        if b = 0 then 0 else if b = 1 then 0 else
          if b = 2 then 2 else 3

/-- The exact four-element Smallsemi representative `S4_73`. -/
def edmundsFourSeventyThree : FiniteTable where
  order := 4
  mul := edmundsFourSeventyThreeMul
  assoc := by decide

def edmundsFourSeventyThreeXY : Word Nat := ⟨0, [1]⟩
def edmundsFourSeventyThreeXYY : Word Nat := ⟨0, [1, 1]⟩
def edmundsFourSeventyThreeXYX : Word Nat := ⟨0, [1, 0]⟩
def edmundsFourSeventyThreeXXY : Word Nat := ⟨0, [0, 1]⟩

def edmundsFourSeventyThreeRightDuplicationLaw : Identity Nat :=
  ⟨edmundsFourSeventyThreeXY, edmundsFourSeventyThreeXYY⟩

def edmundsFourSeventyThreeGatherLaw : Identity Nat :=
  ⟨edmundsFourSeventyThreeXYX, edmundsFourSeventyThreeXXY⟩

/-- Edmunds' basis for `S(4,25)`: `xy = xyy`, `xyx = xxy`. -/
def edmundsFourSeventyThreeBasis : List (Identity Nat) :=
  [edmundsFourSeventyThreeRightDuplicationLaw,
    edmundsFourSeventyThreeGatherLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Duplicate an arbitrary nonempty right block. -/
theorem edmundsFourSeventyThreeDerivesRightDuplication
    (u v : Word Nat) :
    Derives edmundsFourSeventyThreeBasis
      (u ++ v) ((u ++ v) ++ v) := by
  have hbase :
      Derives edmundsFourSeventyThreeBasis
        edmundsFourSeventyThreeXY edmundsFourSeventyThreeXYY :=
    Derives.fromBasis
      (e := edmundsFourSeventyThreeRightDuplicationLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [edmundsFourSeventyThreeBasis,
    edmundsFourSeventyThreeRightDuplicationLaw,
    edmundsFourSeventyThreeXY, edmundsFourSeventyThreeXYY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Gather a repeated left block across an intervening nonempty block. -/
theorem edmundsFourSeventyThreeDerivesGather (u v : Word Nat) :
    Derives edmundsFourSeventyThreeBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives edmundsFourSeventyThreeBasis
        edmundsFourSeventyThreeXYX edmundsFourSeventyThreeXXY :=
    Derives.fromBasis
      (e := edmundsFourSeventyThreeGatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [edmundsFourSeventyThreeBasis,
    edmundsFourSeventyThreeGatherLaw,
    edmundsFourSeventyThreeXYX, edmundsFourSeventyThreeXXY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem edmundsFiveTwoFourAxiomsDerive :
    ∀ e : Identity Nat, e ∈ edmundsFiveTwoFourBasis →
      Derives edmundsFourSeventyThreeBasis e.lhs e.rhs := by
  intro e he
  simp only [edmundsFiveTwoFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simpa [edmundsPowerLaw, edmundsXX, edmundsXXX,
      Word.append, Word.singleton] using
        edmundsFourSeventyThreeDerivesRightDuplication
          (Word.singleton 0) (Word.singleton 0)
  · simpa [edmundsGatherLaw, edmundsXYX, edmundsXXY] using
      edmundsFourSeventyThreeDerivesGather
        (Word.singleton 0) (Word.singleton 1)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- First reduce to the unrestricted Edmunds block normal form. If its tail
is nonempty, duplicate the entire tail. The duplicated tail is precisely the
extra normalization forced by `xy = xyy`. -/
def edmundsFourSeventyThreeNormal (w : Word Nat) : Word Nat :=
  match edmundsNormalList w.toList with
  | [] => w
  | [x] => Word.singleton x
  | x :: y :: ys =>
      let suffix := wordOfCons y ys
      (Word.singleton x ++ suffix) ++ suffix

theorem edmundsFourSeventyThreeDerivesNormal (w : Word Nat) :
    Derives edmundsFourSeventyThreeBasis w
      (edmundsFourSeventyThreeNormal w) := by
  have normalizes := edmundsDerivesNormal w
  cases hn : edmundsNormalList w.toList with
  | nil =>
      have headMem : w.head ∈ edmundsNormalList w.toList :=
        (edmundsNormalList_mem w.head w.toList).2 <| by
          simp [Word.toList]
      rw [hn] at headMem
      simp at headMem
  | cons x xs =>
      rw [hn] at normalizes
      have transported :=
        normalizes.transport edmundsFiveTwoFourAxiomsDerive
      cases xs with
      | nil =>
          simpa [edmundsFourSeventyThreeNormal, hn, wordOfCons] using
            transported
      | cons y ys =>
          let suffix := wordOfCons y ys
          have duplicated :=
            edmundsFourSeventyThreeDerivesRightDuplication
              (Word.singleton x) suffix
          exact Derives.trans
            (by
              simpa [wordOfCons, suffix, Word.append, Word.singleton] using
                transported)
            (by
              simpa [edmundsFourSeventyThreeNormal, hn, wordOfCons,
                suffix] using duplicated)

/-- During a common evaluation, the Edmunds `S4_75` value and the `S4_73`
value are either equal or are respectively `1` and `0`. -/
private def ValuesRelated (a b : Fin 4) : Prop :=
  a = b ∨ (a = 1 ∧ b = 0)

private theorem valuesRelated_step (a b c : Fin 4)
    (related : ValuesRelated a b) :
    ValuesRelated
      (edmundsFiveTwoFourMul a c)
      (edmundsFourSeventyThreeMul b c) := by
  rcases related with rfl | ⟨rfl, rfl⟩ <;>
    simp only [ValuesRelated] <;> decide +revert

private theorem fold_valuesRelated
    (valuation : Nat → Fin 4) :
    ∀ (xs : List Nat) (a b : Fin 4),
      ValuesRelated a b →
      ValuesRelated
        (xs.foldl
          (fun current x =>
            edmundsFiveTwoFourMul current (valuation x)) a)
        (xs.foldl
          (fun current x =>
            edmundsFourSeventyThreeMul current (valuation x)) b)
  | [], _, _, related => related
  | x :: xs, a, b, related => by
      simp only [List.foldl_cons]
      exact fold_valuesRelated valuation xs _ _
        (valuesRelated_step a b (valuation x) related)

private theorem eval_valuesRelated
    (valuation : Nat → Fin 4) (w : Word Nat) :
    ValuesRelated
      (edmundsFiveTwoFour.semigroup.eval valuation w)
      (edmundsFourSeventyThree.semigroup.eval valuation w) := by
  cases w with
  | mk head tail =>
      exact fold_valuesRelated valuation tail _ _ (Or.inl rfl)

private theorem doubledSuffix_values_equal
    (initial a b : Fin 4) (related : ValuesRelated a b) :
    edmundsFiveTwoFourMul
        (edmundsFiveTwoFourMul initial a) a =
      edmundsFourSeventyThreeMul
        (edmundsFourSeventyThreeMul initial b) b := by
  rcases related with rfl | ⟨rfl, rfl⟩ <;> decide +revert

/-- On a word consisting of one initial letter followed by a doubled nonempty
suffix, `S4_73` and `S4_75` have exactly the same value. -/
private theorem eval_doubledSuffix_eq
    (valuation : Nat → Fin 4) (x : Nat) (suffix : Word Nat) :
    edmundsFiveTwoFour.semigroup.eval valuation
        ((Word.singleton x ++ suffix) ++ suffix) =
      edmundsFourSeventyThree.semigroup.eval valuation
        ((Word.singleton x ++ suffix) ++ suffix) := by
  rw [Semigroup.eval_append, Semigroup.eval_append,
    Semigroup.eval_append, Semigroup.eval_append]
  exact doubledSuffix_values_equal
    (valuation x)
    (edmundsFiveTwoFour.semigroup.eval valuation suffix)
    (edmundsFourSeventyThree.semigroup.eval valuation suffix)
    (eval_valuesRelated valuation suffix)

/-- The `S4_73` normal forms are a common evaluation domain for `S4_73` and
the unrestricted Edmunds normal-form model `S4_75`. -/
private theorem normal_eval_eq
    (valuation : Nat → Fin 4) (w : Word Nat) :
    edmundsFiveTwoFour.semigroup.eval valuation
        (edmundsFourSeventyThreeNormal w) =
      edmundsFourSeventyThree.semigroup.eval valuation
        (edmundsFourSeventyThreeNormal w) := by
  cases hn : edmundsNormalList w.toList with
  | nil =>
      have headMem : w.head ∈ edmundsNormalList w.toList :=
        (edmundsNormalList_mem w.head w.toList).2 <| by
          simp [Word.toList]
      rw [hn] at headMem
      simp at headMem
  | cons x xs =>
      cases xs with
      | nil =>
          simp [edmundsFourSeventyThreeNormal, hn]
      | cons y ys =>
          simpa [edmundsFourSeventyThreeNormal, hn] using
            eval_doubledSuffix_eq valuation x (wordOfCons y ys)

private theorem edmundsFourSeventyThreeMul_rightDuplication
    (a b : Fin 4) :
    edmundsFourSeventyThreeMul a b =
      edmundsFourSeventyThreeMul
        (edmundsFourSeventyThreeMul a b) b := by
  decide +revert

private theorem edmundsFourSeventyThreeMul_gather
    (a b : Fin 4) :
    edmundsFourSeventyThreeMul
        (edmundsFourSeventyThreeMul a b) a =
      edmundsFourSeventyThreeMul
        (edmundsFourSeventyThreeMul a a) b := by
  decide +revert

theorem edmundsFourSeventyThreeBasis_models :
    Models edmundsFourSeventyThree.semigroup
      edmundsFourSeventyThreeBasis := by
  intro e he
  simp only [edmundsFourSeventyThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      edmundsFourSeventyThreeMul (valuation 0) (valuation 1) =
        edmundsFourSeventyThreeMul
          (edmundsFourSeventyThreeMul (valuation 0) (valuation 1))
          (valuation 1)
    exact edmundsFourSeventyThreeMul_rightDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    change
      edmundsFourSeventyThreeMul
          (edmundsFourSeventyThreeMul (valuation 0) (valuation 1))
          (valuation 0) =
        edmundsFourSeventyThreeMul
          (edmundsFourSeventyThreeMul (valuation 0) (valuation 0))
          (valuation 1)
    exact edmundsFourSeventyThreeMul_gather
      (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Words first enter the
Edmunds first-occurrence block normal form and then acquire a doubled tail.
Those forms evaluate identically in `S4_73` and `S4_75`, whose unrestricted
normal-form completeness supplies the middle derivation. -/
theorem edmundsFourSeventyThreeBasis_complete :
    BasisFor edmundsFourSeventyThree.semigroup
      edmundsFourSeventyThreeBasis := by
  refine ⟨edmundsFourSeventyThreeBasis_models, ?_⟩
  intro e valid
  have lhsNormal := edmundsFourSeventyThreeDerivesNormal e.lhs
  have rhsNormal := edmundsFourSeventyThreeDerivesNormal e.rhs
  let normalIdentity : Identity Nat :=
    ⟨edmundsFourSeventyThreeNormal e.lhs,
      edmundsFourSeventyThreeNormal e.rhs⟩
  have normalValid :
      normalIdentity.SatisfiedBy edmundsFiveTwoFour.semigroup := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound edmundsFourSeventyThreeBasis_models valuation
    have rhsSound :=
      rhsNormal.sound edmundsFourSeventyThreeBasis_models valuation
    change
      edmundsFiveTwoFour.semigroup.eval valuation
          (edmundsFourSeventyThreeNormal e.lhs) =
        edmundsFiveTwoFour.semigroup.eval valuation
          (edmundsFourSeventyThreeNormal e.rhs)
    rw [normal_eval_eq valuation e.lhs, normal_eval_eq valuation e.rhs]
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have middleEdmunds :=
    edmundsFiveTwoFourBasis_complete.2 normalIdentity normalValid
  have middle :=
    middleEdmunds.transport edmundsFiveTwoFourAxiomsDerive
  exact Derives.trans lhsNormal <|
    Derives.trans middle (Derives.symm rhsNormal)

def edmundsFourSeventyThreeOppositeBasis : List (Identity Nat) :=
  reversedBasis edmundsFourSeventyThreeBasis

theorem edmundsFourSeventyThreeOppositeBasis_complete :
    BasisFor edmundsFourSeventyThree.semigroup.opposite
      edmundsFourSeventyThreeOppositeBasis := by
  simpa [edmundsFourSeventyThreeOppositeBasis] using
    edmundsFourSeventyThreeBasis_complete.oppositeReversed

end SemigroupBasis.Examples
